// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Assembled application control plane.
//!
//! [`ApplicationService`] is the single place where the dynamic application
//! stack is wired together: one [`ApplicationManager`], one
//! [`ApplicationLoader`], one [`SystemDsoRegistry`], one
//! [`FlatImageMemory`] service and one [`ApplicationReaper`], over a fixed
//! system library catalog. Boot bootstrap and the
//! `ApplicationLaunch` syscall both reach it through the same singleton and
//! call [`ApplicationService::spawn`]; there is no boot fast path that calls
//! a loader directly.
//!
//! `spawn` uses the manager's `prepare` closure to open the
//! root, run the staged link, pin the start storage, install the product,
//! and start the main thread at the relocated entry after registering it with
//! the group. Every failure before the install drops the armed
//! link session and cancels the registry permits; a failure after the
//! install moves the group to draining with a skipped fini so the deferred
//! reaper releases the installed product.

use alloc::{boxed::Box, sync::Arc, vec::Vec};
use core::sync::atomic::{AtomicUsize, Ordering};
use spin::Once;

use blueos_header::application::BlueOsStringView;
use blueos_loader::ImageProtectionMemory;

use crate::{
    application::{
        adapters::{flat_memory::FlatImageMemory, system_paths::SystemLibraryPaths},
        group::ThreadGroup,
        loader::ApplicationLoader,
        manager::{
            ApplicationHandle, ApplicationLaunchError, ApplicationManager, OwnedLaunchRequest,
        },
        namespace::ApplicationNamespace,
        planner::NamespaceLoadPlanner,
        reaper::ApplicationReaper,
        registry::SystemDsoRegistry,
        start_storage::ApplicationStartStorage,
    },
    scheduler,
    sync::SpinLock,
    thread::{self, Builder, Entry, GlobalQueueVisitor},
    time::Tick,
};

/// Stack for the thread that performs one launch's link.
///
/// The staged link's depth follows the size of the dependency closure, so it
/// must not be inherited from whichever thread called `spawn` — at boot that is
/// the shell's main thread, and in the QEMU tests it is the test's main thread.
/// Owning the stack here turns "deep enough" into a decision that this constant
/// records, and keeps the application-facing thread stacks budgeted for
/// application work. Sized against the largest closure in the test corpus
/// (a root plus six private DSOs and one system DSO).
const LINK_STACK_SIZE: usize = 64 * 1024;

/// Completion hand-off between a launch caller and its link worker.
///
/// The worker stores its outcome and then bumps `epoch`; the caller parks on
/// `epoch` and reads the outcome once it moves. A `Semaphore` would be the
/// obvious primitive but it is `!Sync` (its counter is a `Cell`), and this
/// value has to cross the thread boundary.
struct LinkHandoff {
    /// Zero until the worker finishes, then one. Never reset.
    epoch: AtomicUsize,
    outcome: SpinLock<Option<Result<(), ApplicationLaunchError>>>,
}

impl LinkHandoff {
    fn new() -> Self {
        Self {
            epoch: AtomicUsize::new(0),
            outcome: SpinLock::new(None),
        }
    }
}

/// The assembled application control plane.
pub struct ApplicationService {
    manager: ApplicationManager,
    loader: ApplicationLoader,
    reaper: ApplicationReaper,
}

static APPLICATION_SERVICE: Once<ApplicationService> = Once::new();

impl ApplicationService {
    /// Assemble the process-wide service over a fixed system library catalog.
    /// Idempotent: later calls return the existing singleton.
    pub(crate) fn init(catalog: &'static SystemLibraryPaths) -> &'static ApplicationService {
        APPLICATION_SERVICE.call_once(|| {
            let memory = FlatImageMemory::new();
            let registry = SystemDsoRegistry::new();
            let loader = ApplicationLoader::new(catalog, registry.clone(), memory.clone());
            let reaper = ApplicationReaper::new(registry.clone(), memory);
            let manager = ApplicationManager::new(registry);
            // The deferred reaper thread owns clones of the reaper and the
            // manager and releases drained groups outside every manager lock
            reaper.spawn(manager.clone());
            Self {
                manager,
                loader,
                reaper,
            }
        })
    }

    /// The singleton, once initialized.
    pub fn get() -> Option<&'static ApplicationService> {
        APPLICATION_SERVICE.get()
    }

    /// The application manager.
    pub fn manager(&self) -> &ApplicationManager {
        &self.manager
    }

    /// Accept the application's init completion: first advance
    /// the pending system batch `Initializing → Ready` and mint the first
    /// group's leases, then move the manager's public state to `Running`.
    /// Only the validated `ApplicationInitComplete` syscall path calls this.
    pub fn complete_init(
        &self,
        group: &ThreadGroup,
        handle: ApplicationHandle,
    ) -> Result<(), ApplicationLaunchError> {
        if let Some(batch) = group.take_pending_system_batch() {
            let leases = self
                .loader
                .registry()
                .finish_initialization_batch(batch)
                .map_err(|_| ApplicationLaunchError::PrepareFailed)?;
            group
                .attach_system_leases(leases)
                .map_err(|_| ApplicationLaunchError::PrepareFailed)?;
        }
        self.manager.complete_init(handle)
    }

    /// Launch a dynamic application: link it against the system catalog,
    /// pin its start storage, install the product into a fresh thread group
    /// and start its main thread at the relocated entry.
    ///
    /// `argv`/`envp` are the owned, already-validated strings the launch
    /// syscall copied in; the returned handle stays `Loading` until the
    /// application reports `ApplicationInitComplete`.
    pub fn spawn(
        &self,
        path: &str,
        argv: Vec<Vec<u8>>,
        envp: Vec<Vec<u8>>,
    ) -> Result<ApplicationHandle, ApplicationLaunchError> {
        let launch_pwd = crate::vfs::get_working_dir().get_full_path();
        let namespace = ApplicationNamespace::from_launch_path(
            path,
            &launch_pwd,
            crate::application::board_dynamic_profile(),
        )
        .ok_or(ApplicationLaunchError::PrepareFailed)?;
        let identity = namespace.root_path().as_bytes().to_vec();
        // The namespace is moved into the link worker below; keep the path for
        // the launch record.
        let launch_path = alloc::string::String::from(namespace.root_path());
        // The link runs on a thread of its own, so the closure handed to the
        // manager has to own everything it captures. The service is a `Once`
        // singleton, so re-fetching it here yields the `'static` handle the
        // worker thread needs.
        let service = ApplicationService::get().ok_or(ApplicationLaunchError::PrepareFailed)?;
        let (result, group) = self
            .manager
            .launch_with_group(OwnedLaunchRequest::new(identity), move |group| {
                service.link_on_own_stack(group.clone(), namespace, argv, envp)
            });
        // Either way the group now belongs to the deferred reaper: a live
        // group is released after its members left and its fini resolved, a
        // failed launch's group (nothing installed, or installed-then-drained)
        // is recycled together with its `Failed` slot.
        self.reaper.register(&group);
        if let Ok(handle) = result {
            // Record the launch so the shell and QEMU checker can correlate
            // applications, DSO generations and reaps.
            log::info!(
                "APP_LAUNCHED handle={}:{} path={}",
                handle.slot,
                handle.generation,
                launch_path
            );
        }
        result
    }

    /// Run [`prepare`](Self::prepare) on a thread whose stack is sized for the
    /// link, and hand its result back to the caller.
    ///
    /// The caller blocks here, and holds no lock while it does: `launch` runs
    /// this closure outside the manager's table lock, so there is no cycle
    /// between the waiting caller and the worker.
    ///
    /// The worker is a plain kernel thread and is deliberately *not* added to
    /// the application's execution set: it is not an application member, and
    /// adding it would corrupt the exit coordinator's member count.
    fn link_on_own_stack(
        &'static self,
        group: ThreadGroup,
        namespace: ApplicationNamespace,
        argv: Vec<Vec<u8>>,
        envp: Vec<Vec<u8>>,
    ) -> Result<(), ApplicationLaunchError> {
        let handoff = Arc::new(LinkHandoff::new());
        let worker = handoff.clone();
        thread::spawn_with_stack(LINK_STACK_SIZE, move || {
            let result = self.prepare(&group, &namespace, &argv, &envp);
            *worker.outcome.irqsave_lock() = Some(result);
            // Publish the outcome before waking, so a caller that observes the
            // bump is guaranteed to observe the value.
            worker.epoch.fetch_add(1, Ordering::Release);
            let _ = crate::sync::atomic_wake(&worker.epoch, usize::MAX);
        })
        .ok_or(ApplicationLaunchError::PrepareFailed)?;

        while handoff.epoch.load(Ordering::Acquire) == 0 {
            // A spurious return only re-reads the epoch; the worker bumps it
            // exactly once and never resets it.
            let _ = crate::sync::atomic_wait(&handoff.epoch, 0, Tick::MAX);
        }
        handoff
            .outcome
            .irqsave_lock()
            .take()
            .expect("the worker stores its outcome before bumping the epoch")
    }

    /// The manager's slow prepare closure: VFS open, staged link, start
    /// storage and main-thread creation all run outside the manager's table
    /// lock.
    fn prepare(
        &self,
        group: &ThreadGroup,
        namespace: &ApplicationNamespace,
        argv: &[Vec<u8>],
        envp: &[Vec<u8>],
    ) -> Result<(), ApplicationLaunchError> {
        let argv_views: Vec<BlueOsStringView> = argv
            .iter()
            .map(|string| BlueOsStringView {
                data: string.as_ptr(),
                len: string.len(),
            })
            .collect();
        let envp_views: Vec<BlueOsStringView> = envp
            .iter()
            .map(|string| BlueOsStringView {
                data: string.as_ptr(),
                len: string.len(),
            })
            .collect();

        let root_path = namespace.root_path();
        let plan = NamespaceLoadPlanner::new(
            namespace,
            self.loader.catalog(),
            blueos_loader::SessionLimits::DEFAULT,
        )
        .plan()
        .map_err(|error| prepare_failed("plan namespace", &error))?;
        let product = self
            .loader
            .link(plan, namespace.profile(), group)
            .map_err(|error| prepare_failed("link application", &error))?;

        let granule = self.loader.memory().protection_capabilities().granule();
        let storage = ApplicationStartStorage::build(
            root_path.as_bytes(),
            &argv_views,
            &envp_views,
            &product,
            granule,
        )
        .map_err(|_| ApplicationLaunchError::PrepareFailed)?;

        // The storage heap allocations never move; the pointer stays valid
        // after the install moved the storage into the group.
        let start_info = storage.start_info_ptr();
        let entry = product.entry().get() as usize;
        let receipt = product.into_publication();
        group
            .install_resources(receipt, storage)
            .map_err(|_| ApplicationLaunchError::PrepareFailed)?;

        let stack =
            thread::Stack::from_size(blueos_kconfig::CONFIG_MAIN_THREAD_STACK_SIZE as usize)
                .ok_or(ApplicationLaunchError::PrepareFailed)?;
        let mut main = Builder::new(Entry::Raw(entry, start_info as *mut core::ffi::c_void))
            .set_stack(stack)
            .build();
        if group.add_member(main.clone()).is_err() {
            let _ = GlobalQueueVisitor::remove(&mut main);
            // The product is installed but the main thread could not join:
            // move the group to draining with a skipped fini so the deferred
            // reaper releases the installed resources (abnormal path).
            let _ = group.begin_exit();
            let _ = group.skip_fini();
            return Err(ApplicationLaunchError::PrepareFailed);
        }
        let main_id = thread::Thread::id(&main);
        let membership = group.membership();
        main.lock().set_cleanup(Entry::Closure(Box::new(move || {
            if let Some(group) = membership.upgrade() {
                let _ = group.remove_member(main_id);
            }
        })));
        let queued = scheduler::queue_ready_thread(thread::IDLE, main.clone());
        if queued.is_err() {
            let _ = group.remove_member(main_id);
            let _ = GlobalQueueVisitor::remove(&mut main);
            let _ = group.begin_exit();
            let _ = group.skip_fini();
            return Err(ApplicationLaunchError::PrepareFailed);
        }
        Ok(())
    }
}

fn prepare_failed(step: &str, error: &blueos_loader::LoadError) -> ApplicationLaunchError {
    log::error!("application prepare: {step} failed: {:?}", error);
    ApplicationLaunchError::PrepareFailed
}
