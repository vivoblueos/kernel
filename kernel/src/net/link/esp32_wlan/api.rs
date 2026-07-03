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

use crate::{
    boards::get_device, net::link::esp32_wlan::event::WifiEvent, sync::SpinLock, time, time::Tick,
};
use alloc::boxed::Box;
use blueos_driver::interrupt_controller::Interrupt;
use core::{
    ptr::NonNull,
    sync::atomic::{AtomicPtr, AtomicU32, Ordering},
};
use esp_radio_rtos_driver::{
    queue::{QueueHandle, QueuePtr},
    semaphore::{SemaphoreHandle, SemaphoreKind, SemaphorePtr},
    timer::{TimerHandle, TimerPtr},
};
use esp_wifi_sys_esp32c3::{
    c_types::{c_char, c_uint, c_void},
    include::{esp_event_base_t, ets_timer, timeval, OSI_FUNCS_TIME_BLOCKING},
};

// #define ESP_EVENT_DEFINE_BASE(id) esp_event_base_t id = #id
#[unsafe(no_mangle)]
static mut __ESP_RADIO_WIFI_EVENT: esp_event_base_t = c"WIFI_EVENT".as_ptr();

#[no_mangle]
pub(crate) unsafe extern "C" fn sleep(seconds: c_uint) -> c_uint {
    let target = Tick::after(Tick::from_millis(seconds as u64 * 1000));
    crate::scheduler::suspend_me_until::<()>(target, None);
    0
}

#[allow(unused)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn esp_event_post(
    event_base: *const c_char,
    event_id: i32,
    event_data: *mut c_void,
    event_data_size: usize,
    ticks_to_wait: u32,
) -> i32 {
    event_post(
        event_base,
        event_id,
        event_data,
        event_data_size,
        ticks_to_wait,
    )
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn gettimeofday(tv: *mut timeval, _tz: *mut ()) -> i32 {
    if !tv.is_null() {
        unsafe {
            let microseconds = Tick::now().as_micros();
            (*tv).tv_sec = (microseconds / 1_000_000) as u64;
            (*tv).tv_usec = (microseconds % 1_000_000) as u32;
        }
    }

    0
}

#[no_mangle]
pub unsafe extern "C" fn esp_fill_random(dst: *mut u8, len: u32) {
    unsafe {
        let dst = core::slice::from_raw_parts_mut(dst, len as usize);

        random_internal(dst);
    }
}

pub(super) fn random_u32() -> u32 {
    let mut data = [0u8; 4];
    random_internal(&mut data);
    u32::from_le_bytes(data)
}

pub(super) fn random_internal(data: &mut [u8]) {
    use blueos_driver::rng::esp32c3_rng::Esp32c3Rng;
    static RNG: SpinLock<Esp32c3Rng> = SpinLock::new(Esp32c3Rng::new());

    let wait_timer_cycles = 16_000_000 * 32 / 80_000_000;
    let until_tick = time::Tick::after(time::Tick(wait_timer_cycles));

    let mut remaining = data.len();
    let mut offset = 0;
    while remaining > 0 {
        loop {
            if until_tick.is_elapsed() {
                break;
            }
            core::hint::spin_loop();
        }
        let random_bytes = RNG.lock().read_one().to_le_bytes();
        let bytes_to_copy = random_bytes.len().min(remaining);
        data[offset..offset + bytes_to_copy].copy_from_slice(&random_bytes[..bytes_to_copy]);
        offset += bytes_to_copy;
        remaining -= bytes_to_copy;
    }
}

pub struct Handler {
    f: AtomicPtr<c_void>,
    arg: AtomicPtr<c_void>,
}

impl Handler {
    pub const fn new() -> Self {
        Self {
            f: AtomicPtr::new(core::ptr::null_mut()),
            arg: AtomicPtr::new(core::ptr::null_mut()),
        }
    }

    pub fn set(&self, f: *const c_void, arg: *const c_void) {
        self.arg.store(arg.cast_mut(), Ordering::Relaxed);
        self.f.store(f.cast_mut(), Ordering::Release);
    }

    pub fn dispatch(&self) {
        let f = self.f.load(Ordering::Acquire);
        if !f.is_null() {
            let func = unsafe {
                core::mem::transmute::<*const c_void, unsafe extern "C" fn(*mut c_void)>(f)
            };
            let arg = self.arg.load(Ordering::Relaxed);
            unsafe { func(arg) };
        }
    }
}

pub static ISR_INTERRUPT_1: Handler = Handler::new();

static WIFI_PWR_INTERRUPT: Interrupt = Interrupt::new(2, 1);
static WIFI_MAC_INTERRUPT: Interrupt = Interrupt::new(0, 1);

pub unsafe extern "C" fn env_is_chip() -> bool {
    true
}

pub unsafe extern "C" fn set_intr(cpu_no: i32, intr_source: u32, intr_num: u32, intr_prio: i32) {
    let intr = Interrupt::new(intr_source as _, intr_num as _);
    get_device!(intc).allocate_irq(intr);
    get_device!(intc).set_priority(intr, intr_prio as _);
}

/// Don't support
pub unsafe extern "C" fn clear_intr(intr_source: u32, intr_num: u32) {}

pub unsafe extern "C" fn set_isr(n: i32, f: *mut c_void, arg: *mut c_void) {
    match n {
        0 | 1 => ISR_INTERRUPT_1.set(f, arg),
        _ => panic!("set_isr - unsupported interrupt number {}", n),
    }

    get_device!(intc).enable_irq(WIFI_PWR_INTERRUPT);
    get_device!(intc).enable_irq(WIFI_MAC_INTERRUPT);
}

pub unsafe extern "C" fn ints_on(mask: u32) {
    let tmp = core::ptr::read_volatile(0x600C2104 as *const u32);
    core::ptr::write_volatile(0x600C2104 as *mut u32, tmp | mask);
}

pub unsafe extern "C" fn ints_off(mask: u32) {
    let tmp = core::ptr::read_volatile(0x600C2104 as *const u32);
    core::ptr::write_volatile(0x600C2104 as *mut u32, tmp & !mask);
}

pub unsafe extern "C" fn is_from_isr() -> bool {
    true
}

pub unsafe extern "C" fn spin_lock_create() -> *mut c_void {
    semphr_create(1, 1)
}

pub unsafe extern "C" fn wifi_int_disable(_wifi_int_mux: *mut c_void) -> u32 {
    crate::arch::disable_local_irq_save() as u32
}

pub unsafe extern "C" fn wifi_int_restore(_wifi_int_mux: *mut c_void, tmp: u32) {
    crate::arch::enable_local_irq_restore(tmp as usize);
}

pub unsafe extern "C" fn task_yield_from_isr() {
    crate::scheduler::yield_me_now_or_later();
}

pub unsafe extern "C" fn spin_lock_delete(lock: *mut c_void) {
    semphr_delete(lock);
}

pub unsafe extern "C" fn semphr_create(max: u32, init: u32) -> *mut c_void {
    let ptr = SemaphoreHandle::new(SemaphoreKind::Counting { max, initial: init })
        .leak()
        .as_ptr()
        .cast::<c_void>();
    ptr
}

pub unsafe extern "C" fn semphr_delete(semphr: *mut c_void) {
    if !semphr.is_null() {
        let ptr = SemaphorePtr::new(semphr.cast()).expect("invalid semaphore pointer");
        let handle = SemaphoreHandle::from_ptr(ptr);
        core::mem::drop(handle);
    }
}

pub unsafe extern "C" fn semphr_take(semphr: *mut c_void, block_time_tick: u32) -> i32 {
    if !semphr.is_null() {
        let ptr = SemaphorePtr::new(semphr.cast()).expect("invalid semaphore pointer");
        let handle = SemaphoreHandle::ref_from_ptr(&ptr);
        let timeout = if block_time_tick == OSI_FUNCS_TIME_BLOCKING {
            None
        } else {
            Some(block_time_tick)
        };

        handle.take(timeout) as i32
    } else {
        0
    }
}

pub unsafe extern "C" fn semphr_give(semphr: *mut c_void) -> i32 {
    if !semphr.is_null() {
        let ptr = SemaphorePtr::new(semphr.cast()).expect("invalid semaphore pointer");
        let handle = SemaphoreHandle::ref_from_ptr(&ptr);
        handle.give() as i32
    } else {
        0
    }
}

pub unsafe extern "C" fn wifi_thread_semphr_get() -> *mut c_void {
    esp_radio_rtos_driver::current_task_thread_semaphore()
        .as_ptr()
        .cast::<c_void>()
}

pub unsafe extern "C" fn mutex_create() -> *mut c_void {
    let ptr = SemaphoreHandle::new(SemaphoreKind::Mutex)
        .leak()
        .as_ptr()
        .cast();
    ptr
}

pub unsafe extern "C" fn recursive_mutex_create() -> *mut c_void {
    let ptr = SemaphoreHandle::new(SemaphoreKind::RecursiveMutex)
        .leak()
        .as_ptr()
        .cast();
    ptr
}

pub unsafe extern "C" fn mutex_delete(mutex: *mut c_void) {
    if !mutex.is_null() {
        let ptr = SemaphorePtr::new(mutex.cast()).expect("invalid mutex pointer");
        let handle = SemaphoreHandle::from_ptr(ptr);
        core::mem::drop(handle);
    }
}

pub unsafe extern "C" fn mutex_lock(mutex: *mut c_void) -> i32 {
    if !mutex.is_null() {
        let ptr = SemaphorePtr::new(mutex.cast()).expect("invalid mutex pointer");
        let handle = SemaphoreHandle::ref_from_ptr(&ptr);
        handle.take(None) as i32
    } else {
        0
    }
}

pub unsafe extern "C" fn mutex_unlock(mutex: *mut c_void) -> i32 {
    if !mutex.is_null() {
        let ptr = SemaphorePtr::new(mutex.cast()).expect("invalid mutex pointer");
        let handle = SemaphoreHandle::ref_from_ptr(&ptr);
        handle.give() as i32
    } else {
        0
    }
}

pub unsafe extern "C" fn queue_create(queue_len: u32, item_size: u32) -> *mut c_void {
    let queue = QueueHandle::new(queue_len as usize, item_size as usize)
        .leak()
        .as_ptr()
        .cast::<c_void>();
    queue
}

pub unsafe extern "C" fn queue_delete(queue: *mut c_void) {
    let ptr = QueuePtr::new(queue.cast()).expect("invalid queue pointer");

    let handle = unsafe { QueueHandle::from_ptr(ptr) };
    core::mem::drop(handle);
}

pub unsafe extern "C" fn queue_send(
    queue: *mut c_void,
    item: *mut c_void,
    block_time_tick: u32,
) -> i32 {
    queue_send_to_back(queue, item, block_time_tick)
}

pub unsafe extern "C" fn queue_send_from_isr(
    queue: *mut c_void,
    item: *mut c_void,
    hptw: *mut c_void,
) -> i32 {
    if !queue.is_null() {
        let ptr = QueuePtr::new(queue.cast()).expect("invalid queue pointer");
        let handle = unsafe { QueueHandle::ref_from_ptr(&ptr) };
        let ret =
            handle.try_send_to_back_from_isr(item.cast(), (hptw as *mut bool).as_mut()) as i32;
        ret
    } else {
        0
    }
}

pub unsafe extern "C" fn queue_send_to_back(
    queue: *mut c_void,
    item: *mut c_void,
    block_time_tick: u32,
) -> i32 {
    if !queue.is_null() {
        let ptr = QueuePtr::new(queue.cast()).expect("invalid queue pointer");
        let handle = unsafe { QueueHandle::ref_from_ptr(&ptr) };
        let timeout = if block_time_tick == OSI_FUNCS_TIME_BLOCKING {
            None
        } else {
            Some(block_time_tick)
        };

        let ret = handle.send_to_back(item.cast(), timeout) as i32;
        ret
    } else {
        0
    }
}

pub unsafe extern "C" fn queue_send_to_front(
    queue: *mut c_void,
    item: *mut c_void,
    block_time_tick: u32,
) -> i32 {
    if !queue.is_null() {
        let ptr = QueuePtr::new(queue.cast()).expect("invalid queue pointer");
        let handle = unsafe { QueueHandle::ref_from_ptr(&ptr) };
        let timeout = if block_time_tick == OSI_FUNCS_TIME_BLOCKING {
            None
        } else {
            Some(block_time_tick)
        };

        handle.send_to_front(item.cast(), timeout) as i32
    } else {
        0
    }
}

pub unsafe extern "C" fn queue_recv(
    queue: *mut c_void,
    item: *mut c_void,
    block_time_tick: u32,
) -> i32 {
    if !queue.is_null() {
        let ptr = QueuePtr::new(queue.cast()).expect("invalid queue pointer");
        let handle = unsafe { QueueHandle::ref_from_ptr(&ptr) };
        let timeout = if block_time_tick == OSI_FUNCS_TIME_BLOCKING {
            None
        } else {
            Some(block_time_tick)
        };

        let ret = handle.receive(item.cast(), timeout) as i32;
        ret
    } else {
        0
    }
}

pub unsafe extern "C" fn queue_msg_waiting(queue: *mut c_void) -> u32 {
    if !queue.is_null() {
        let ptr = QueuePtr::new(queue.cast()).expect("invalid queue pointer");
        let handle = unsafe { QueueHandle::ref_from_ptr(&ptr) };
        handle.messages_waiting() as u32
    } else {
        0
    }
}

pub unsafe extern "C" fn event_group_create() -> *mut c_void {
    log::error!("wifi_os_event_group_create called");
    todo!("event_group_create")
}

pub unsafe extern "C" fn event_group_delete(event: *mut c_void) {
    log::error!("wifi_os_event_group_delete called: event={:p}", event);
    todo!("event_group_delete")
}

pub unsafe extern "C" fn event_group_set_bits(event: *mut c_void, bits: u32) -> u32 {
    log::error!(
        "wifi_os_event_group_set_bits called: event={:p} bits=0x{:08x}",
        event,
        bits,
    );
    todo!("event_group_set_bits")
}

pub unsafe extern "C" fn event_group_clear_bits(event: *mut c_void, bits: u32) -> u32 {
    log::error!(
        "wifi_os_event_group_clear_bits called: event={:p} bits=0x{:08x}",
        event,
        bits,
    );
    todo!("event_group_clear_bits")
}

pub unsafe extern "C" fn event_group_wait_bits(
    event: *mut c_void,
    bits_to_wait_for: u32,
    clear_on_exit: i32,
    wait_for_all_bits: i32,
    block_time_tick: u32,
) -> u32 {
    log::error!(
        "wifi_os_event_group_wait_bits called: event={:p} bits=0x{:08x} clear={} all={} ticks={}",
        event,
        bits_to_wait_for,
        clear_on_exit,
        wait_for_all_bits,
        block_time_tick,
    );
    todo!("event_group_wait_bits")
}

pub unsafe extern "C" fn task_create_pinned_to_core(
    task_func: *mut c_void,
    _task_name: *const core::ffi::c_char,
    stack_depth: u32,
    param: *mut c_void,
    prio: u32,
    task_handle: *mut c_void,
    core_id: u32,
) -> i32 {
    let task_name = "unused";

    let task_func = core::mem::transmute::<*mut c_void, extern "C" fn(*mut c_void)>(task_func);

    let task = esp_radio_rtos_driver::task_create(
        task_name,
        task_func,
        param,
        prio,
        if core_id < 2 { Some(core_id) } else { None },
        stack_depth as usize,
    );
    *(task_handle as *mut usize) = task.as_ptr() as usize;

    1
}

pub unsafe extern "C" fn task_create(
    task_func: *mut c_void,
    _task_name: *const core::ffi::c_char,
    stack_depth: u32,
    param: *mut c_void,
    prio: u32,
    task_handle: *mut c_void,
) -> i32 {
    let task_name = "unused";

    let task_func = core::mem::transmute::<*mut c_void, extern "C" fn(*mut c_void)>(task_func);

    let task = esp_radio_rtos_driver::task_create(
        task_name,
        task_func,
        param,
        prio,
        None,
        stack_depth as usize,
    );
    *(task_handle as *mut usize) = task.as_ptr() as usize;

    1
}

pub unsafe extern "C" fn task_delete(task_handle: *mut c_void) {
    esp_radio_rtos_driver::schedule_task_deletion(NonNull::new(task_handle.cast::<()>()));
}

pub unsafe extern "C" fn task_delay(tick: u32) {
    crate::scheduler::suspend_me_for::<()>(Tick(tick as usize), None);
}

pub unsafe extern "C" fn task_ms_to_tick(ms: u32) -> i32 {
    Tick::from_millis(ms as u64).0 as i32
}

pub unsafe extern "C" fn task_get_current_task() -> *mut c_void {
    esp_radio_rtos_driver::current_task()
        .cast::<c_void>()
        .as_ptr()
}

pub unsafe extern "C" fn task_get_max_priority() -> i32 {
    esp_radio_rtos_driver::max_task_priority() as i32
}

/// Rust-side log output function called from C bridge (log_bridge.c).
/// Receives the fully formatted message string and prints via kernel log.
#[no_mangle]
pub unsafe extern "C" fn blueos_wifi_log_output(
    level: c_uint,
    tag: *const c_char,
    msg: *const c_char,
) {
    let tag_str = if tag.is_null() {
        "<null>"
    } else {
        // Safety: tag is a C string from the ESP driver, guaranteed non-null here
        unsafe {
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(tag as *const u8, unsafe {
                libc::strlen(tag)
            }
                as usize))
        }
    };
    let msg_str = if msg.is_null() {
        "<null>"
    } else {
        // Safety: msg is a C string produced by vsnprintf in log_bridge.c
        unsafe {
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(msg as *const u8, unsafe {
                libc::strlen(msg)
            }
                as usize))
        }
    };
    match level {
        1 => log::error!("[ESP_WIFI][{}] {}", tag_str, msg_str),
        2 => log::warn!("[ESP_WIFI][{}] {}", tag_str, msg_str),
        _ => {}
    }
}

extern "C" {
    /// C bridge for _log_writev — formats va_list via vsnprintf and calls
    /// blueos_wifi_log_output. Defined in log_bridge.c.
    fn wifi_log_writev_bridge(
        level: c_uint,
        tag: *const c_char,
        format: *const c_char,
        args: *mut c_void,
    );
    /// C bridge for _log_write — formats varargs and calls wifi_log_writev_bridge.
    /// Defined in log_bridge.c.
    fn wifi_log_write_bridge(level: c_uint, tag: *const c_char, format: *const c_char, ...);
}

pub unsafe extern "C" fn log_writev(
    level: c_uint,
    tag: *const c_char,
    format: *const c_char,
    args: *mut c_void,
) {
    wifi_log_writev_bridge(level, tag, format, args)
}

pub unsafe extern "C" fn log_write(level: c_uint, tag: *const c_char, format: *const c_char, ...) {
    // We can't forward Rust ... to C ... directly.
    // Instead, just call the C bridge which handles varargs natively.
    // Note: wifi_log in libnet80211.a always calls _log_writev first,
    // then _log_write with the same arguments. Since _log_writev already
    // printed the message, we make _log_write a no-op to avoid duplicate output.
    // The C bridge function exists for completeness but we skip duplicate printing.
}

pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
    crate::allocator::malloc(size) as *mut c_void
}

pub unsafe extern "C" fn free(p: *mut c_void) {
    crate::allocator::free(p as *mut u8);
}

pub unsafe extern "C" fn event_post(
    _event_base: *const core::ffi::c_char,
    event_id: i32,
    event_data: *mut c_void,
    _event_data_size: usize,
    _ticks_to_wait: u32,
) -> i32 {
    use num_traits::FromPrimitive;

    let Some(event) = WifiEvent::from_i32(event_id) else {
        log::warn!("Unknown event id: {}", event_id);
        return 0;
    };

    let Some(payload) = super::event::EventInfo::from_wifi_event_raw(event, event_data) else {
        return 0;
    };

    // Forward to async handler only; payload processing stays in async context.
    if let Err(e) = unsafe { super::EVENT_SENDER.assume_init_mut() }
        .0
        .try_send(payload)
    {
        log::warn!("Event channel full, dropping event: {:?}", e.0);
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn get_free_internal_heap_size() -> usize {
    let memory_info = crate::allocator::memory_info();
    (memory_info.total - memory_info.used) as usize
}

pub unsafe extern "C" fn get_free_heap_size() -> u32 {
    let memory_info = crate::allocator::memory_info();
    (memory_info.total - memory_info.used) as u32
}

pub unsafe extern "C" fn rand() -> u32 {
    random_u32()
}

pub unsafe extern "C" fn dport_access_stall_other_cpu_start_wrap() {}

pub unsafe extern "C" fn dport_access_stall_other_cpu_end_wrap() {}

/// no-op
pub unsafe extern "C" fn wifi_apb80m_request() {}

/// no-op
pub unsafe extern "C" fn wifi_apb80m_release() {}

const SYSTEM_WIFI_CLK_WIFI_BT_COMMON_M: u32 = 0x78078F;
static PHY_CLK_REF: AtomicU32 = AtomicU32::new(0);
static PHY_CLK_LOCK: SpinLock<()> = SpinLock::new(());
const WIFI_CLK_EN_REG_ADDRESS: usize = 0x60026014;

pub unsafe extern "C" fn phy_disable() {
    esp_phy::disable_phy();
}

pub unsafe extern "C" fn phy_enable() {
    core::mem::forget(esp_phy::enable_phy());
}

// no-support
pub unsafe extern "C" fn phy_update_country_info(_country: *const core::ffi::c_char) -> i32 {
    -1
}

pub unsafe extern "C" fn read_mac(mac_out: *mut u8, type_: u32) -> i32 {
    let mac = blueos_driver::hwinfo::esp32c3::mac();
    match type_ {
        0 => {
            // Station
            let mac_bytes = mac;
            unsafe {
                core::ptr::copy_nonoverlapping(mac_bytes.as_ptr(), mac_out, 6);
            }
            0
        }
        1 => {
            // Access Point
            let mac_bytes = {
                let bytes = mac;
                let mut local_mac = bytes;
                let base = bytes[0];

                for i in 0..64 {
                    let derived = (base | 0x02) ^ (i << 2);
                    if derived != base {
                        local_mac[0] = derived;
                        break;
                    }
                }
                local_mac
            };
            unsafe {
                core::ptr::copy_nonoverlapping(mac_bytes.as_ptr(), mac_out, 6);
            }
            0
        }
        _ => -1,
    }
}

pub unsafe extern "C" fn ets_timer_arm(timer: *mut c_void, tmout: u32, repeat: bool) {
    ets_timer_arm_us(timer, tmout.saturating_mul(1000), repeat);
}

pub unsafe extern "C" fn ets_timer_disarm(timer: *mut c_void) {
    let ets_timer = timer as *mut ets_timer;
    let ets_timer = ets_timer.as_mut().expect("ets_timer is null");

    if let Some(timer) = TimerPtr::new(ets_timer.priv_.cast()) {
        let timer = unsafe { TimerHandle::ref_from_ptr(&timer) };

        timer.disarm();
    }
}

pub unsafe extern "C" fn ets_timer_done(ptimer: *mut c_void) {
    let ets_timer = ptimer as *mut ets_timer;
    let ets_timer = ets_timer.as_mut().expect("ets_timer is null");

    if let Some(timer) = TimerPtr::new(ets_timer.priv_.cast()) {
        let timer = unsafe { TimerHandle::from_ptr(timer) };

        core::mem::drop(timer);
        ets_timer.priv_ = core::ptr::null_mut();
    }
}

pub unsafe extern "C" fn ets_timer_setfn(
    ptimer: *mut c_void,
    pfunction: *mut c_void,
    parg: *mut c_void,
) {
    // This function is expected to create timers. For the simplicity of the preempt API, we
    // will not update existing timers, but create new ones.
    ets_timer_done(ptimer);

    let ets_timer = ptimer as *mut ets_timer;
    let ets_timer = ets_timer.as_mut().expect("ets_timer is null");
    let timer = unsafe {
        TimerHandle::new(
            core::mem::transmute::<*mut c_void, unsafe extern "C" fn(*mut c_void)>(pfunction),
            parg,
        )
    }
    .leak()
    .cast()
    .as_ptr();

    ets_timer.next = core::ptr::null_mut();
    ets_timer.period = 0;
    ets_timer.func = None;
    ets_timer.priv_ = timer;
}

pub unsafe extern "C" fn ets_timer_arm_us(ptimer: *mut c_void, us: u32, repeat: bool) {
    let ets_timer = ptimer as *mut ets_timer;
    let ets_timer = ets_timer.as_mut().expect("ets_timer is null");

    let timer = TimerPtr::new(ets_timer.priv_.cast()).expect("timer is null");
    let timer = TimerHandle::ref_from_ptr(&timer);

    timer.arm(us as u64, repeat);
}

pub unsafe extern "C" fn wifi_reset_mac() {
    const APB_CTRL_BASE: usize = 0x6002_6000;
    const WIFI_RST_EN: *mut u32 = (APB_CTRL_BASE + 0x18) as *mut u32;
    const MAC_RST: u32 = 1 << 2;

    // set_bit()
    let value = core::ptr::read_volatile(WIFI_RST_EN);
    core::ptr::write_volatile(WIFI_RST_EN, value | MAC_RST);

    // clear_bit()
    let value = core::ptr::read_volatile(WIFI_RST_EN);
    core::ptr::write_volatile(WIFI_RST_EN, value & !MAC_RST);
}

/// no-op
pub unsafe extern "C" fn wifi_clock_enable() {}

/// no-op
pub unsafe extern "C" fn wifi_clock_disable() {}

pub unsafe extern "C" fn wifi_rtc_enable_iso() {
    todo!("wifi_rtc_enable_iso")
}

pub unsafe extern "C" fn wifi_rtc_disable_iso() {
    todo!("wifi_rtc_disable_iso")
}

pub unsafe extern "C" fn __esp_radio_esp_timer_get_time() -> i64 {
    Tick::now().as_micros() as i64
}

pub unsafe extern "C" fn nvs_set_i8(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _value: i8,
) -> i32 {
    0
}

pub unsafe extern "C" fn nvs_get_i8(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _out_value: *mut i8,
) -> i32 {
    todo!("nvs_get_i8")
}

pub unsafe extern "C" fn nvs_set_u8(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _value: u8,
) -> i32 {
    todo!("nvs_set_u8")
}

pub unsafe extern "C" fn nvs_get_u8(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _out_value: *mut u8,
) -> i32 {
    todo!("nvs_get_u8")
}

pub unsafe extern "C" fn nvs_set_u16(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _value: u16,
) -> i32 {
    todo!("nvs_set_u16")
}

pub unsafe extern "C" fn nvs_get_u16(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _out_value: *mut u16,
) -> i32 {
    todo!("nvs_get_u16")
}

pub unsafe extern "C" fn nvs_open(
    _name: *const core::ffi::c_char,
    _open_mode: u32,
    _out_handle: *mut u32,
) -> i32 {
    todo!("nvs_open")
}

pub unsafe extern "C" fn nvs_close(_handle: u32) {
    todo!("nvs_close")
}

pub unsafe extern "C" fn nvs_commit(_handle: u32) -> i32 {
    todo!("nvs_commit")
}

pub unsafe extern "C" fn nvs_set_blob(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _value: *const c_void,
    _length: usize,
) -> i32 {
    todo!("nvs_set_blob")
}

pub unsafe extern "C" fn nvs_get_blob(
    _handle: u32,
    _key: *const core::ffi::c_char,
    _out_value: *mut c_void,
    _length: *mut usize,
) -> i32 {
    todo!("nvs_get_blob")
}

pub unsafe extern "C" fn nvs_erase_key(_handle: u32, _key: *const core::ffi::c_char) -> i32 {
    todo!("nvs_erase_key")
}

pub unsafe extern "C" fn get_random(buf: *mut u8, len: usize) -> i32 {
    let slice = core::slice::from_raw_parts_mut(buf, len);
    random_internal(slice);
    0
}

pub unsafe extern "C" fn get_time(_t: *mut c_void) -> i32 {
    todo!("get_time")
}

pub unsafe extern "C" fn random() -> u32 {
    random_u32()
}

pub unsafe extern "C" fn slowclk_cal_get() -> u32 {
    28639
}

pub unsafe extern "C" fn log_timestamp() -> u32 {
    crate::time::Tick::now().as_millis() as u32
}

#[no_mangle]
pub unsafe extern "C" fn malloc_internal(size: usize) -> *mut c_void {
    crate::allocator::malloc(size) as *mut c_void
}

#[no_mangle]
pub unsafe extern "C" fn free_internal(ptr: *mut c_void) {
    crate::allocator::free(ptr as *mut u8);
}

#[no_mangle]
pub unsafe extern "C" fn realloc_internal(ptr: *mut c_void, size: usize) -> *mut c_void {
    crate::allocator::realloc(ptr as *mut u8, size) as *mut c_void
}

#[no_mangle]
pub unsafe extern "C" fn calloc_internal(n: usize, size: usize) -> *mut c_void {
    crate::allocator::calloc(n, size) as *mut c_void
}

pub unsafe extern "C" fn zalloc_internal(size: usize) -> *mut c_void {
    calloc_internal(size, 1)
}

pub unsafe extern "C" fn wifi_malloc(size: usize) -> *mut c_void {
    malloc_internal(size)
}

pub unsafe extern "C" fn wifi_realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
    realloc_internal(ptr, size)
}

pub unsafe extern "C" fn wifi_calloc(n: usize, size: usize) -> *mut c_void {
    calloc_internal(n, size)
}

pub unsafe extern "C" fn wifi_zalloc(size: usize) -> *mut c_void {
    wifi_calloc(size, 1)
}

pub unsafe extern "C" fn wifi_create_queue(queue_len: i32, item_size: i32) -> *mut c_void {
    let queue = queue_create(queue_len as u32, item_size as u32);

    let queue_ptr: *mut *mut c_void = Box::leak(Box::new(queue));

    queue_ptr.cast()
}

pub unsafe extern "C" fn wifi_delete_queue(queue: *mut c_void) {
    let queue_ptr: *mut *mut c_void = queue.cast();

    let boxed = unsafe { Box::from_raw(queue_ptr) };

    queue_delete(*boxed)
}

pub unsafe extern "C" fn coex_init() -> i32 {
    0
}

pub unsafe extern "C" fn coex_deinit() {}

pub unsafe extern "C" fn coex_enable() -> i32 {
    0
}

pub unsafe extern "C" fn coex_disable() {}

pub unsafe extern "C" fn coex_status_get() -> u32 {
    0
}

pub unsafe extern "C" fn coex_wifi_request(_event: u32, _latency: u32, _duration: u32) -> i32 {
    0
}

pub unsafe extern "C" fn coex_wifi_release(_event: u32) -> i32 {
    0
}

pub unsafe extern "C" fn coex_wifi_channel_set(_primary: u8, _secondary: u8) -> i32 {
    0
}

pub unsafe extern "C" fn coex_event_duration_get(_event: u32, _duration: *mut u32) -> i32 {
    0
}

pub unsafe extern "C" fn coex_pti_get(_event: u32, _pti: *mut u8) -> i32 {
    0
}

pub unsafe extern "C" fn coex_schm_status_bit_clear(_type_: u32, _status: u32) {}

pub unsafe extern "C" fn coex_schm_status_bit_set(_type_: u32, _status: u32) {}

pub unsafe extern "C" fn coex_schm_interval_set(_interval: u32) -> i32 {
    0
}

pub unsafe extern "C" fn coex_schm_interval_get() -> u32 {
    0
}

pub unsafe extern "C" fn coex_schm_curr_period_get() -> u8 {
    0
}

pub unsafe extern "C" fn coex_schm_curr_phase_get() -> *mut c_void {
    core::ptr::null_mut()
}

pub unsafe extern "C" fn coex_schm_process_restart() -> i32 {
    0
}

pub unsafe extern "C" fn coex_schm_register_cb(
    _arg1: i32,
    _cb: Option<unsafe extern "C" fn(_arg1: i32) -> i32>,
) -> i32 {
    0
}

pub unsafe extern "C" fn coex_register_start_cb(_cb: Option<unsafe extern "C" fn() -> i32>) -> i32 {
    0
}

pub unsafe extern "C" fn coex_schm_flexible_period_set(_arg1: u8) -> i32 {
    0
}

pub unsafe extern "C" fn coex_schm_flexible_period_get() -> u8 {
    0
}

pub unsafe extern "C" fn coex_schm_get_phase_by_idx(_arg1: i32) -> *mut c_void {
    core::ptr::null_mut()
}

pub unsafe extern "C" fn calloc_internal_wrapper(n: usize, size: usize) -> *mut c_void {
    calloc_internal(n, size)
}

pub unsafe extern "C" fn coex_schm_register_cb_wrapper(
    arg1: i32,
    cb: Option<unsafe extern "C" fn(arg1: i32) -> i32>,
) -> i32 {
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn phy_printf(_format: *const c_char, mut __valist: ...) -> core::ffi::c_int {
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn pp_printf(_format: *const c_char, mut __valist: ...) -> core::ffi::c_int {
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn net80211_printf(
    _format: *const c_char,
    mut __valist: ...
) -> core::ffi::c_int {
    0
}
