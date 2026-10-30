use atomic_polyfill::{AtomicBool, Ordering};

pub trait SplitState: Clone {
    fn same(&self, other: &Self) -> bool;
    fn is_open(&self) -> bool;
    fn set_open(&self, open: bool);
}

pub trait SplitStateContainer {
    type State: SplitState;

    fn state(self) -> Self::State;
}

pub struct SplitConnectionState {
    is_open: AtomicBool,
}

impl Default for SplitConnectionState {
    #[inline]
    fn default() -> Self {
        Self {
            is_open: AtomicBool::new(true),
        }
    }
}

impl<'a> SplitStateContainer for &'a mut SplitConnectionState {
    type State = &'a SplitConnectionState;

    fn state(self) -> Self::State {
        &*self
    }
}

impl SplitState for &SplitConnectionState {
    fn is_open(&self) -> bool {
        self.is_open.load(Ordering::Acquire)
    }

    fn set_open(&self, open: bool) {
        self.is_open.store(open, Ordering::Release);
    }

    fn same(&self, other: &Self) -> bool {
        core::ptr::eq(*self, *other)
    }
}

#[cfg(feature = "std")]
pub use stdlib::ManagedSplitState;

#[cfg(feature = "std")]
mod stdlib {
    use super::*;
    use std::sync::Arc;

    #[derive(Clone)]
    pub struct ManagedSplitState(Arc<SplitConnectionState>);
    impl ManagedSplitState {
        pub(crate) fn new() -> Self {
            Self(Arc::new(SplitConnectionState::default()))
        }
    }

    impl SplitStateContainer for ManagedSplitState {
        type State = ManagedSplitState;

        fn state(self) -> Self::State {
            self
        }
    }

    impl SplitState for ManagedSplitState {
        fn is_open(&self) -> bool {
            self.0.as_ref().is_open()
        }

        fn set_open(&self, open: bool) {
            self.0.as_ref().set_open(open)
        }

        fn same(&self, other: &Self) -> bool {
            Arc::ptr_eq(&self.0, &other.0)
        }
    }
}
