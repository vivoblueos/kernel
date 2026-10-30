//! Support for native Rust functions.

use crate::{for_all_tuples, value::LoadStore, TypeSet, TypedValue};

/// An error that occurs when calling a function.
pub enum FunctionCallError {
    /// The function was not found in the context.
    FunctionNotFound,

    /// The number of arguments passed to the function does not match the expected count.
    IncorrectArgumentCount {
        /// The expected number of arguments.
        expected: usize,
    },

    /// The type of an argument does not match the expected type.
    IncorrectArgumentType {
        /// The 0-based index of the argument that has the incorrect type.
        idx: usize,
        /// The expected type of the argument.
        expected: &'static str,
    },

    /// An error occurred while calling the function.
    Other(Box<str>),
}

/// Functions and closures that implement this trait can be registered as functions to be called by expressions.
pub trait DynFunction<A, T>
where
    T: TypeSet,
{
    /// Call the function with the specified arguments.
    ///
    /// # Errors
    ///
    /// This functions returns an error if:
    /// - The number of arguments is incorrect
    /// - The types of arguments are incorrect
    fn call(&self, ctx: &mut T, args: &[TypedValue<T>])
        -> Result<TypedValue<T>, FunctionCallError>;
}

macro_rules! substitute {
    ($arg:tt, $replacement:tt) => {
        $replacement
    };
}

for_all_tuples! {
    ($($arg:ident),*) => {
        impl<$($arg,)* R, F, T> DynFunction<($($arg,)*), T> for F
        where
            $($arg: LoadStore<T>,)*
            // This double bound on F ensures that we can work with reference types (&str), too:
            // The first one ensures type-inference matches the Load implementation we want
            // The second one ensures we don't run into "... is not generic enough" errors.
            F: Fn($($arg,)*) -> R,
            F: for<'t> Fn($($arg::Output<'t>,)*) -> R,
            R: LoadStore<T>,
            T: TypeSet,
        {

            #[allow(non_snake_case, unused)]
            fn call(&self, ctx: &mut T, args: &[TypedValue<T>]) -> Result<TypedValue<T>, FunctionCallError> {
                const ARG_COUNT: usize = 0 $( + substitute!($arg, 1) )* ;

                if args.len() != ARG_COUNT {
                    return Err(FunctionCallError::IncorrectArgumentCount { expected: ARG_COUNT });
                }

                let idx = 0;
                $(
                    let Some($arg) = <$arg>::load(ctx, &args[idx]) else {
                        return Err(FunctionCallError::IncorrectArgumentType { idx, expected: std::any::type_name::<$arg>() });
                    };
                    let idx = idx + 1;
                )*


                Ok(self($($arg),*).store(ctx))
            }
        }
    };
}

pub(crate) struct ExprFn<'ctx, T: TypeSet> {
    #[allow(clippy::type_complexity)]
    func: Box<dyn Fn(&mut T, &[TypedValue<T>]) -> Result<TypedValue<T>, FunctionCallError> + 'ctx>,
}

impl<'ctx, T: TypeSet> ExprFn<'ctx, T> {
    pub fn new<A, F>(func: F) -> Self
    where
        F: DynFunction<A, T> + 'ctx,
    {
        Self {
            func: Box::new(move |ctx, args| func.call(ctx, args)),
        }
    }

    pub fn call(
        &self,
        ctx: &mut T,
        args: &[TypedValue<T>],
    ) -> Result<TypedValue<T>, FunctionCallError> {
        (self.func)(ctx, args)
    }
}
