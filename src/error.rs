use crate::chain::Chain;
use crate::EyreHandler;
use crate::{Report, StdError};
use core::fmt::{self, Debug, Display};
use core::any::TypeId;

use core::ops::{Deref, DerefMut};

use narrow_box::NarrowBox;

impl Report {
    /// Create a new error object from any error type.
    ///
    /// The error type must be threadsafe and `'static`, so that the `Report`
    /// will be as well.
    ///
    /// If the error type does not provide a backtrace, a backtrace will be
    /// created here to ensure that a backtrace exists.
    #[cfg_attr(track_caller, track_caller)]
    pub fn new<E>(error: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        let handler = Some(crate::capture_handler(&error));

        let inner = NarrowBox::new_unsize(ErrorImpl { handler, error });

        Report { inner }
    }

    /// Create a new error object from a printable error message.
    ///
    /// If the argument implements std::error::Error, prefer `Report::new`
    /// instead which preserves the underlying error's cause chain and
    /// backtrace. If the argument may or may not implement std::error::Error
    /// now or in the future, use `eyre!(err)` which handles either way
    /// correctly.
    ///
    /// `Report::msg("...")` is equivalent to `eyre!("...")` but occasionally
    /// convenient in places where a function is preferable over a macro, such
    /// as iterator or stream combinators:
    ///
    /// ```
    /// # mod ffi {
    /// #     pub struct Input;
    /// #     pub struct Output;
    /// #     pub async fn do_some_work(_: Input) -> Result<Output, &'static str> {
    /// #         unimplemented!()
    /// #     }
    /// # }
    /// #
    /// # use ffi::{Input, Output};
    /// #
    /// use eyre::{Report, Result};
    /// use futures::stream::{Stream, StreamExt, TryStreamExt};
    ///
    /// async fn demo<S>(stream: S) -> Result<Vec<Output>>
    /// where
    ///     S: Stream<Item = Input>,
    /// {
    ///     stream
    ///         .then(ffi::do_some_work) // returns Result<Output, &str>
    ///         .map_err(Report::msg)
    ///         .try_collect()
    ///         .await
    /// }
    /// ```
    #[cfg_attr(track_caller, track_caller)]
    pub fn msg<M>(message: M) -> Self
    where
        M: Display + Debug + Send + Sync + 'static,
    {
        use crate::wrapper::MessageError;
        Self::new(MessageError(message))
    }

    #[cfg_attr(track_caller, track_caller)]
    pub(crate) fn from_display<M>(message: M) -> Self
    where
        M: Display + Send + Sync + 'static,
    {
        use crate::wrapper::DisplayError;
        Self::new(DisplayError(message))
    }

    #[cfg_attr(track_caller, track_caller)]
    pub(crate) fn from_msg<D, E>(msg: D, error: E) -> Self
    where
        D: Display + Send + Sync + 'static,
        E: StdError + Send + Sync + 'static,
    {
        let error: ContextError<D, E> = ContextError { msg, error };

        Self::new(error)
    }

    #[cfg_attr(track_caller, track_caller)]
    pub(crate) fn from_boxed(error: Box<dyn StdError + Send + Sync>) -> Self {
        use crate::wrapper::BoxedError;
        let error = BoxedError(error);
        Self::new(error)
    }

    /// Create a new error from an error message to wrap the existing error.
    ///
    /// For attaching a higher level error message to a `Result` as it is propagated, the
    /// [`WrapErr`][crate::WrapErr] extension trait may be more convenient than this function.
    ///
    /// The primary reason to use `error.wrap_err(...)` instead of `result.wrap_err(...)` via the
    /// `WrapErr` trait would be if the message needs to depend on some data held by the underlying
    /// error:
    ///
    /// ```
    /// # use std::fmt::{self, Debug, Display};
    /// #
    /// # type T = ();
    /// #
    /// # impl std::error::Error for ParseError {}
    /// # impl Debug for ParseError {
    /// #     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    /// #         unimplemented!()
    /// #     }
    /// # }
    /// # impl Display for ParseError {
    /// #     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    /// #         unimplemented!()
    /// #     }
    /// # }
    /// #
    /// use eyre::Result;
    /// use std::fs::File;
    /// use std::path::Path;
    ///
    /// struct ParseError {
    ///     line: usize,
    ///     column: usize,
    /// }
    ///
    /// fn parse_impl(file: File) -> Result<T, ParseError> {
    ///     # const IGNORE: &str = stringify! {
    ///     ...
    ///     # };
    ///     # unimplemented!()
    /// }
    ///
    /// pub fn parse(path: impl AsRef<Path>) -> Result<T> {
    ///     let file = File::open(&path)?;
    ///     parse_impl(file).map_err(|error| {
    ///         let message = format!(
    ///             "only the first {} lines of {} are valid",
    ///             error.line, path.as_ref().display(),
    ///         );
    ///         eyre::Report::new(error).wrap_err(message)
    ///     })
    /// }
    /// ```
    pub fn wrap_err<D>(mut self, msg: D) -> Self
    where
        D: Display + Send + Sync + 'static,
    {
        let handler = self.inner.handler_mut().take();
        let error: ContextError<D, Report> = ContextError { msg, error: self };

        let inner = NarrowBox::new_unsize(ErrorImpl { handler, error });

        Report { inner }
    }

    /// An iterator of the chain of source errors contained by this Report.
    ///
    /// This iterator will visit every error in the cause chain of this error
    /// object, beginning with the error that this error object was created
    /// from.
    ///
    /// # Example
    ///
    /// ```
    /// use eyre::Report;
    /// use std::io;
    ///
    /// pub fn underlying_io_error_kind(error: &Report) -> Option<io::ErrorKind> {
    ///     for cause in error.chain() {
    ///         if let Some(io_error) = cause.downcast_ref::<io::Error>() {
    ///             return Some(io_error.kind());
    ///         }
    ///     }
    ///     None
    /// }
    /// ```
    pub fn chain(&self) -> Chain<'_> {
        Chain::new(self.inner.error())
    }

    /// The lowest level cause of this error &mdash; this error's cause's
    /// cause's cause etc.
    ///
    /// The root cause is the last error in the iterator produced by
    /// [`chain()`][Report::chain].
    pub fn root_cause(&self) -> &(dyn StdError + 'static) {
        let mut chain = self.chain();
        let mut root_cause = chain.next().unwrap();
        for cause in chain {
            root_cause = cause;
        }
        root_cause
    }

    /// Returns true if `E` is the type held by this error object.
    ///
    /// For errors constructed from messages, this method returns true if `E` matches the type of
    /// the message `D` **or** the type of the error on which the message has been attached. For
    /// details about the interaction between message and downcasting, [see here].
    ///
    /// [see here]: trait.WrapErr.html#effect-on-downcasting
    pub fn is<E>(&self) -> bool
    where
        E: Display + Debug + Send + Sync + 'static,
    {
      self.inner.is(TypeId::of::<E>())
    }

    /// Attempt to downcast the error object to a concrete type.
    pub fn downcast<E>(self) -> Result<E, Self>
    where
        E: Display + Debug + Send + Sync + 'static,
    {
        if self.is::<E>() {
            unsafe {
              let nb: NarrowBox<E> = self.inner.downcast_unchecked();
              let error: E = nb.into_inner();
              Ok(error)
            }
        } else {
            Err(self)
        }
    }

    /// Downcast this error object by reference.
    ///
    /// # Example
    ///
    /// ```
    /// # use eyre::{Report, eyre};
    /// # use std::fmt::{self, Display};
    /// # use std::task::Poll;
    /// #
    /// # #[derive(Debug)]
    /// # enum DataStoreError {
    /// #     Censored(()),
    /// # }
    /// #
    /// # impl Display for DataStoreError {
    /// #     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    /// #         unimplemented!()
    /// #     }
    /// # }
    /// #
    /// # impl std::error::Error for DataStoreError {}
    /// #
    /// # const REDACTED_CONTENT: () = ();
    /// #
    /// # let error: Report = eyre!("...");
    /// # let root_cause = &error;
    /// #
    /// # let ret =
    /// // If the error was caused by redaction, then return a tombstone instead
    /// // of the content.
    /// match root_cause.downcast_ref::<DataStoreError>() {
    ///     Some(DataStoreError::Censored(_)) => Ok(Poll::Ready(REDACTED_CONTENT)),
    ///     None => Err(error),
    /// }
    /// # ;
    /// ```
    pub fn downcast_ref<E>(&self) -> Option<&E>
    where
        E: Display + Debug + Send + Sync + 'static,
    {
        if self.is::<E>() {
            let error: &E = unsafe { self.inner.downcast_ref_unchecked() };
            Some(error)
        } else {
            None
        }
    }

    /// Downcast this error object by mutable reference.
    pub fn downcast_mut<E>(&mut self) -> Option<&mut E>
    where
        E: Display + Debug + Send + Sync + 'static,
    {
        if self.is::<E>() {
            let error: &mut E = unsafe { self.inner.downcast_mut_unchecked() };
            Some(error)
        } else {
            None
        }
    }

    /// Get a reference to the Handler for this Report.
    pub fn handler(&self) -> &dyn EyreHandler {
        &**self.inner.handler().as_ref().unwrap()
    }

    /// Get a mutable reference to the Handler for this Report.
    pub fn handler_mut(&mut self) -> &mut dyn EyreHandler {
        &mut **self.inner.handler_mut().as_mut().unwrap()
    }

    /// Get a reference to the Handler for this Report.
    #[doc(hidden)]
    pub fn context(&self) -> &dyn EyreHandler {
        self.handler()
    }

    /// Get a mutable reference to the Handler for this Report.
    #[doc(hidden)]
    pub fn context_mut(&mut self) -> &mut dyn EyreHandler {
        self.handler_mut()
    }
}

impl<E> From<E> for Report
where
    E: StdError + Send + Sync + 'static,
{
    #[cfg_attr(track_caller, track_caller)]
    fn from(error: E) -> Self {
        Report::new(error)
    }
}

impl Deref for Report {
    type Target = dyn StdError + Send + Sync + 'static;

    fn deref(&self) -> &Self::Target {
        &*self.inner.error()
    }
}

impl DerefMut for Report {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.inner.error_mut()
    }
}

impl Display for Report {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.deref().display(formatter)
    }
}

impl Debug for Report {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.deref().debug(formatter)
    }
}

pub(crate) struct ErrorImpl<E> {
    pub(crate) handler: Option<Box<dyn EyreHandler>>,
    error: E,
}

pub(crate) trait ErrorWithHandler: Send + Sync + 'static {
    fn handler(&self) -> &Option<Box<dyn EyreHandler>>;
    fn handler_mut(&mut self) -> &mut Option<Box<dyn EyreHandler>>;
    fn error(&self) -> &(dyn StdError + Send + Sync + 'static);
    fn error_mut(&mut self) -> &mut (dyn StdError + Send + Sync + 'static);
    fn get_reboxer(&self) -> fn(Report) -> Box<dyn StdError + Send + Sync + 'static>;
    fn is(&self, other: TypeId) -> bool;
}

impl<E: StdError + Send + Sync + 'static> ErrorWithHandler for ErrorImpl<E> {
    fn handler(&self) -> &Option<Box<dyn EyreHandler>> {
        &self.handler
    }

    fn handler_mut(&mut self) -> &mut Option<Box<dyn EyreHandler>> {
        &mut self.handler
    }

    fn error(&self) -> &(dyn StdError + Send + Sync + 'static) {
        &self.error
    }

    fn error_mut(&mut self) -> &mut (dyn StdError + Send + Sync + 'static) {
        &mut self.error
    }

    fn get_reboxer(&self) -> fn(Report) -> Box<dyn StdError + Send + Sync + 'static> {
      return rebox::<E>;
    }

    fn is(&self, other:TypeId) -> bool {
        TypeId::of::<E>() == other
    }
}

fn rebox<E: StdError + Send + Sync + 'static>(r: Report) -> Box<dyn StdError + Send + Sync + 'static> {
    Box::new(r.downcast::<E>().unwrap())
}

// repr C to ensure that ContextError<D, E> has the same layout as
// ContextError<ManuallyDrop<D>, E> and ContextError<D, ManuallyDrop<E>>.
#[repr(C)]
pub(crate) struct ContextError<D, E> {
    pub(crate) msg: D,
    pub(crate) error: E,
}

impl From<Report> for Box<dyn StdError + Send + Sync + 'static> {
    fn from(error: Report) -> Self {
      let r = error.inner.get_reboxer();
      r(error)
    }
}

impl From<Report> for Box<dyn StdError + 'static> {
    fn from(error: Report) -> Self {
        Box::<dyn StdError + Send + Sync>::from(error)
    }
}

impl AsRef<dyn StdError + Send + Sync> for Report {
    fn as_ref(&self) -> &(dyn StdError + Send + Sync + 'static) {
        &**self
    }
}

impl AsRef<dyn StdError> for Report {
    fn as_ref(&self) -> &(dyn StdError + 'static) {
        &**self
    }
}

#[cfg(feature = "pyo3")]
mod pyo3_compat;
