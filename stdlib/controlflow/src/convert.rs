//! core::convert module`


#[rr::export_as(core::convert::AsRef)]
#[rr::exists("AsRefFn" : "{xt_of Self} → {xt_of T}")]
pub trait AsRef<T: ?Sized> {
    /// Converts this type into a shared reference of the (usually inferred) input type.
    #[rr::returns("{AsRefFn} self")]
    fn as_ref(&self) -> &T;
}

#[rr::export_as(core::convert::AsMut)]
// TODO: look at some example clients to figure out what kind of spec would be sensible
#[rr::exists("AsMutFn" : "{xt_of Self} → {xt_of T}")]
#[rr::exists("AsMutBackFn" : "{xt_of T} → {xt_of Self}")]
pub trait AsMut<T: ?Sized> {
    /// Converts this type into a mutable reference of the (usually inferred) input type.
    #[rr::exists("γ", "y")]
    //#[rr::observe("self.ghost" : "👻 γ")]
    #[rr::returns("(y, γ)")]
    fn as_mut(&mut self) -> &mut T;
}

#[rr::export_as(core::convert::Into)]
#[rr::exists("IntoFn" : "{xt_of Self} → {xt_of T}")]
pub trait Into<T>: Sized {
    /// Converts this type into the (usually inferred) input type.
    #[rr::returns("{IntoFn} self")]
    fn into(self) -> T;
}

#[rr::export_as(core::convert::From)]
#[rr::exists("FromFn" : "{xt_of T} → {xt_of Self}")]
pub trait From<T>: Sized {
    #[rr::returns("{FromFn} value")]
    fn from(value: T) -> Self;
}

#[rr::export_as(core::convert::TryInto)]
pub trait TryInto<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Performs the conversion.
    fn try_into(self) -> Result<T, Self::Error>;
}

#[rr::export_as(core::convert::TryFrom)]
pub trait TryFrom<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Performs the conversion.
    fn try_from(value: T) -> Result<Self, Self::Error>;
}


impl<T: ?Sized, U: ?Sized> AsRef<U> for &T
where
    T: AsRef<U>,
{
    #[inline]
    fn as_ref(&self) -> &U {
        <T as AsRef<U>>::as_ref(*self)
    }
}

// As lifts over &mut
impl<T: ?Sized, U: ?Sized> AsRef<U> for &mut T
where
    T: AsRef<U>,
{
    #[inline]
    fn as_ref(&self) -> &U {
        <T as AsRef<U>>::as_ref(*self)
    }
}

// AsMut lifts over &mut
impl<T: ?Sized, U: ?Sized> AsMut<U> for &mut T
where
    T: AsMut<U>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut U {
        (*self).as_mut()
    }
}

// From implies Into
#[rr::instantiate("IntoFn" := "{U::FromFn}")]
impl<T, U> Into<U> for T
where
    U: From<T>,
{

    #[rr::default_spec]
    fn into(self) -> U {
        U::from(self)
    }
}

#[rr::instantiate("FromFn" := "id")]
impl<T> From<T> for T {
    #[rr::default_spec]
    fn from(t: T) -> T {
        t
    }
}

//impl<T> From<!> for T {
    //fn from(t: !) -> T {
        //t
    //}
//}

// TryFrom implies TryInto
impl<T, U> TryInto<U> for T
where
    U: TryFrom<T>,
{
    type Error = U::Error;

    #[inline]
    fn try_into(self) -> Result<U, U::Error> {
        U::try_from(self)
    }
}

// Infallible conversions are semantically equivalent to fallible conversions
// with an uninhabited error type.
impl<T, U> TryFrom<U> for T
where
    U: Into<T>,
{
    type Error = Infallible;

    #[inline]
    fn try_from(value: U) -> Result<Self, Self::Error> {
        Ok(U::into(value))
    }
}

////////////////////////////////////////////////////////////////////////////////
// CONCRETE IMPLS
////////////////////////////////////////////////////////////////////////////////

/*
impl<T> AsRef<[T]> for [T] {
    #[inline(always)]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for [T] {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl AsRef<str> for str {
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self
    }
}

impl AsMut<str> for str {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}
*/

#[rr::export_as(core::convert::Infallible)]
#[rr::refined_by("unit")]
#[rr::partial]
pub enum Infallible {
}

/*
#[stable(feature = "convert_infallible", since = "1.34.0")]
impl Clone for Infallible {
    fn clone(&self) -> Infallible {
        match *self {}
    }
}

#[stable(feature = "convert_infallible", since = "1.34.0")]
impl fmt::Debug for Infallible {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

#[stable(feature = "convert_infallible", since = "1.34.0")]
impl fmt::Display for Infallible {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

#[stable(feature = "str_parse_error2", since = "1.8.0")]
impl Error for Infallible {
    fn description(&self) -> &str {
        match *self {}
    }
}

#[stable(feature = "convert_infallible", since = "1.34.0")]
impl PartialEq for Infallible {
    fn eq(&self, _: &Infallible) -> bool {
        match *self {}
    }
}

#[stable(feature = "convert_infallible", since = "1.34.0")]
impl Eq for Infallible {}

#[stable(feature = "convert_infallible", since = "1.34.0")]
impl PartialOrd for Infallible {
    fn partial_cmp(&self, _other: &Self) -> Option<crate::cmp::Ordering> {
        match *self {}
    }
}

#[stable(feature = "convert_infallible", since = "1.34.0")]
impl Ord for Infallible {
    fn cmp(&self, _other: &Self) -> crate::cmp::Ordering {
        match *self {}
    }
}

#[stable(feature = "convert_infallible", since = "1.34.0")]
impl From<!> for Infallible {
    #[inline]
    fn from(x: !) -> Self {
        x
    }
}
*/
