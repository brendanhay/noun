//! Conversions to and from [`Noun`](crate::noun::Noun).

use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use std::ops::Deref;
use std::{error, iter};

use crate::Rc;
use crate::{atom::Atom, cell::Cell, noun::Noun};

/// Errors that occur when converting from a noun.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// An atom could not be converted into an unsigned integer.
    AtomToUint,
    /// An atom could not be converted into a string.
    AtomToStr,
    /// A null atom was expected.
    ExpectedNull,
    /// An error specific to the implementing type occurred.
    ImplType,
    /// No value exists at a particular axis of a cell.
    MissingValue,
    /// Encountered an atom when a cell was expected.
    UnexpectedAtom,
    /// Encountered a cell when an atom was expected.
    UnexpectedCell,
    /// A cell could not be converted into an array of the expected length.
    CellToArray,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::AtomToUint => write!(
                f,
                "the atom is too large to fit in the unsigned integer type"
            ),
            Self::AtomToStr => write!(f, "the atom is not composed of valid UTF-8 bytes"),
            Self::ExpectedNull => write!(f, "a null atom was expected"),
            Self::ImplType => write!(f, "an error specific to the implementing type occurred"),
            Self::MissingValue => write!(f, "the noun does not have a value at this axis"),
            Self::UnexpectedAtom => write!(f, "an atom was encountered when a cell was expected"),
            Self::UnexpectedCell => write!(f, "a cell was encountered when an atom was expected"),
            Self::CellToArray => write!(
                f,
                "a cell could not be converted into an array of the expected length"
            ),
        }
    }
}

impl error::Error for Error {}

pub trait IsNoun: Sized {
    fn encode_noun(&self) -> Noun;

    fn decode_noun(noun: &Noun) -> Result<Self, Error>;
}

/// The null atom, `~`.
impl IsNoun for () {
    fn encode_noun(&self) -> Noun {
        Noun::null()
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        match noun {
            Noun::Atom(atom) if atom.is_null() => Ok(()),
            Noun::Atom(_atom) => Err(Error::UnexpectedAtom),
            Noun::Cell(_cell) => Err(Error::UnexpectedCell),
        }
    }
}

/// An arbitrary atom, `A`.
///
/// Encoding requires cloning the `Atom`. Use [`From<Atom>`] for zero-copy.
impl IsNoun for Atom {
    fn encode_noun(&self) -> Noun {
        Noun::Atom(self.clone())
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        match noun {
            Noun::Atom(atom) => Ok(atom.clone()),
            Noun::Cell(_cell) => Err(Error::UnexpectedCell),
        }
    }
}

/// An arbitrary noun, `N`.
///
/// Encoding and decoding requires cloning `Noun`. Use [`From<Noun>`] for zero-copy.
impl IsNoun for Noun {
    fn encode_noun(&self) -> Noun {
        self.clone()
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        Ok(noun.clone())
    }
}

/// A pair `[A B]`.
impl<A, B> IsNoun for (A, B)
where
    A: IsNoun,
    B: IsNoun,
{
    fn encode_noun(&self) -> Noun {
        Noun::from([self.0.encode_noun(), self.1.encode_noun()])
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        match noun {
            Noun::Atom(_atom) => Err(Error::UnexpectedAtom),
            Noun::Cell(cell) => {
                let a = A::decode_noun(cell.head_ref())?;
                let b = B::decode_noun(cell.tail_ref())?;

                Ok((a, b))
            }
        }
    }
}

macro_rules! impl_noun_for_tuple {
    ($( $ty:tt = $n:ident ),*) => {
        /// A n-ary tuple, `[$($ty )*]`.
        impl< $($ty),* > IsNoun for ( $($ty),* )
        where
            $(
                $ty: IsNoun,
            )*
        {
            fn encode_noun(&self) -> Noun {
                let ( $($n),* ) = self;

                Noun::from([
                    $(
                        $n.encode_noun(),
                    )*
                ])
            }

            fn decode_noun(noun: &Noun) -> Result<Self, Error> {
                match noun {
                    Noun::Atom(_atom) => Err(Error::UnexpectedAtom),
                    Noun::Cell(cell) => match cell.to_array() {
                        Some([ $($n),* ]) => Ok((
                            $(
                                <$ty>::decode_noun($n.deref())?,
                            )*
                        )),
                        None => Err(Error::CellToArray),
                    },
                }
            }
        }
    };
}

impl_noun_for_tuple!(A = a, B = b, C = c);
impl_noun_for_tuple!(A = a, B = b, C = c, D = d);
impl_noun_for_tuple!(A = a, B = b, C = c, D = d, E = e);
impl_noun_for_tuple!(A = a, B = b, C = c, D = d, E = e, F = f);
impl_noun_for_tuple!(A = a, B = b, C = c, D = d, E = e, F = f, G = g);
impl_noun_for_tuple!(A = a, B = b, C = c, D = d, E = e, F = f, G = g, H = h);

/// A null-terminated list, `[T1 T2 TN ~]`.
impl<T> IsNoun for Vec<T>
where
    T: IsNoun,
{
    fn encode_noun(&self) -> Noun {
        Noun::Cell(Cell::from(
            self.into_iter()
                .map(|item| Rc::new(item.encode_noun()))
                .chain(iter::once(Rc::new(Noun::null())))
                .collect::<Vec<_>>(),
        ))
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        let mut noun = noun;
        let mut vec: Vec<T> = Vec::new();

        loop {
            match noun {
                Noun::Atom(atom) if atom.is_null() => return Ok(vec),
                Noun::Atom(_atom) => return Err(Error::ExpectedNull),
                Noun::Cell(cell) => {
                    let item = T::decode_noun(cell.head_ref())?;
                    vec.push(item);

                    noun = cell.tail_ref();
                }
            }
        }
    }
}

/// A null-terminated map, `[[k0 v0] [k1 v1] ... [kN vN] ~]`.
impl<K, V> IsNoun for HashMap<K, V>
where
    K: Eq + Hash + IsNoun,
    V: IsNoun,
{
    fn encode_noun(&self) -> Noun {
        self.iter()
            .map(|(k, v)| {
                // Avoids unnecessary cloning going through (A, B).encode_noun().
                Noun::Cell(Cell::from([k.encode_noun(), v.encode_noun()]))
            })
            .collect::<Vec<_>>()
            .encode_noun()
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        let vec: Vec<(K, V)> = Vec::decode_noun(noun)?;
        Ok(vec.into_iter().collect())
    }
}

/// A null-terminated map, `[[k0 v0] [k1 v1] ... [kN vN] ~]`.
impl<K, V> IsNoun for BTreeMap<K, V>
where
    K: Ord + IsNoun,
    V: IsNoun,
{
    fn encode_noun(&self) -> Noun {
        self.iter()
            .map(|(k, v)| {
                // Avoids unnecessary cloning going through (A, B).encode_noun().
                Noun::Cell(Cell::from([k.encode_noun(), v.encode_noun()]))
            })
            .collect::<Vec<_>>()
            .encode_noun()
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        let vec: Vec<(K, V)> = Vec::decode_noun(noun)?;
        Ok(vec.into_iter().collect())
    }
}

/// Pointer wrapper types such as `Rc<T>`, `Box<T>`, etc.
macro_rules! impl_noun_for_pointers {
    ($( $ty:ty $(: $bounds:ident)? ),*) => {
        $(
            impl<T: IsNoun $(+ $bounds)?> IsNoun for $ty {
                fn encode_noun(&self) -> Noun {
                    self.deref().encode_noun()
                }

                fn decode_noun(noun: &Noun) -> Result<Self, Error> {
                    Ok(<$ty>::new(T::decode_noun(noun)?))
                }
            }
        )*
    };
}

impl_noun_for_pointers!(std::rc::Rc<T>, std::sync::Arc<T>, std::boxed::Box<T>);

impl<T> IsNoun for Option<T>
where
    T: IsNoun,
{
    fn encode_noun(&self) -> Noun {
        match self {
            Some(x) => Noun::from([().encode_noun(), x.encode_noun()]),
            None => Noun::null(),
        }
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        match noun {
            Noun::Atom(atom) if atom.is_null() => Ok(None),
            Noun::Atom(_atom) => Err(Error::UnexpectedAtom),
            Noun::Cell(_cell) => {
                let ((), tail) = <((), T)>::decode_noun(noun)?;
                Ok(Some(tail))
            }
        }
    }
}

/// Converts [`Noun`](crate::Noun)s to and from other complex types.
///
/// There are three forms of this macro:
///
/// - Convert a [`&Noun`] of the form `[e0 e1 ... eN 0]` (a null-terminated list) to a
///   [`Vec`]`<$elem_type>`, returning [`Result`]`<`[`Vec`]`<$elem_type>, `[`Error`]`>`.
///
///   `$elem_type` must implement [`TryFrom`]`<`[`&Noun`]`>`.
///
///   The resulting [`Vec`] does not include the null terminator.
///
/// ```
/// # use noun::{convert, noun::Noun};
/// let noun = Noun::null();
/// let vec = convert!(&noun => Vec<String>).unwrap();
/// assert!(vec.is_empty());
/// ```
///
/// ```
/// # use noun::{atom::Atom, cell::Cell, convert, noun::Noun};
/// let noun = Noun::from(Cell::from([
///     Atom::from("hello"),
///     Atom::from("world"),
///     Atom::null(),
/// ]));
/// let vec = convert!(&noun => Vec<String>).unwrap();
/// assert_eq!(vec, vec!["hello", "world"]);
/// ```
///
/// - Convert a [`&Noun`] of the form `[[k0 v0] [k1 v1] ... [kN vN] 0]` (a null-terminated map) to a
///   [`HashMap`]`<$key_type, $val_type>`, returning [`Result`]`<`[`HashMap`]`<$key_type, $val_type>,
///   `[`Error`]`>`.
///
///   `$key_type` and `$val_type` must each implement [`TryFrom`]`<`[`&Noun`]`>`.
///
///   The resulting [`HashMap`] does not include the null terminator.
///
/// ```
/// # use noun::{cell::Cell, convert, noun::Noun};
/// let noun = Noun::null();
/// let map = convert!(&noun => HashMap<&str, &str>).unwrap();
/// assert_eq!(map.len(), 0);
/// ```
///
/// ```
/// # use noun::{cell::Cell, convert, noun::Noun};
/// let noun = Noun::from(Cell::from([
///     Noun::from(Cell::from(["Ruth", "Babe"])),
///     Noun::from(Cell::from(["Williams", "Ted"])),
///     Noun::from(Cell::from(["Bonds", "Barry"])),
///     Noun::from(Cell::from(["Pujols", "Albert"])),
///     Noun::null()
/// ]));
/// let map = convert!(&noun => HashMap<&str, &str>).unwrap();
/// assert_eq!(map.len(), 4);
/// assert_eq!(map.get("Ruth"), Some(&"Babe"));
/// assert_eq!(map.get("Williams"), Some(&"Ted"));
/// assert_eq!(map.get("Bonds"), Some(&"Barry"));
/// assert_eq!(map.get("Pujols"), Some(&"Albert"));
/// ```
///
/// - Convert an iterator of the form `[e0, e1, ... eN]` where each element has type `T` into a
///   [`Noun`] of the form `[e0 e1 ... eN 0]` (a null-terminated list), returning
///   [`Result`]`<`[`Noun`]`, <err_type>>`, where `<err_type>` is the type of error returned by
///   `Noun::try_from` when attempting to convert `T` into a [`Noun`].
///
///   [`Noun`] must implement [`TryFrom`]`<T>`.
///
/// ```
/// # use noun::{atom::Atom, cell::Cell, convert, noun::Noun};
/// let strings = [];
/// let noun = convert!(strings.iter() => Noun).unwrap();
/// assert!(noun.is_null());
/// ```
///
/// ```
/// # use noun::{atom::Atom, cell::Cell, convert, noun::Noun};
/// let strings = vec![
///     String::from("1"),
///     String::from("2"),
///     String::from("3"),
///     String::from("4"),
/// ];
/// let noun = convert!(strings.into_iter() => Noun).unwrap();
/// assert_eq!(
///     noun,
///     Noun::from(Cell::from([
///         Atom::from("1"),
///         Atom::from("2"),
///         Atom::from("3"),
///         Atom::from("4"),
///         Atom::null(),
///     ]))
/// );
/// ```
///
/// [`Err(Error)`]: Error
/// [`HashMap`]: std::collections::HashMap
/// [`&Noun`]: crate::Noun
/// [`Noun`]: crate::Noun
#[macro_export]
macro_rules! convert {
    ($noun:expr => Vec<$elem_type:ty>) => {{
        use $crate::{convert::Error, noun::Noun};
        let mut noun = $noun;
        let mut elems: Vec<$elem_type> = Vec::new();
        loop {
            match noun {
                Noun::Atom(atom) => {
                    if atom.is_null() {
                        break Ok(elems);
                    } else {
                        break Err(Error::ExpectedNull);
                    }
                }
                Noun::Cell(cell) => match <$elem_type>::try_from(cell.head_ref()) {
                    Ok(elem) => {
                        elems.push(elem);
                        noun = cell.tail_ref();
                    }
                    Err(err) => break Err(err),
                },
            }
        }
    }};
    ($noun:expr => HashMap<$key_type:ty, $val_type:ty>) => {{
        use std::collections::HashMap;
        use $crate::{convert::Error, noun::Noun};
        let mut noun = $noun;
        let mut map: HashMap<$key_type, $val_type> = HashMap::new();
        loop {
            match noun {
                Noun::Atom(atom) => {
                    if atom.is_null() {
                        break Ok(map);
                    } else {
                        break Err(Error::ExpectedNull);
                    }
                }
                Noun::Cell(cell) => {
                    if let Noun::Cell(head) = cell.head_ref() {
                        match (
                            <$key_type>::try_from(head.head_ref()),
                            <$val_type>::try_from(head.tail_ref()),
                        ) {
                            (Ok(key), Ok(val)) => {
                                map.insert(key, val);
                                noun = cell.tail_ref();
                            }
                            (Err(err), _) => break Err(err),
                            (_, Err(err)) => break Err(err),
                        }
                    } else {
                        break Err(Error::UnexpectedAtom);
                    }
                }
            }
        }
    }};
    ($iter:expr => Noun) => {{
        use $crate::{cell::Cell, noun::Noun, Rc};
        let mut noun = Rc::<Noun>::from(Noun::null());
        let mut iter = $iter.rev();
        loop {
            match iter.next() {
                Some(elem) => match Noun::try_from(elem) {
                    Ok(elem) => {
                        noun = Rc::<Noun>::from(Noun::from(Cell::from([
                            Rc::<Noun>::from(elem),
                            noun,
                        ])));
                    }
                    Err(err) => break Err(err),
                },
                None => break Ok(Rc::try_unwrap(noun).unwrap()),
            }
        }
    }};
}

#[cfg(test)]
mod tests {
    use crate::{atom::Atom, cell::Cell, noun::Noun};

    #[test]
    fn convert() {
        // Noun -> Vec<String>: expect failure.
        {
            {
                let noun = Noun::from(Cell::from(["no", "null", "terminator"]));
                assert!(convert!(&noun => Vec<String>).is_err());
            }

            {
                let noun = Noun::from(Cell::from([
                    Noun::from(Cell::from(["unexpected", "cell"])),
                    Noun::null(),
                ]));
                assert!(convert!(&noun => Vec<String>).is_err());
            }
        }

        // &[&str] -> Noun: expect success.
        {
            {
                let strings = ["a", "b", "c"];
                let noun = convert!(strings.iter() => Noun).expect("&[str] to Noun");
                assert_eq!(
                    noun,
                    Noun::from(Cell::from([
                        Atom::from("a"),
                        Atom::from("b"),
                        Atom::from("c"),
                        Atom::null()
                    ]))
                );
            }
        }
    }
}
