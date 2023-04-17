use crate::{atom::Atom, convert, noun::Noun};
use ibig::UBig;

// Atoms

#[cfg(feature = "ibig")]
impl From<UBig> for Atom {
    fn from(ubig: UBig) -> Self {
        // XXX: add endian-ness tests.
        Self::from_le_bytes(ubig.to_le_bytes().to_vec())
    }
}

#[cfg(feature = "ibig")]
impl From<&UBig> for Atom {
    fn from(ubig: &UBig) -> Self {
        // XXX: add endian-ness tests.
        Self::from_le_bytes(ubig.to_le_bytes().to_vec())
    }
}

#[cfg(feature = "ibig")]
impl From<Atom> for UBig {
    fn from(atom: Atom) -> Self {
        Self::from_le_bytes(atom.as_bytes())
    }
}

#[cfg(feature = "ibig")]
impl From<&Atom> for UBig {
    fn from(atom: &Atom) -> Self {
        Self::from_le_bytes(atom.as_bytes())
    }
}

// Nouns

#[cfg(feature = "ibig")]
impl TryFrom<Noun> for UBig {
    type Error = convert::Error;

    fn try_from(noun: Noun) -> Result<Self, Self::Error> {
        Ok(Self::from(Atom::try_from(noun)?))
    }
}
