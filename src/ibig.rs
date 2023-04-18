use crate::{
    atom::Atom,
    convert::{Error, IsNoun},
    noun::Noun,
};
use ibig::UBig;

impl From<UBig> for Atom {
    fn from(ubig: UBig) -> Self {
        // XXX: add endian-ness tests.
        Self::from_le_bytes(ubig.to_le_bytes().to_vec())
    }
}

impl From<&UBig> for Atom {
    fn from(ubig: &UBig) -> Self {
        // XXX: add endian-ness tests.
        Self::from_le_bytes(ubig.to_le_bytes().to_vec())
    }
}

impl From<Atom> for UBig {
    fn from(atom: Atom) -> Self {
        Self::from_le_bytes(atom.as_bytes())
    }
}

impl From<&Atom> for UBig {
    fn from(atom: &Atom) -> Self {
        Self::from_le_bytes(atom.as_bytes())
    }
}

impl IsNoun for UBig {
    fn encode_noun(&self) -> Noun {
        Atom::from(self).encode_noun()
    }

    fn decode_noun(noun: &Noun) -> Result<Self, Error> {
        Ok(UBig::from(Atom::decode_noun(noun)?))
    }
}
