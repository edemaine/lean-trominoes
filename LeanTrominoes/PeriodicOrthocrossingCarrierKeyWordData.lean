/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CellData

/-! # Self-delimiting binary words for carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierKeyWords

abbrev CarrierKey := Nat × Nat × Cell

/-- Unary natural field terminated by `true`. -/
def natField (number : Nat) : List Bool :=
  List.replicate number false ++ [true]

/-- Canonical signed unary field.  The leading sign bit is `false` for
`ofNat` and `true` for `negSucc`. -/
def intField : Int → List Bool
  | .ofNat number => false :: natField number
  | .negSucc number => true :: natField number

/-- Four self-delimiting fields encoding route index, segment index, and the
two coordinates of the occurrence translation. -/
def word (key : CarrierKey) : List Bool :=
  natField key.1 ++
    natField key.2.1 ++
      intField key.2.2.1 ++ intField key.2.2.2

/-- Decode one terminated unary natural field, retaining the suffix. -/
def decodeNatAux : Nat → List Bool → Option (Nat × List Bool)
  | _, [] => none
  | count, false :: bits => decodeNatAux (count + 1) bits
  | count, true :: bits => some (count, bits)

def decodeNat (bits : List Bool) : Option (Nat × List Bool) :=
  decodeNatAux 0 bits

/-- Decode one signed unary integer field, retaining the suffix. -/
def decodeInt : List Bool → Option (Int × List Bool)
  | [] => none
  | sign :: bits => do
      let (number, suffix) ← decodeNat bits
      pure (if sign then Int.negSucc number else Int.ofNat number, suffix)

/-- Decode four consecutive fields as one carrier key; trailing bits are
returned so injectivity does not depend on end-of-word inspection. -/
def decode : List Bool → Option (CarrierKey × List Bool)
  | bits => do
      let (routeIndex, bits) ← decodeNat bits
      let (segmentIndex, bits) ← decodeNat bits
      let (horizontal, bits) ← decodeInt bits
      let (vertical, bits) ← decodeInt bits
      pure ((routeIndex, segmentIndex, (horizontal, vertical)), bits)

end LeanTrominoes.PeriodicOrthocrossing.CarrierKeyWords
