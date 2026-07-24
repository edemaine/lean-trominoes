import LeanTrominoes.StripFrontierIndex

/-!
# Computability of arithmetic frontier decoding

The indexed strip algorithm reads a polynomial-length base-nine frontier word
from a natural state index.  This file proves the low-level digit and word
decoders primitive recursive.  In particular, decoding maps over
`List.range length`; it does not construct the exponentially large range of
state indices.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

open LeanTrominoes.Computability

theorem assignmentDigit_primrec : Primrec assignmentDigit :=
  Primrec.dom_finite assignmentDigit

theorem assignmentOfDigit_primrec : Primrec assignmentOfDigit := by
  unfold assignmentOfDigit
  exact Primrec.list_getD (none : Option SquareSymmetry) |>.comp
    (Primrec.const TrominoAssignment.assignmentStateList) Primrec.id

theorem nat_pow_primrec : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem assignmentDigitAt_primrec : Primrec₂ assignmentDigitAt := by
  unfold assignmentDigitAt
  exact Primrec.nat_mod.comp₂
    (Primrec.nat_div.comp₂ Primrec₂.left
      (nat_pow_primrec.comp₂ (Primrec₂.const (9 : Nat)) Primrec₂.right))
    (Primrec₂.const (9 : Nat))

theorem decodeAssignment_primrec : Primrec₂ decodeAssignment := by
  change Primrec fun input : Nat × Nat =>
    decodeAssignment input.1 input.2
  unfold decodeAssignment
  exact Primrec.list_map
    (Primrec.list_range.comp Primrec.fst)
    (assignmentOfDigit_primrec.comp₂
      (assignmentDigitAt_primrec.comp₂
        (Primrec.snd.comp₂ Primrec₂.left)
        Primrec₂.right))

end RawWindowState
end PeriodicStrip
end LeanTrominoes
