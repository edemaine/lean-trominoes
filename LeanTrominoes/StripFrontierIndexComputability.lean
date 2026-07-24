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

theorem rawWindowState_equivData_primrec :
    Primrec equivData :=
  Primrec.of_equiv

theorem rawWindowState_phase_primrec :
    Primrec RawWindowState.phase := by
  exact (Primrec.fst.comp rawWindowState_equivData_primrec).of_eq
    (fun _ => rfl)

theorem rawWindowState_assignment_primrec :
    Primrec RawWindowState.assignment := by
  exact (Primrec.snd.comp rawWindowState_equivData_primrec).of_eq
    (fun _ => rfl)

theorem motifCells_primrec : Primrec motifCells := by
  exact periodicStrip_motif_primrec

theorem assignmentKeys_primrec : Primrec assignmentKeys := by
  have cellsForColumn : Primrec₂ fun
      (periodicStrip : PeriodicStrip) (column : WindowColumn) =>
      (motifCells periodicStrip).map fun cell => (column, cell) := by
    exact Primrec.list_map
      (motifCells_primrec.comp Primrec.fst)
      (Primrec₂.pair.comp₂
        (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
  exact Primrec.list_flatMap
    (Primrec.const (List.finRange 5)) cellsForColumn

theorem assignmentAtCell_primrec :
    Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.1.assignmentAtCell input.1 input.2.2.1 input.2.2.2 := by
  let strip : Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.1 :=
    Primrec.fst
  let raw : Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let column : Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let cell : Primrec fun input :
      PeriodicStrip × RawWindowState × WindowColumn × Cell =>
      input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  unfold assignmentAtCell
  exact Primrec.list_getD (none : Option SquareSymmetry) |>.comp
    (rawWindowState_assignment_primrec.comp raw)
    (Primrec.list_idxOf.comp
      (Primrec.pair column cell)
      (assignmentKeys_primrec.comp strip))

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

theorem indexCount_primrec : Primrec indexCount := by
  unfold indexCount
  exact Primrec.nat_mul.comp periodicStrip_period_primrec
    (nat_pow_primrec.comp
      (Primrec.const (9 : Nat))
      (Primrec.list_length.comp assignmentKeys_primrec))

theorem ofIndex_primrec : Primrec₂ ofIndex := by
  change Primrec fun input : PeriodicStrip × Nat =>
    ofIndex input.1 input.2
  let period : Primrec fun input : PeriodicStrip × Nat =>
      input.1.period :=
    periodicStrip_period_primrec.comp Primrec.fst
  let phase : Primrec fun input : PeriodicStrip × Nat =>
      input.2 % input.1.period :=
    Primrec.nat_mod.comp Primrec.snd period
  let assignmentLength : Primrec fun input : PeriodicStrip × Nat =>
      (assignmentKeys input.1).length :=
    Primrec.list_length.comp (assignmentKeys_primrec.comp Primrec.fst)
  let assignmentCode : Primrec fun input : PeriodicStrip × Nat =>
      input.2 / input.1.period :=
    Primrec.nat_div.comp Primrec.snd period
  let assignment : Primrec fun input : PeriodicStrip × Nat =>
      decodeAssignment (assignmentKeys input.1).length
        (input.2 / input.1.period) :=
    decodeAssignment_primrec.comp assignmentLength assignmentCode
  have inversePrimrec : Primrec equivData.symm :=
    Primrec.of_equiv_symm
  exact (inversePrimrec.comp (Primrec.pair phase assignment)).of_eq
    fun _ => rfl

end RawWindowState
end PeriodicStrip
end LeanTrominoes
