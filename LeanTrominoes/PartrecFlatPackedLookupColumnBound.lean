import LeanTrominoes.PartrecFlatPackedLookupColumnSpace

/-!
# Native-field bounds for flat packed lookup

The exact evaluator certificates retain an unconsumed suffix of the motif's
coordinate fields.  This module establishes one fixed envelope, expressed in
the original native fields, for every suffix state and countdown input reached
during a lookup pass.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

theorem flatLookupEncodedFieldSpace_le_of_mem
    (field : Nat) (fields : List Nat) (member : field ∈ fields) :
    (Computability.encodeNat field).length + 1 ≤
      encodedListSpace fields := by
  induction fields with
  | nil => simp at member
  | cons value fields induction =>
      rw [encodedListSpace_cons]
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · omega
      · exact (induction member).trans (by omega)

theorem flatLookupEncodedListSpace_suffix_le
    (leadingFields suffix : List Nat) :
    encodedListSpace suffix ≤
      encodedListSpace (leadingFields ++ suffix) := by
  induction leadingFields with
  | nil => simp
  | cons value leadingFields induction =>
      rw [List.cons_append, encodedListSpace_cons]
      exact induction.trans (by omega)

/-- Original native fields against which a complete lookup pass is charged. -/
def flatPackedLookupEnvelopeFields
    (target : Cell) (motif : List Cell)
    (wordLimit digitLimit : Nat) : List Nat :=
  [motif.length, Encodable.encode target.1, Encodable.encode target.2,
    wordLimit, digitLimit] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields

theorem flatPackedLookupSuffixSpace_le
    (motif suffix leading : List Cell)
    (decomposition : motif = leading ++ suffix) :
    encodedListSpace
        (suffix.flatMap PeriodicStripFlatEncoding.cellFields) ≤
      encodedListSpace
        (motif.flatMap PeriodicStripFlatEncoding.cellFields) := by
  let suffixFields := suffix.flatMap PeriodicStripFlatEncoding.cellFields
  have bound := flatLookupEncodedListSpace_suffix_le
    (leading.flatMap PeriodicStripFlatEncoding.cellFields)
    suffixFields
  simpa [decomposition, suffixFields, List.flatMap_append] using bound

/-- Every reachable scanner payload fits in the original native envelope plus
the two Boolean flag cells. -/
theorem flatPackedLookupStateSpace_le
    (target : Cell) (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ suffix)
    (wordBound : word ≤ wordLimit)
    (digitBound : digit ≤ digitLimit) :
    encodedListSpace
        (Code.flatPackedLookupColumnState target word digit found selected
          suffix) ≤
      encodedListSpace
          (flatPackedLookupEnvelopeFields target motif
            wordLimit digitLimit) + 4 := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  let targetX := Encodable.encode target.1
  let targetY := Encodable.encode target.2
  let suffixFields := suffix.flatMap PeriodicStripFlatEncoding.cellFields
  have suffixSpace := flatPackedLookupSuffixSpace_le motif suffix
    leading decomposition
  have inputExpanded :
      encodedListSpace fields =
        (Computability.encodeNat motif.length).length + 1 +
        ((Computability.encodeNat targetX).length + 1 +
        ((Computability.encodeNat targetY).length + 1 +
        ((Computability.encodeNat wordLimit).length + 1 +
        ((Computability.encodeNat digitLimit).length + 1 +
          encodedListSpace
            (motif.flatMap PeriodicStripFlatEncoding.cellFields))))) := by
    simp [fields, flatPackedLookupEnvelopeFields, targetX, targetY,
      encodedListSpace_cons]
  have wordBits := encodeNat_length_mono wordBound
  have digitBits := encodeNat_length_mono digitBound
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases found <;> cases selected <;>
    simp [Code.flatPackedLookupColumnState,
      encodedListSpace_cons, fields, targetX, targetY,
      zeroBits, oneBits] at inputExpanded suffixSpace ⊢ <;>
    omega

/-- Adding a bounded countdown field still changes the native envelope by
only a constant number of cells. -/
theorem flatPackedLookupCountdownStateSpace_le
    (steps : Nat) (target : Cell) (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ suffix)
    (stepsBound : steps ≤ motif.length)
    (wordBound : word ≤ wordLimit)
    (digitBound : digit ≤ digitLimit) :
    encodedListSpace
        (steps :: Code.flatPackedLookupColumnState target word digit
          found selected suffix) ≤
      encodedListSpace
          (flatPackedLookupEnvelopeFields target motif
            wordLimit digitLimit) + 4 := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  let targetX := Encodable.encode target.1
  let targetY := Encodable.encode target.2
  let suffixFields := suffix.flatMap PeriodicStripFlatEncoding.cellFields
  have suffixSpace := flatPackedLookupSuffixSpace_le motif suffix
    leading decomposition
  have inputExpanded :
      encodedListSpace fields =
        (Computability.encodeNat motif.length).length + 1 +
        ((Computability.encodeNat targetX).length + 1 +
        ((Computability.encodeNat targetY).length + 1 +
        ((Computability.encodeNat wordLimit).length + 1 +
        ((Computability.encodeNat digitLimit).length + 1 +
          encodedListSpace
            (motif.flatMap PeriodicStripFlatEncoding.cellFields))))) := by
    simp [fields, flatPackedLookupEnvelopeFields, targetX, targetY,
      encodedListSpace_cons]
  have stepsBits := encodeNat_length_mono stepsBound
  have wordBits := encodeNat_length_mono wordBound
  have digitBits := encodeNat_length_mono digitBound
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases found <;> cases selected <;>
    simp [Code.flatPackedLookupColumnState,
      encodedListSpace_cons, fields, targetX, targetY,
      zeroBits, oneBits] at inputExpanded suffixSpace ⊢ <;>
    omega

end EvaluatorCodeFits
end PartrecToTM2
end Turing
