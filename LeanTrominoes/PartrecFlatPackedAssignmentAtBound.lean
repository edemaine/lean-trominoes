import LeanTrominoes.PartrecFlatPackedAssignmentAtSpace
import LeanTrominoes.PartrecFlatPackedLookupColumnBound

/-!
# Native-field bounds for five-column flat assignment lookup

All five stages share one envelope containing the original packed word, the
queried column, a constant accumulator-digit ceiling, and the native motif
stream.  This module first relates every one-column scanner call to that common
envelope, then lifts the bound through the exact five-stage certificate.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

/-- The digit accumulator starts at zero and grows by at most eight in each of
five passes.  We reserve eight additional units so every one-pass scanner's
internal `digit + 8` envelope fits uniformly. -/
def flatPackedAssignmentEnvelopeFields
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : List Nat :=
  queriedColumn :: flatPackedLookupEnvelopeFields target motif word 48

def flatPackedAssignmentInputUnit
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  encodedListSpace
      (flatPackedAssignmentEnvelopeFields motif queriedColumn target word) + 5

theorem flatPackedAssignmentUnitPositive
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    5 ≤ flatPackedAssignmentInputUnit motif queriedColumn target word := by
  simp [flatPackedAssignmentInputUnit]

theorem flatPackedAssignmentLookupUnit_le
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedLookupInputUnit target motif word 48 ≤
      flatPackedAssignmentInputUnit motif queriedColumn target word := by
  simp [flatPackedAssignmentInputUnit,
    flatPackedAssignmentEnvelopeFields, flatPackedLookupInputUnit,
    encodedListSpace_cons]

/-- Any reachable five-pass state fits in the common assignment envelope. -/
theorem flatPackedAssignmentStateSpace_le_unit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat) (found : Bool)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    encodedListSpace
        (Code.flatPackedAssignmentLookupState motif queriedColumn target
          (word, digit, found)) ≤
      flatPackedAssignmentInputUnit motif queriedColumn target initialWord := by
  let fields := flatPackedAssignmentEnvelopeFields motif queriedColumn
    target initialWord
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  have expanded :
      encodedListSpace fields =
        (Computability.encodeNat queriedColumn).length + 1 +
        ((Computability.encodeNat motif.length).length + 1 +
        ((Computability.encodeNat (Encodable.encode target.1)).length + 1 +
        ((Computability.encodeNat (Encodable.encode target.2)).length + 1 +
        ((Computability.encodeNat initialWord).length + 1 +
        ((Computability.encodeNat 48).length + 1 +
          encodedListSpace coordinates))))) := by
    simp [fields, flatPackedAssignmentEnvelopeFields,
      flatPackedLookupEnvelopeFields, coordinates, encodedListSpace_cons]
  have wordBits := encodeNat_length_mono wordBound
  have digitToForty := encodeNat_length_mono digitBound
  have fortyToFortyEight :
      (Computability.encodeNat 40).length ≤
        (Computability.encodeNat 48).length :=
    encodeNat_length_mono (by omega)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases found <;>
    simp [Code.flatPackedAssignmentLookupState,
      flatPackedAssignmentInputUnit, fields, coordinates,
      encodedListSpace_cons, zeroBits, oneBits] at expanded ⊢ <;>
    omega

/-- A one-column scanner whose accumulator is reachable within the five-pass
lookup fits the common assignment unit. -/
theorem flatPackedLookupInputUnit_le_assignmentUnit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    flatPackedLookupInputUnit target motif word (digit + 8) ≤
      flatPackedAssignmentInputUnit motif queriedColumn target initialWord := by
  have wordBits := encodeNat_length_mono wordBound
  have digitEnvelopeBound : digit + 8 ≤ 48 := by omega
  have digitBits := encodeNat_length_mono digitEnvelopeBound
  simp [flatPackedLookupInputUnit, flatPackedLookupEnvelopeFields,
    flatPackedAssignmentInputUnit, flatPackedAssignmentEnvelopeFields,
    encodedListSpace_cons]
  omega

theorem flatPackedLookupSpaceBound_le_assignmentUnit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    flatPackedLookupSpaceBound target motif word digit ≤
      100000000000000000000000000000000000 *
        (flatPackedAssignmentInputUnit motif queriedColumn target
          initialWord) ^ 2 := by
  have unitBound := flatPackedLookupInputUnit_le_assignmentUnit motif
    queriedColumn target initialWord word digit wordBound digitBound
  have squared :
      (flatPackedLookupInputUnit target motif word (digit + 8)) ^ 2 ≤
        (flatPackedAssignmentInputUnit motif queriedColumn target
          initialWord) ^ 2 := by
    nlinarith
  simpa only [flatPackedLookupSpaceBound] using
    Nat.mul_le_mul_left 100000000000000000000000000000000000 squared

theorem flatPackedLookupFlatCost_le_assignmentUnit
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (initialWord word digit : Nat) (found selected : Bool)
    (wordBound : word ≤ initialWord) (digitBound : digit ≤ 40) :
    flatPackedLookupFlatCost target selected motif word digit found ≤
      100000000000000000000000000000000000 *
        (flatPackedAssignmentInputUnit motif queriedColumn target
          initialWord) ^ 2 :=
  (flatPackedLookupFlatCost_le_quadratic
    target selected motif word digit found).trans
      (flatPackedLookupSpaceBound_le_assignmentUnit motif queriedColumn
        target initialWord word digit wordBound digitBound)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
