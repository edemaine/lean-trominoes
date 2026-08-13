import LeanTrominoes.PartrecDynamicDrop
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecListCodeSpace

/-!
# Evaluator-space certificate for dynamic native-list suffix selection

Dynamic drop is a tail-recursive countdown.  Every reachable payload is a
suffix of the original list, so one linear envelope fits every iteration.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def dynamicDropCost (count : Nat) (values : List Nat) : Nat :=
  1000000 * (encodedListSpace (count :: values) + 1)

def DynamicDropInvariant
    (count : Nat) (values : List Nat)
    (remaining : Nat) (payload : List Nat) : Prop :=
  remaining ≤ count ∧ encodedListSpace payload ≤ encodedListSpace values

theorem dynamicDropInvariant_initial (count : Nat) (values : List Nat) :
    DynamicDropInvariant count values count values := by
  exact ⟨by rfl, by rfl⟩

theorem dynamicDropInvariant_preserved
    (count : Nat) (values : List Nat)
    (remaining : Nat) (payload : List Nat)
    (invariant : DynamicDropInvariant count values (remaining + 1) payload) :
    DynamicDropInvariant count values remaining payload.tail := by
  exact ⟨(Nat.le_succ remaining).trans invariant.1,
    (listCodeEncodedListSpace_tail_le payload).trans invariant.2⟩

theorem dynamicDropBodyCost_le
    (count : Nat) (values : List Nat)
    (remaining : Nat) (payload : List Nat)
    (invariant : DynamicDropInvariant count values remaining payload) :
    flatCountdownBodyCost List.tail tailCost remaining payload ≤
      dynamicDropCost count values := by
  have payloadSpace := invariant.2
  have remainingLe := invariant.1
  have remainingBound := listCodeEncodeNat_length_mono invariant.1
  have inputSpace :
      encodedListSpace (remaining :: payload) ≤
        encodedListSpace (count :: values) := by
    simp only [encodedListSpace_cons]
    omega
  have tailSpace := listCodeEncodedListSpace_tail_le payload
  have headSpace := listCodeEncodedListSpace_singleton_headI_le payload
  have headBits :
      (Computability.encodeNat payload.headI).length ≤
        encodedListSpace payload := by
    simpa [encodedListSpace_cons] using headSpace
  have headSuccessor := listCodeEncodeNat_succ_length_le payload.headI
  have remainingSuccessor := listCodeEncodeNat_succ_length_le remaining
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [flatCountdownBodyCost, dynamicDropCost, zeroPrimeCost,
        encodedListSpace_cons, zeroBits]
      omega
  | succ remaining =>
      have oneToCount := listCodeEncodeNat_length_mono
        (show 1 ≤ count by omega)
      rw [oneBits] at oneToCount
      have predecessorBits := listCodeEncodeNat_length_mono
        (show remaining ≤ remaining + 1 by omega)
      have currentSuccessorBits := listCodeEncodeNat_succ_length_le
        (remaining + 1)
      simp [flatCountdownBodyCost, flatCountdownSuccBranchCost,
        dynamicDropCost, prependCost, tailCost, headCost, oneCost,
        zeroCost, nilCost, idCost, zeroPrimeCost, succCost,
        encodedListSpace_cons, zeroBits, oneBits] at *
      omega

theorem dynamicDropSpace_drop_le (count : Nat) (values : List Nat) :
    encodedListSpace (values.drop count) ≤ encodedListSpace values := by
  induction count generalizing values with
  | zero => simp
  | succ count induction =>
      cases values with
      | nil => simp
      | cons head tail =>
          have tailBound := listCodeEncodedListSpace_tail_le (head :: tail)
          have recursive := induction tail
          simpa [List.drop] using recursive.trans tailBound

theorem dynamicDrop_iterated_tail (count : Nat) (values : List Nat) :
    ((List.tail)^[count]) values = values.drop count := by
  induction count generalizing values with
  | zero => rfl
  | succ count induction =>
      rw [Function.iterate_succ_apply]
      simpa using induction values.tail

/-- Exact evaluator certificate for runtime suffix selection. -/
theorem dynamicDrop (count : Nat) (values : List Nat) :
    EvaluatorCodeFits Code.dynamicDropCode (count :: values)
      (values.drop count) (dynamicDropCost count values) := by
  let cost := dynamicDropCost count values
  have input : encodedListSpace (count :: values) ≤ cost := by
    simp [cost, dynamicDropCost]
    omega
  have suffix : encodedListSpace (values.drop count) ≤ cost := by
    have localBound := dynamicDropSpace_drop_le count values
    simp [cost, dynamicDropCost, encodedListSpace_cons]
    omega
  refine
    { input_space := input
      output_space := suffix
      call := ?_ }
  intro continuation bound budget after
  have bodyFits : ∀ remaining payload,
      EvaluatorCodeFits (Code.flatCountdownBody Code.tail)
        (remaining :: payload)
        (flatCountdownOutput List.tail remaining payload)
        (flatCountdownBodyCost List.tail tailCost remaining payload) := by
    intro remaining payload
    exact flatCountdownBody (fun payload => tail_named payload)
      remaining payload
  apply EvaluatorCallFits.flatIterate_of_code_fits_invariant
      bodyFits (dynamicDropInvariant_initial count values)
      (dynamicDropInvariant_preserved count values)
  · intro remaining payload invariant
    have localCost := dynamicDropBodyCost_le count values remaining payload
      invariant
    omega
  · simpa [dynamicDrop_iterated_tail count values] using after

theorem dynamicDropCost_le_linear (count : Nat) (values : List Nat) :
    dynamicDropCost count values ≤
      1000000 * (encodedListSpace (count :: values) + 1) := by rfl

end EvaluatorCodeFits
end PartrecToTM2
end Turing
