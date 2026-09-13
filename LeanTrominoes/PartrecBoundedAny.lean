/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedAll
import LeanTrominoes.IndexedSavitch

/-! # A streaming bounded existential evaluator -/

namespace Turing.ToPartrec.Code

def boundedAnyCode (leaf : Code) : Code := isZero (boundedAll (isZero leaf))

theorem allFrom_not (predicate : Nat → Bool) (count : Nat) :
    allFrom (fun i => !(predicate i)) 0 count = !(LeanTrominoes.FiniteState.boundedAny predicate count) := by
  apply Bool.eq_iff_iff.mpr
  have neg (b : Bool) : (Bool.not b = true) ↔ ¬ b = true := by cases b <;> decide
  change (allFrom (fun i => !(predicate i)) 0 count = true) ↔
    (Bool.not (LeanTrominoes.FiniteState.boundedAny predicate count) = true)
  simp only [allFrom_eq_true_iff,neg,Nat.zero_le,Nat.zero_add,true_implies,
    LeanTrominoes.FiniteState.boundedAny_eq_true_iff,not_exists,not_and]

theorem isZero_eval_bool (leaf : Code) (values : List Nat) (value : Bool)
    (run : leaf.eval values = pure [value.toNat]) :
    (isZero leaf).eval values = pure [(!value).toNat] := by
  have h := isZero_eval_at leaf values value.toNat run
  cases value <;> simpa using h

theorem boundedAnyCode_eval (leaf : Code) (payload : List Nat) (predicate : Nat → Bool)
    (leafRun : ∀ i, leaf.eval (i :: payload) = pure [(predicate i).toNat]) (count : Nat) :
    (boundedAnyCode leaf).eval (count :: payload) = pure [(LeanTrominoes.FiniteState.boundedAny predicate count).toNat] := by
  have negative := boundedAll_eval (isZero leaf) payload (fun i => !(predicate i))
    (fun i => isZero_eval_bool leaf (i :: payload) (predicate i) (leafRun i)) count
  have outer := isZero_eval_bool (boundedAll (isZero leaf)) (count :: payload)
    (allFrom (fun i => !(predicate i)) 0 count) negative
  simpa [boundedAnyCode,allFrom_not] using outer

end Turing.ToPartrec.Code
