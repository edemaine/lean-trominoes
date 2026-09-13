/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecListCode

/-! # Uniform tail loops for bounded universal quantifiers -/

namespace Turing.ToPartrec.Code

/-- The semantic bounded conjunction, starting at an arbitrary index. -/
def allFrom (predicate : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | count+1 => predicate start && allFrom predicate (start+1) count

theorem allFrom_eq_true_iff (predicate : Nat → Bool) (start count : Nat) :
    allFrom predicate start count = true ↔ ∀ i, start ≤ i → i < start+count → predicate i = true := by
  induction count generalizing start with
  | zero => simp [allFrom]; omega
  | succ count ih =>
    rw [allFrom,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨first,rest⟩ i lo hi
      by_cases eq : i = start
      · simpa [eq] using first
      · exact rest i (by omega) (by omega)
    · intro h
      exact ⟨h start (by omega) (by omega),fun i lo hi => h i (by omega) (by omega)⟩

/-- State is `[accumulator, index] ++ payload`; the leaf receives `[index] ++ payload`. -/
def boundedAllStep (leaf : Code) : Code :=
  prepend (boolAnd (get 0) (leaf.comp tail))
    (prepend (succ.comp (get 1)) (drop 2))

theorem boundedAllStep_eval (leaf : Code) (payload : List Nat) (predicate : Nat → Bool)
    (leafRun : ∀ i, leaf.eval (i :: payload) = pure [(predicate i).toNat])
    (valid : Bool) (index : Nat) :
    (boundedAllStep leaf).eval (valid.toNat :: index :: payload) =
      pure ((valid && predicate index).toNat :: (index+1) :: payload) := by
  have leafCall : (leaf.comp tail).eval (valid.toNat :: index :: payload) =
      pure [(predicate index).toNat] := by simp [leafRun,Part.bind_eq_bind]
  have combined := boolAnd_eval_at (get 0) (leaf.comp tail)
    (valid.toNat :: index :: payload) valid.toNat (predicate index).toNat (by simp) leafCall
  have combined' : (boolAnd (get 0) (leaf.comp tail)).eval (valid.toNat :: index :: payload) =
      pure [(valid && predicate index).toNat] := by
    cases valid <;> cases hi : predicate index <;> simpa [hi] using combined
  simp [boundedAllStep,prepend_eval_eq,combined',Part.bind_eq_bind]

theorem boundedAllIterate_eval (leaf : Code) (payload : List Nat) (predicate : Nat → Bool)
    (leafRun : ∀ i, leaf.eval (i :: payload) = pure [(predicate i).toNat])
    (count start : Nat) (valid : Bool) :
    (flatIterate (boundedAllStep leaf)).eval (count :: valid.toNat :: start :: payload) =
      pure ((valid && allFrom predicate start count).toNat :: (start+count) :: payload) := by
  rw [flatIterate,fix_eval]
  apply Part.eq_some_iff.mpr
  induction count generalizing start valid with
  | zero =>
    apply PFun.mem_fix_iff.mpr
    left
    simp [flatCountdownBody_zero_eval,allFrom]
  | succ count ih =>
    apply PFun.mem_fix_iff.mpr
    right
    refine ⟨count :: (valid && predicate start).toNat :: (start+1) :: payload,?_,?_⟩
    · simp [flatCountdownBody,boundedAllStep_eval leaf payload predicate leafRun]
    · simpa [allFrom,Bool.and_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (start+1) (valid && predicate start)

/-- Convert `[count] ++ payload` into the initial countdown state. -/
def boundedAllInput : Code := prepend (get 0) (prepend one (zero'.comp tail))

@[simp] theorem boundedAllInput_eval (count : Nat) (payload : List Nat) :
    boundedAllInput.eval (count :: payload) = pure (count :: 1 :: 0 :: payload) := by
  simp [boundedAllInput,prepend_eval_eq,Part.bind_eq_bind]

/-- Return a Boolean singleton, preserving the leaf's input payload throughout the loop. -/
def boundedAll (leaf : Code) : Code :=
  (get 0).comp ((flatIterate (boundedAllStep leaf)).comp boundedAllInput)

theorem boundedAll_eval (leaf : Code) (payload : List Nat) (predicate : Nat → Bool)
    (leafRun : ∀ i, leaf.eval (i :: payload) = pure [(predicate i).toNat]) (count : Nat) :
    (boundedAll leaf).eval (count :: payload) = pure [(allFrom predicate 0 count).toNat] := by
  have loop := boundedAllIterate_eval leaf payload predicate leafRun count 0 true
  simp only [Bool.toNat_true,Bool.true_and,Nat.zero_add] at loop
  simp [boundedAll,loop,Part.bind_eq_bind]

end Turing.ToPartrec.Code
