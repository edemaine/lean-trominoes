/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreeAtomCompiler

/-! # Correctness of compiled exact-one atom columns -/
namespace LeanTrominoes.PeriodicOneInThree.AtomDescriptors

private theorem sentinel (original : List Nat) (n : Nat) :
    (original ++ [0]).getD n 0 = original.getD n 0 := by
  induction original generalizing n with
  | nil => cases n <;> simp
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

private theorem columns_evaluate (original : List Nat) (clause occurrence : Nat)
    (ds : List Descriptor) :
    AlignedUnaryBooleanChoice.pointwiseSelected (controls ds)
      ((PrefixSums.startsAux occurrence (ds.map originalStep)).map (fun n => 2*original.getD n 0))
      (AlignedUnaryListClosure.added
        ((PrefixSums.startsAux clause (ds.map clauseStep)).map (fun n => n*28))
        (ds.map auxiliaryOffset)) = evaluate original clause occurrence ds := by
  induction ds generalizing clause occurrence with
  | nil => rfl
  | cons d ds ih =>
    rcases d with ⟨k,last⟩
    cases k <;>
      simp [controls,AlignedUnaryBooleanChoice.pointwiseSelected,
        AlignedUnaryListClosure.added,UnaryAlignedAddMachine.sums,evaluate,auxiliaryOffset,
        ← ih,controls,Nat.mul_comm,Nat.add_assoc]

theorem output_eq_evaluate (ds : List Descriptor) (original : List Nat)
    (enough : (ds.map originalStep).sum ≤ original.length) :
    output ds original = evaluate original 0 0 ds := by
  have valid : ∀ q ∈ queries ds, q < (original ++ [0]).length := by
    intro q hq
    have h := prefix_le_sum 0 (ds.map originalStep) q hq
    simp only [List.length_append,List.length_cons,List.length_nil] at *
    omega
  have inheritedEq : inherited ds original =
      (queries ds).map (fun n => 2*original.getD n 0) := by
    unfold inherited UnaryFieldConstantScale.values
    rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ valid,List.map_map]
    simp only [Function.comp_def,sentinel,Nat.mul_comm]
  unfold output
  rw [AlignedUnaryBooleanChoice.selectedValues_eq_pointwiseSelected _ _ _
    (by simp [controls]) (by simp),inheritedEq]
  exact columns_evaluate original 0 0 ds

end LeanTrominoes.PeriodicOneInThree.AtomDescriptors
