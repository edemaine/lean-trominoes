/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecUnpackDigits
import LeanTrominoes.PartrecLinearAdaptersSpace

/-! # Polynomial workspace for unpacking bounded fields -/
namespace LeanTrominoes.PackedFields
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open BoundedArithmetic BoundedArithmetic.Expr

def stepCoefficient : Nat :=
  4*((var 0 / var 1).weight*((var 0 / var 1).radius+1)+
    4*(20000+4*((var 0 % var 1).weight*((var 0 % var 1).radius+1)+30000+1)+1)+1)

theorem step_fits (values : List Nat) :
    EvaluatorCodeFits stepCode values (step values) (stepCoefficient*(encodedListSpace values+1)) := by
  exact prepend_linear ((var 0 / var 1).code_fits_automatic values (by simp))
    (prepend_linear (get_linear 1 values)
      (prepend_linear ((var 0 % var 1).code_fits_automatic values (by simp)) (drop_linear 2 values)))

theorem iterate_shape (word base count : Nat) :
    ∃ w xs, w ≤ word ∧ xs.length = count ∧ (∀ a ∈ xs, a ≤ word) ∧
      (step^[count]) [word,base] = w::base::xs := by
  induction count with
  | zero => exact ⟨word,[],le_rfl,rfl,by simp,rfl⟩
  | succ n ih =>
    obtain ⟨w,xs,hw,hlen,bounded,eq⟩ := ih
    refine ⟨w/base,w%base::xs,(Nat.div_le_self _ _).trans hw,by simp [hlen],?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (Nat.mod_le _ _).trans hw
      · exact bounded a ha
    · rw [Function.iterate_succ_apply',eq]
      rfl

private theorem list_space_bound (xs : List Nat) (word : Nat) (h : ∀ a ∈ xs, a ≤ word) :
    encodedListSpace xs ≤ xs.length*((Computability.encodeNat word).length+1) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have first := listCodeEncodeNat_length_mono (h a (by simp))
    have rest := ih (fun d hd => h d (by simp [hd]))
    simp only [encodedListSpace_cons,List.length_cons]
    nlinarith

def orbitBudget (word base count : Nat) : Nat :=
  (count+2)*((Computability.encodeNat word).length+(Computability.encodeNat base).length+1)

theorem iterate_space (word base count : Nat) :
    encodedListSpace ((step^[count]) [word,base]) ≤ orbitBudget word base count := by
  obtain ⟨w,xs,hw,hlen,bounded,eq⟩ := iterate_shape word base count
  have first := listCodeEncodeNat_length_mono hw
  have rest := list_space_bound xs word bounded
  rw [eq]
  simp only [encodedListSpace_cons,orbitBudget]
  rw [hlen] at rest
  nlinarith

def unpackBudget (word base count : Nat) : Nat :=
  30000*(orbitBudget word base count+1)+
    iterationBudget (stepCoefficient*(orbitBudget word base count+1)) (Computability.encodeNat count).length

theorem unpack_fits (base : Nat) (xs : List Nat) (bounded : ∀ a ∈ xs, a < base) :
    EvaluatorCodeFits unpackCode [xs.length,pack base xs,base] xs.reverse
      (unpackBudget (pack base xs) base xs.length) := by
  let word := pack base xs
  let budget := stepCoefficient*(orbitBudget word base xs.length+1)
  have steps (taken : Nat) (h : taken ≤ xs.length) :
      EvaluatorCodeFits stepCode ((step^[taken]) [word,base])
        ((step^[taken+1]) [word,base]) budget := by
    rw [Function.iterate_succ_apply']
    apply (step_fits _).mono
    have bound := iterate_space word base taken
    have mono : orbitBudget word base taken ≤ orbitBudget word base xs.length := by
      unfold orbitBudget
      exact Nat.mul_le_mul_right _ (by omega)
    exact Nat.mul_le_mul_left _ (by omega)
  have loop := flatIterate_uniform stepCode step [word,base] xs.length budget
    (Computability.encodeNat xs.length).length le_rfl steps
  have final := iterate_pack base xs [] bounded
  change (step^[xs.length]) [word,base] = _ at final
  rw [final] at loop
  have outputSpace := iterate_space word base xs.length
  rw [final] at outputSpace
  have finish := (drop_linear 2 (0::base::(xs.reverse++[]))).mono
    (Nat.mul_le_mul_left 30000 (Nat.add_le_add_right outputSpace 1))
  simpa [word,budget,unpackCode,unpackBudget] using comp finish loop

end LeanTrominoes.PackedFields
