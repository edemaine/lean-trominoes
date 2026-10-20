/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRawInput

/-! # Private Cramer pointers survive original-input loading -/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

private theorem embedded_preserves {r s : ℕ} (code : Structured.Code r) (i : Fin (r+s)) (high : r≤ i.val) :
    (code.embed s).PreservesRegister i := by
  have ne (j : Fin r) : i≠j.castAdd s := by
    intro equal
    have same := congrArg Fin.val equal
    have := j.isLt
    simp only [Fin.val_castAdd] at same
    omega
  induction code with
  | atom op => cases op <;> simp [Structured.Code.embed,Structured.Primitive.embed,
      Structured.Code.PreservesRegister,Structured.Primitive.PreservesRegister,ne]
  | seq a b ha hb => exact ⟨ha,hb⟩
  | branch c a b ha hb => exact ⟨ha,hb⟩
  | loop c a ha => exact ha

private theorem assignments_preserves {r : ℕ} (finish anchor : Fin r) (moves : List (Fin r × Fin r))
    (i : Fin r) (finish_ne : i≠finish) (destinations : ∀ p∈moves, i≠p.1) :
    (Assignments.code finish anchor moves).PreservesRegister i := by
  induction moves with
  | nil => exact finish_ne
  | cons p rest ih =>
    exact ⟨destinations p List.mem_cons_self,ih (fun p hp => destinations p (List.mem_cons_of_mem _ hp))⟩

private theorem block_preserves (first target : ℕ) (i : Fin 64) (high : 16≤ i.val) :
    (BlockCopy.program first target).PreservesRegister i := by
  have ne (j : Fin 16) : i≠BlockCopy.low j := by
    intro equal
    have same := congrArg Fin.val equal
    have := j.isLt
    simp only [BlockCopy.low,Fin.val_castAdd] at same
    omega
  change _ ∧ _
  refine ⟨?_,embedded_preserves (r:=16) (s:=48) copyProgram i high⟩
  simp [BlockCopy.setup,BlockCopy.pointerProgram,Structured.Code.PreservesRegister,
    Structured.Primitive.PreservesRegister,ne]

private theorem batch_preserves (count first target : ℕ) (i : Fin 64) (high : 16≤ i.val) (low : i.val<56) :
    (BatchCopy.program count first target).PreservesRegister i := by
  induction count generalizing first target with
  | zero =>
    change i≠BlockCopy.lengthRegister
    intro equal
    have same := congrArg Fin.val equal
    change i.val=56 at same
    omega
  | succ count ih => exact ⟨block_preserves first target i high,ih (first+1) (target+1)⟩

private theorem source_preserves (source : Fin 64) (count target : ℕ) (i : Fin 64)
    (high : 16≤ i.val) (low : i.val<56) :
    (SourceBlocks.program source count target).PreservesRegister i := by
  change _ ∧ _
  refine ⟨?_,batch_preserves _ _ _ _ high low⟩
  apply assignments_preserves
  · intro equal
    have same := congrArg Fin.val equal
    change i.val=1 at same
    omega
  · intro p hp
    simp only [SourceBlocks.moves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals intro equal; have same := congrArg Fin.val equal; norm_num [BlockCopy.lengthRegister,BlockCopy.sourceRegister,BlockCopy.targetRegister] at same; omega

theorem SourceLoad.preservesHeaders (d : ℕ) : Numerator.PreservesHeaders (SourceLoad.completeProgram d) := by
  intro i high low
  have h : 16≤ i.val := by omega
  have l : i.val<56 := by omega
  change (_ ∧ _ ∧ _) ∧ _
  refine ⟨⟨source_preserves _ _ _ _ h l,source_preserves _ _ _ _ h l,source_preserves _ _ _ _ h l⟩,?_⟩
  change i≠BlockCopy.low Reg.length ∧ i≠Circuit.baseRegister.castAdd 47
  constructor
  all_goals intro equal; have same := congrArg Fin.val equal; norm_num [BlockCopy.low,Reg.length,Circuit.baseRegister] at same; omega

end LeanTrominoes.Domino.WordRAM.Binary
