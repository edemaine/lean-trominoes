/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMLinkedIndex

/-! # Correctness of the executed Horn indexing loop

The invariant here belongs to the states reached by the actual bytecode
certificate, rather than to a separately assumed index-building algorithm.
-/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.index Reg.one Reg.occurrences

def indexState (input : Input) (k : ℕ) : Data :=
  (index10^[k]) ((preparedInput input).set Reg.index 0)

theorem indexState_zero (input : Input) :
    indexState input 0=(preparedInput input).set Reg.index 0 := rfl

theorem indexState_succ (input : Input) (k : ℕ) :
    indexState input (k+1)=index10 (indexState input k) :=
  Function.iterate_succ_apply' _ _ _

theorem indexState_control (input : Input) (k : ℕ) :
    (indexState input k).1 Reg.index=k ∧ (indexState input k).1 Reg.one=1 ∧
      (indexState input k).1 Reg.occurrences=(Indexed.edges input.2).length := by
  induction k with
  | zero =>
    have before := prepared5_controls (initialData input) (words input).length input.1
      input.2.rules.size (Indexed.edges input.2).length
    simpa [indexState,NaturalData.set,preparedInput] using And.intro (rfl : (0 : ℕ)=0) before
  | succ k ih =>
    rw [indexState_succ]
    have step := index10_control (indexState input k)
    exact ⟨by omega,by omega,by omega⟩

/-- All eight arrays have their claimed contents at every reached iteration.
In particular, each bucket is the reversed-prefix native worklist bucket,
and its links only dereference allocated occurrence cells. -/
theorem indexState_invariant (input : Input) (k : ℕ) (within : k≤(Indexed.edges input.2).length) :
    ∃ contents : Tables,
      (Layout.ofInput input).Realizes (indexState input k).2 contents ∧
      (Layout.ofInput input).Pointers (indexState input k) ∧ IndexTables input k contents := by
  induction k with
  | zero =>
    refine ⟨initialContents input,preparedInput_realizes input,?_,initialContents_indexTables input⟩
    exact (Layout.ofInput input).set_pointers _ (preparedInput_pointers input) Reg.index
      (scalarRegister_of_large _ (by decide)) 0
  | succ k ih =>
    obtain ⟨contents,realizes,pointers,tables⟩ := ih (by omega)
    have eventBound : k<(Indexed.edges input.2).length := by omega
    let occurrence := (Indexed.edges input.2)[k]
    have atoms : contents Slot.edgeAtoms k=atomCode occurrence.1 := by
      rw [tables.untouched Slot.edgeAtoms (by decide) (by decide) (by decide)]
      exact initialContents_edgeAtom input k eventBound
    have rules : contents Slot.edgeRules k=occurrence.2.val := by
      rw [tables.untouched Slot.edgeRules (by decide) (by decide) (by decide)]
      exact initialContents_edgeRule input k eventBound
    have control := indexState_control input k
    refine ⟨indexedContents contents k (atomCode occurrence.1) occurrence.2.val,?_,?_,?_⟩
    · rw [indexState_succ]
      exact index10_realizes (Layout.ofInput input) (indexState input k) contents realizes pointers
        k (atomCode occurrence.1) occurrence.2.val control.1 control.2.1 eventBound
        (by have := atomCode_le occurrence.1; dsimp [Layout.ofInput]; omega) occurrence.2.isLt atoms rules
    · rw [indexState_succ]
      exact index10_pointers _ _ pointers
    · exact tables.step input k contents eventBound

/-- Endpoint of the already compiled prefix: counters and bucket chains
represent the complete occurrence stream, with duplicate premises retained. -/
theorem indexedInput_invariant (input : Input) :
    ∃ contents : Tables,
      (Layout.ofInput input).Realizes (indexedInput input).2 contents ∧
      (Layout.ofInput input).Pointers (indexedInput input) ∧
      IndexTables input (Indexed.edges input.2).length contents :=
  indexState_invariant input _ (by omega)

theorem semanticIndex_complete (input : Input) :
    semanticIndex input (Indexed.edges input.2).length=Worklist.index (Indexed.edges input.2).reverse := by
  simp [semanticIndex]

end LeanTrominoes.Horn.WordRAM
