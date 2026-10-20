/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInitialize

/-! # Root-initialization instructions implement the logical path update -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.n Reg.m Reg.edges Reg.partnerLeft Reg.lengths Reg.index Reg.value Reg.scratch

theorem initializeState_fixed (d : Data) (i : Fin 64)
    (different : i≠Reg.index ∧ i≠Reg.value ∧ i≠Reg.scratch) : (initializeState d).1 i=d.1 i := by
  simp only [initializeState,initialize2]
  split <;> simp_all [initialize1,readState,writeState,NaturalData.set,NaturalData.store]

theorem initializeState_index (d : Data) :
    (initializeState d).1 Reg.index=d.1 Reg.index+d.1 Reg.one := by simp [initializeState,NaturalData.set]

theorem PathsBound.update_empty (input : Input) (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1))
    (bound : PathsBound input paths) (l : Fin input.1) (value : Option (List (Fin input.1 × Fin input.2.1)))
    (empty : ∀ prior, value=some prior → prior=[]) : PathsBound input (Function.update paths l value) := by
  intro a prior marked
  by_cases same : a=l
  · subst a
    have nil := empty prior (by simpa using marked)
    simp [nil]
  · exact bound a prior (by simpa [Function.update_of_ne same] using marked)

theorem initial_path_empty (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (l : Fin input.1) (prior : List (Fin input.1 × Fin input.2.1))
    (marked : DenseSearch.initial matching l=some prior) : prior=[] := by
  unfold DenseSearch.initial at marked
  split at marked <;> simp_all

theorem initializeState_memory (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (l : Fin input.1) (index : d.1 Reg.index=l.val) :
    (initializeState d).2=Function.update d.2 ((Layout.ofInput input).base Slot.lengths+l.val)
      (lengthCode (DenseSearch.initial matching l)) := by
  have leftptr := rep.pointers Slot.partnerLeft
  have lengthptr := rep.pointers Slot.lengths
  change d.1 Reg.partnerLeft=(Layout.ofInput input).base Slot.partnerLeft at leftptr
  change d.1 Reg.lengths=(Layout.ofInput input).base Slot.lengths at lengthptr
  have value := rep.memory.partnerLeft l
  cases mate : matching.left l with
  | none =>
    simp [initializeState,initialize2,initialize1,readState,writeState,NaturalData.set,NaturalData.store,
      leftptr,lengthptr,index,rep.one,rep.zero,value,mate,optionCode,lengthCode,DenseSearch.initial]
  | some r =>
    simp [initializeState,initialize2,initialize1,readState,writeState,NaturalData.set,NaturalData.store,
      leftptr,lengthptr,index,rep.one,rep.zero,value,mate,optionCode,lengthCode,DenseSearch.initial]

theorem initializeState_represents (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (bound : PathsBound input paths)
    (l : Fin input.1) (index : d.1 Reg.index=l.val) :
    Representation input matching (Function.update paths l (DenseSearch.initial matching l)) (initializeState d) := by
  have ptr : (Layout.ofInput input).Pointers (initializeState d) := by
    intro slot
    rw [initializeState_fixed d (pointer slot) (by simp [pointer,Fin.ext_iff]; have := slot.isLt; omega)]
    exact rep.pointers slot
  refine ⟨ptr,?_,?_,?_,?_,?_,?_⟩
  · rw [initializeState_fixed d Reg.n (by decide),rep.n]
  · rw [initializeState_fixed d Reg.m (by decide),rep.m]
  · rw [initializeState_fixed d Reg.edges (by decide),rep.edges]
  · rw [initializeState_fixed d Reg.one (by decide),rep.one]
  · rw [initializeState_fixed d Reg.zero (by decide),rep.zero]
  · rw [initializeState_memory input matching paths d rep l index]
    exact rep.memory.emptyPath input matching paths d.2 bound l (DenseSearch.initial matching l)
      (initial_path_empty input matching l)

end LeanTrominoes.BipartiteMatching.DenseWordRAM
