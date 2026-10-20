/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMFreshMemory
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMExecutionFrame

/-! # Fresh discovery refines the correct dense alternating-path algorithm -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem fresh_preserves_layout : PreservesLayout discoverFresh := by
  constructor
  · intro slot; fin_cases slot <;> decide
  · decide

theorem invariant_paths_bound (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1))
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths) : PathsBound input paths := by
  intro l prior marked
  have bound := path_length_bound inv l prior marked
  simp only [Fintype.card_fin] at bound
  omega

theorem fresh_simulates {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B)
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths)
    (l target : Fin input.1) (r : Fin input.2.1) (prior : List (Fin input.1 × Fin input.2.1))
    (edge : (l,r)∈input.2.2) (marked : paths l=some prior) (unseen : paths target=none)
    (paired : matching.right r=some target)
    (left : d.1 Reg.left=l.val) (right : d.1 Reg.right=r.val) (mate : d.1 Reg.mate=target.val)
    (length : d.1 Reg.length=prior.length+1) :
    ∃ cost, Natural.Exec B discoverFresh d (freshState d) cost ∧ cost≤15*prior.length+15 ∧
      Representation input matching (DenseSearch.discover matching paths (l,r)) (freshState d) ∧
      NaturalData.Bounded B (freshState d) := by
  have nextInv := DenseSearch.discover_invariant (fun l r => (l,r)∈input.2.2) matching paths inv (l,r) edge
  have discovered : DenseSearch.discover matching paths (l,r)=Function.update paths target (some (prior++[(l,r)])) := by
    simp [DenseSearch.discover,marked,paired,unseen]
  have nextMarked : DenseSearch.discover matching paths (l,r) target=some (prior++[(l,r)]) := by rw [discovered]; simp
  have lengthBound := path_length_bound nextInv target (prior++[(l,r)]) nextMarked
  have countBound : prior.length+2≤ input.1 := by
    simp only [List.length_append,List.length_singleton,Fintype.card_fin] at lengthBound
    omega
  obtain ⟨cost,execution,budget⟩ := fresh_exec input matching paths d rep before room l target r left right mate length countBound
  have memory : MemoryRep input matching (DenseSearch.discover matching paths (l,r)) (freshState d).2 := by
    rw [discovered,freshState_memory input matching paths d rep l target r prior.length left right mate length]
    exact extendedPrefixMemory_spec input matching paths d.2 rep.memory (invariant_paths_bound input matching paths inv)
      l target prior marked unseen (l,r) (by omega)
  exact ⟨cost,execution,budget,rep.of_execution input matching matching paths _ d _ execution fresh_preserves_layout memory,
    execution.bounded before⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
