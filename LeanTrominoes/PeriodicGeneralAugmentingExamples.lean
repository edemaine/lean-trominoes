/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGeneralAugmentingPath

/-! # Regression: a nonbipartite graph in dimension zero -/
noncomputable section
namespace LeanTrominoes.PeriodicLatticeGraph.GeneralExamples
open TwoMatching
abbrev Vertex := Bool × Bool

def arcs : List (Arc Vertex 0) :=
  ((Finset.univ : Finset (Vertex × Vertex)).filter (fun e => e.1 ≠ e.2)).toList.map fun e => ⟨e.1,e.2,0⟩

theorem adjacency (x y : Vertex × Lattice 0) (different : x.1 ≠ y.1) : UndirectedAdj arcs x y := by
  apply Or.inl
  refine ⟨⟨x.1,y.1,0⟩,?_,rfl,rfl,?_⟩
  · exact List.mem_map.mpr ⟨(x.1,y.1),Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,different⟩),rfl⟩
  · funext i; exact Fin.elim0 i

def perfect : PerfectMatching (Vertex × Lattice 0) where
  mate x := ((!x.1.1,x.1.2),x.2)
  involutive := by intro x; simp
  irreflexive := by
    intro x eq
    have same := congrArg (fun a => a.1.1) eq
    cases x.1.1 <;> simp at same

def empty : PeriodOneMatching arcs where
  mate _ := none
  symmetric := by intros; contradiction
  irreflexive := by simp
  supported := by intros; contradiction
  periodic := by simp

theorem not_bipartite : ¬ ∃ color : Vertex × Lattice 0 → Bool, ProperColoring arcs color := by
  rintro ⟨color,h⟩
  have one := h ((false,false),0) ((false,true),0) (adjacency _ _ (by decide))
  have two := h ((false,true),0) ((true,false),0) (adjacency _ _ (by decide))
  have three := h ((false,false),0) ((true,false),0) (adjacency _ _ (by decide))
  have pigeonhole (a b c : Bool) (ab : a ≠ b) (bc : b ≠ c) : a=c := by
    cases a <;> cases b <;> cases c <;> simp_all
  exact three (pigeonhole _ _ _ one two)

/-- Dimension zero and the general, nonbipartite API both remain supported. -/
theorem augmenting_from_every_vertex (root : Vertex × Lattice 0) :
    ∃ path : AugmentingPath empty.toPartialMatching (UndirectedAdj arcs) root,
      DiameterAtMost path.vertices 0 := by
  have locality : Local arcs := by intro e he i; exact Fin.elim0 i
  have supported : ∀ x, UndirectedAdj arcs x (perfect.mate x) := by
    intro x; apply adjacency
    intro equal
    have same := congrArg Prod.fst equal
    cases x.1.1 <;> simp [perfect] at same
  simpa using bounded_augmenting_path arcs locality ⟨perfect,supported⟩ empty root rfl

end LeanTrominoes.PeriodicLatticeGraph.GeneralExamples
