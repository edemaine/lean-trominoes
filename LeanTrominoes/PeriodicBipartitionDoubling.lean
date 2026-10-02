/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicLatticeGraph

/-! # Lemma 4.4: the bipartition of a connected periodic graph is 2-periodic -/
namespace LeanTrominoes.PeriodicLatticeGraph
variable {V : Type*} {d : Nat}
set_option maxRecDepth 4096

private theorem bool_step {a b c e : Bool} (one : a ≠ b) (two : c ≠ e) (same : a=c) : b=e := by
  exact (by decide +kernel : ∀ a b c e : Bool, a ≠ b → c ≠ e → a=c → b=e) a b c e one two same

/-- Two proper two-colorings agreeing at one vertex agree throughout its component. -/
theorem coloring_unique (arcs : List (Arc V d)) (color other : V × Lattice d → Bool)
    (proper : ProperColoring arcs color) (otherProper : ProperColoring arcs other)
    (u v : V × Lattice d) (path : Relation.ReflTransGen (UndirectedAdj arcs) u v)
    (same : color u=other u) : color v=other v := by
  induction path with
  | refl => exact same
  | @tail w v path edge ih => exact bool_step (proper w v edge) (otherProper w v edge) ih

/-- Every doubled lattice translation preserves the given bipartition. -/
theorem bipartition_two_periodic (arcs : List (Arc V d)) (connected : Connected arcs)
    (color : V × Lattice d → Bool) (proper : ProperColoring arcs color)
    (v : V) (z t : Lattice d) : color (v,z+(t+t))=color (v,z) := by
  let u : V × Lattice d := (v,z)
  let shifted := fun w => color (translate t w)
  have shiftedProper : ProperColoring arcs shifted := fun a b edge =>
    proper _ _ (undirected_translate arcs a b t edge)
  by_cases same : color u=shifted u
  · have all (w) := coloring_unique arcs color shifted proper shiftedProper u w (connected u w) same
    have first := all u
    have second := all (translate t u)
    change color (v,z+t)=color (v,(z+t)+t) at second
    change color (v,z)=color (v,z+t) at first
    simpa [add_assoc] using second.symm.trans first.symm
  · let flipped := fun w => !(shifted w)
    have flippedProper : ProperColoring arcs flipped := by
      intro a b edge
      have ne := shiftedProper a b edge
      intro equal
      apply ne
      simpa only [flipped,Bool.not_not] using congrArg Bool.not equal
    have equal : color u=flipped u := by
      exact Bool.eq_not_iff.mpr same
    have all (w) := coloring_unique arcs color flipped proper flippedProper u w (connected u w) equal
    have second := all (translate t u)
    have first := all u
    change color (v,z)=!color (v,z+t) at first
    change color (v,z+t)=!color (v,(z+t)+t) at second
    rw [second] at first
    simpa [add_assoc] using first.symm

end LeanTrominoes.PeriodicLatticeGraph
