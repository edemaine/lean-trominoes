/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDoubleCover
import LeanTrominoes.PeriodicColoredMatching

/-! # Perfect matchings invariant under doubled lattice translations -/
namespace LeanTrominoes.TwoMatching
variable {X Y : Type*}

def PerfectMatching.transport (e : Y ≃ X) (p : PerfectMatching X) : PerfectMatching Y where
  mate y := e.symm (p.mate (e y))
  involutive y := by simp only [Equiv.apply_symm_apply,p.involutive (e y),Equiv.symm_apply_apply]
  irreflexive y := by
    intro h
    apply p.irreflexive (e y)
    simpa using congrArg e h

end LeanTrominoes.TwoMatching
namespace LeanTrominoes.PeriodicLatticeGraph
variable {V : Type*} {d : Nat}

def TwiceInvariant (color : V × Lattice d → Bool) : Prop :=
  ∀ x t, color (translate (t+t) x)=color x

def doubledColor (color : V × Lattice d → Bool) (v : V × DoubleCover.Phase d) : Bool :=
  color (DoubleCover.equivalence V d (v,0))

theorem doubledColor_eq (color : V × Lattice d → Bool) (periodic : TwiceInvariant color)
    (x : (V × DoubleCover.Phase d) × Lattice d) :
    doubledColor color x.1=color (DoubleCover.equivalence V d x) := by
  have h := periodic (DoubleCover.equivalence V d (x.1,0)) x.2
  rw [← DoubleCover.equivalence_translate] at h
  simpa only [translate,zero_add,doubledColor] using h.symm

theorem doubledColor_proper (arcs : List (Arc V d)) (color : V × Lattice d → Bool)
    (proper : ProperColoring arcs color) (periodic : TwiceInvariant color) :
    ProperColoring (DoubleCover.arcs arcs) (fun x => doubledColor color x.1) := by
  intro x y edge
  change doubledColor color x.1 ≠ doubledColor color y.1
  rw [doubledColor_eq color periodic x,doubledColor_eq color periodic y]
  exact proper _ _ ((DoubleCover.undirected_iff arcs x y).mp edge)

theorem doubleCover_perfect_iff (arcs : List (Arc V d)) :
    HasPerfectMatching (DoubleCover.arcs arcs) ↔ HasPerfectMatching arcs := by
  constructor
  · rintro ⟨p,supported⟩
    refine ⟨p.transport (DoubleCover.equivalence V d).symm,?_⟩
    intro x
    have h := (DoubleCover.undirected_iff arcs _ _).mp (supported ((DoubleCover.equivalence V d).symm x))
    simpa only [Equiv.apply_symm_apply,TwoMatching.PerfectMatching.transport,Equiv.symm_symm] using h
  · rintro ⟨p,supported⟩
    refine ⟨p.transport (DoubleCover.equivalence V d),?_⟩
    intro x
    apply (DoubleCover.undirected_iff arcs _ _).mpr
    simpa only [TwoMatching.PerfectMatching.transport,Equiv.apply_symm_apply] using supported (DoubleCover.equivalence V d x)

theorem doubleCover_inverse_translate (x : V × Lattice d) (t : Lattice d) :
    (DoubleCover.equivalence V d).symm (translate (t+t) x)=
      translate t ((DoubleCover.equivalence V d).symm x) := by
  apply (DoubleCover.equivalence V d).injective
  simp only [Equiv.apply_symm_apply,DoubleCover.equivalence_translate]

/-- A twice-invariant bipartition suffices even when the graph is disconnected. -/
theorem doubled_perfect_matching [DecidableEq V] [Fintype V] (arcs : List (Arc V d))
    (color : V × Lattice d → Bool) (proper : ProperColoring arcs color)
    (periodic : TwiceInvariant color) (perfect : HasPerfectMatching arcs) :
    ∃ p : TwoMatching.PerfectMatching (V × Lattice d),
      (∀ x, UndirectedAdj arcs x (p.mate x)) ∧
      ∀ x t, p.mate (translate (t+t) x)=translate (t+t) (p.mate x) := by
  obtain ⟨p,supported,invariant⟩ := colored_period_one (DoubleCover.arcs arcs)
    (doubledColor color) (doubledColor_proper arcs color proper periodic)
    ((doubleCover_perfect_iff arcs).mpr perfect)
  refine ⟨p.transport (DoubleCover.equivalence V d).symm,?_,?_⟩
  · intro x
    have h := (DoubleCover.undirected_iff arcs _ _).mp (supported ((DoubleCover.equivalence V d).symm x))
    simpa only [Equiv.apply_symm_apply,TwoMatching.PerfectMatching.transport,Equiv.symm_symm] using h
  · intro x t
    change DoubleCover.equivalence V d (p.mate ((DoubleCover.equivalence V d).symm (translate (t+t) x))) = _
    rw [doubleCover_inverse_translate,invariant,DoubleCover.equivalence_translate]
    rfl

end LeanTrominoes.PeriodicLatticeGraph
