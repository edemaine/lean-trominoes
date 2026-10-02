/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGeneralAugmentingPath
import LeanTrominoes.PeriodicMatchingSolver

/-! # Periodic matchings with a translation-invariant two-coloring

Use two copies of the same finite vertex index type in the bipartite solver.
A returned bijection sends each black vertex to a white vertex. Taking this
bijection on black vertices and its inverse on white vertices gives the
required undirected perfect matching without reindexing the color classes.
-/
namespace LeanTrominoes.TwoMatching
variable {X : Type*}

def PerfectMatching.equivalence (p : PerfectMatching X) : X ≃ X where
  toFun := p.mate
  invFun := p.mate
  left_inv := p.involutive
  right_inv := p.involutive

def coloredMate (f : X ≃ X) (color : X → Bool) (x : X) : X :=
  if color x=false then f x else f.symm x

def coloredMatching (f : X ≃ X) (color : X → Bool)
    (proper : ∀ x, color x ≠ color (f x)) : PerfectMatching X where
  mate := coloredMate f color
  involutive := by
    intro x
    have backward := proper (f.symm x)
    simp only [Equiv.apply_symm_apply] at backward
    by_cases h : color x=false
    · have next : color (f x)≠false := by simpa only [h] using (proper x).symm
      simp [coloredMate,h,next]
    · have previous : color (f.symm x)=false := by
        cases hx : color x <;> cases hi : color (f.symm x) <;> simp_all
      simp [coloredMate,h,previous]
  irreflexive := by
    intro x equal
    unfold coloredMate at equal
    split_ifs at equal with h
    · exact proper x (congrArg color equal).symm
    · have same : f x=x := by simpa using (congrArg f equal).symm
      exact proper x (congrArg color same).symm

end LeanTrominoes.TwoMatching
namespace LeanTrominoes.PeriodicLatticeGraph
variable {V : Type*} {d : Nat}

def symmetricEdges (arcs : List (Arc V d)) : List (PeriodicBipartite.Edge V V d) :=
  arcs.flatMap fun e => [⟨e.source,e.target,e.offset⟩,⟨e.target,e.source,-e.offset⟩]

theorem symmetricEdges_length (arcs : List (Arc V d)) : (symmetricEdges arcs).length=2*arcs.length := by
  induction arcs <;> simp_all [symmetricEdges] <;> omega

theorem symmetricEdges_adj (arcs : List (Arc V d)) (x y : V × Lattice d) :
    PeriodicBipartite.Adj (symmetricEdges arcs) x y ↔ UndirectedAdj arcs x y := by
  constructor
  · rintro ⟨a,ha,source,target,offset⟩
    obtain ⟨e,he,ha⟩ := List.mem_flatMap.mp ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inl ⟨e,he,source,target,offset⟩
    · have eq := List.mem_singleton.mp ha
      subst a
      exact Or.inr ⟨e,he,target,source,by change y.2=x.2+-e.offset at offset; rw [offset]; abel⟩
  · rintro (⟨e,he,source,target,offset⟩ | ⟨e,he,target,source,offset⟩)
    · exact ⟨⟨e.source,e.target,e.offset⟩,List.mem_flatMap.mpr ⟨e,he,by simp⟩,source,target,offset⟩
    · exact ⟨⟨e.target,e.source,-e.offset⟩,List.mem_flatMap.mpr ⟨e,he,by simp⟩,
        source,target,by rw [offset]; simp⟩

theorem symmetricEdges_perfect (arcs : List (Arc V d)) (color : V → Bool)
    (proper : ProperColoring arcs (fun x => color x.1)) :
    PeriodicBipartite.HasPerfectMatching (symmetricEdges arcs) ↔ HasPerfectMatching arcs := by
  constructor
  · rintro ⟨f,supported⟩
    have support x := (symmetricEdges_adj arcs x (f x)).mp (supported x)
    refine ⟨TwoMatching.coloredMatching f (fun x => color x.1) (fun x => proper x (f x) (support x)),?_⟩
    intro x
    change UndirectedAdj arcs x (TwoMatching.coloredMate f (fun x => color x.1) x)
    unfold TwoMatching.coloredMate
    split_ifs
    · exact support x
    · have back := support (f.symm x)
      simp only [Equiv.apply_symm_apply] at back
      exact back.symm
  · rintro ⟨p,supported⟩
    exact ⟨p.equivalence,fun x => (symmetricEdges_adj arcs x (p.mate x)).mpr (supported x)⟩

theorem inverse_translation (f : (V × Lattice d) ≃ (V × Lattice d))
    (periodic : PeriodicBipartite.TranslationInvariant f) :
    PeriodicBipartite.TranslationInvariant f.symm := by
  intro v z t
  apply f.injective
  rw [Equiv.apply_symm_apply]
  have h := periodic (f.symm (v,z)).1 (f.symm (v,z)).2 t
  simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using h.symm

/-- The matching periodization theorem without connectedness or locality assumptions. -/
theorem colored_period_one [DecidableEq V] [Fintype V] (arcs : List (Arc V d))
    (color : V → Bool) (proper : ProperColoring arcs (fun x => color x.1))
    (perfect : HasPerfectMatching arcs) :
    ∃ p : TwoMatching.PerfectMatching (V × Lattice d),
      (∀ x, UndirectedAdj arcs x (p.mate x)) ∧
      ∀ x t, p.mate (translate t x)=translate t (p.mate x) := by
  obtain ⟨f,supported,periodic⟩ := PeriodicBipartite.exists_period_one (symmetricEdges arcs)
    ((symmetricEdges_perfect arcs color proper).mpr perfect)
  have support x := (symmetricEdges_adj arcs x (f x)).mp (supported x)
  let p := TwoMatching.coloredMatching f (fun x => color x.1) (fun x => proper x (f x) (support x))
  refine ⟨p,?_,?_⟩
  · intro x
    change UndirectedAdj arcs x (TwoMatching.coloredMate f (fun x => color x.1) x)
    unfold TwoMatching.coloredMate
    split_ifs
    · exact support x
    · have back := support (f.symm x)
      simp only [Equiv.apply_symm_apply] at back
      exact back.symm
  · intro x t
    change TwoMatching.coloredMate f (fun x => color x.1) (translate t x)=
      translate t (TwoMatching.coloredMate f (fun x => color x.1) x)
    unfold TwoMatching.coloredMate translate
    dsimp only
    split_ifs
    · exact periodic x.1 x.2 t
    · exact inverse_translation f periodic x.1 x.2 t

end LeanTrominoes.PeriodicLatticeGraph
