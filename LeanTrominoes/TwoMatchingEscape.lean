/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoMatchingTrace

/-! # A finite box must contain an augmenting path or many boundary edges -/
namespace LeanTrominoes.TwoMatching
variable {X : Type*} [DecidableEq X]
variable (m : PartialMatching X) (p : PerfectMatching X)

/-- A trace and its final perfect edge lie entirely in the finite region. -/
def Terminal (s f : Finset X) : Prop :=
  ∃ r ∈ f, ∃ x, ∃ t : Trace m p r x,
    (∀ a ∈ t.vertices, a ∈ s) ∧ p.mate x ∈ s ∧ m.mate (p.mate x) = none

noncomputable def reachable (s f : Finset X) : Finset X := by
  classical
  exact s.filter fun x => ∃ r ∈ f, ∃ t : Trace m p r x,
    ∀ a ∈ t.vertices, a ∈ s

def Exits (s : Finset X) (x : X) : Prop :=
  p.mate x ∉ s ∨ ∃ y, m.mate (p.mate x) = some y ∧ y ∉ s

/-- Boundary edges are oriented from the region to its complement. Each
reachable trace consumes a different such edge if no trace can finish inside. -/
theorem roots_le_boundary (s f : Finset X) (boundary : Finset (X × X))
    (contained : f ⊆ s) (free : ∀ r ∈ f, m.mate r = none)
    (perfect_boundary : ∀ x ∈ s, p.mate x ∉ s → (x,p.mate x) ∈ boundary)
    (partial_boundary : ∀ x ∈ s, ∀ y, m.mate x = some y → y ∉ s → (x,y) ∈ boundary)
    (no_terminal : ¬ Terminal m p s f) : f.card ≤ boundary.card := by
  classical
  let a := reachable m p s f
  have a_mem (x : X) : x ∈ a ↔ x ∈ s ∧ ∃ r ∈ f, ∃ t : Trace m p r x,
      ∀ v ∈ t.vertices, v ∈ s := by simp [a,reachable]
  have f_sub : f ⊆ a := by
    intro r hr
    apply (a_mem r).mpr
    refine ⟨contained hr,r,hr,Trace.start,?_⟩
    intro v hv
    simp only [Trace.vertices,List.mem_singleton] at hv
    exact hv ▸ contained hr
  let exits := a.filter (Exits m p s)
  let stay := a.filter fun x => ¬ Exits m p s x
  have successor (x : X) (hx : x ∈ stay) :
      ∃ y ∈ a \ f, m.mate (p.mate x) = some y := by
    have ha := (Finset.mem_filter.mp hx).1
    have he := (Finset.mem_filter.mp hx).2
    have pin : p.mate x ∈ s := by
      by_contra hn; exact he (Or.inl hn)
    obtain ⟨xs,r,rf,t,inside⟩ := (a_mem x).mp ha
    cases hm : m.mate (p.mate x) with
    | none => exact (no_terminal ⟨r,rf,x,t,inside,pin,hm⟩).elim
    | some y =>
      have yin : y ∈ s := by
        by_contra hn; exact he (Or.inr ⟨y,hm,hn⟩)
      have ya : y ∈ a := by
        apply (a_mem y).mpr
        refine ⟨yin,r,rf,Trace.step t y hm,?_⟩
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact inside v hv
        · simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
          rcases hv with rfl | rfl
          · exact pin
          · exact yin
      have nf : y ∉ f := by
        intro yf
        have rev := m.symmetric _ _ hm
        rw [free y yf] at rev
        contradiction
      exact ⟨y,Finset.mem_sdiff.mpr ⟨ya,nf⟩,rfl⟩
  choose next next_mem next_pair using successor
  have stay_bound : stay.card ≤ (a \ f).card := by
    let forward : {x // x ∈ stay} → {y // y ∈ a \ f} :=
      fun x => ⟨next x x.property,next_mem x x.property⟩
    have inj : Function.Injective forward := by
      intro x y eq
      have equal : next x x.property = next y y.property := congrArg Subtype.val eq
      have one := m.symmetric _ _ (next_pair x x.property)
      have two := m.symmetric _ _ (next_pair y y.property)
      rw [equal] at one
      apply Subtype.ext
      exact p.involutive.injective (Option.some.inj (one.symm.trans two))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective forward inj
  have split : exits.card + stay.card = a.card :=
    Finset.card_filter_add_card_filter_not (s := a) (Exits m p s)
  have removed := Finset.card_sdiff_add_card_eq_card f_sub
  have roots_bound : f.card ≤ exits.card := by omega
  have exit_edge (x : X) (hx : x ∈ exits) :
      ∃ e ∈ boundary, (e = (x,p.mate x) ∧ p.mate x ∉ s) ∨
        (e.1 = p.mate x ∧ e.1 ∈ s ∧ m.mate e.1 = some e.2 ∧ e.2 ∉ s) := by
    have xs := ((a_mem x).mp (Finset.mem_filter.mp hx).1).1
    rcases (Finset.mem_filter.mp hx).2 with out | ⟨y,paired,out⟩
    · exact ⟨(x,p.mate x),perfect_boundary x xs out,Or.inl ⟨rfl,out⟩⟩
    · by_cases pin : p.mate x ∈ s
      · exact ⟨(p.mate x,y),partial_boundary _ pin _ paired out,
          Or.inr ⟨rfl,pin,paired,out⟩⟩
      · exact ⟨(x,p.mate x),perfect_boundary x xs pin,Or.inl ⟨rfl,pin⟩⟩
  choose edge edge_mem edge_spec using exit_edge
  have exit_bound : exits.card ≤ boundary.card := by
    let forward : {x // x ∈ exits} → {e // e ∈ boundary} :=
      fun x => ⟨edge x x.property,edge_mem x x.property⟩
    have inj : Function.Injective forward := by
      intro x y eq
      have equal : edge x x.property = edge y y.property := congrArg Subtype.val eq
      have xs := ((a_mem x).mp (Finset.mem_filter.mp x.property).1).1
      have ys := ((a_mem y).mp (Finset.mem_filter.mp y.property).1).1
      rcases edge_spec x x.property with ⟨ex,outx⟩ | ⟨ex,inx,mx,outx⟩ <;>
        rcases edge_spec y y.property with ⟨ey,outy⟩ | ⟨ey,iny,my,outy⟩
      · rw [ex,ey] at equal; exact Subtype.ext (congrArg Prod.fst equal)
      · have one : x = p.mate y := by
          have := congrArg Prod.fst equal; simpa only [ex,ey] using this
        have p_y : p.mate x = y := by rw [one,p.involutive]
        exact (outx (p_y ▸ ys)).elim
      · have one : y = p.mate x := by
          have := congrArg Prod.fst equal; simpa only [ex,ey] using this.symm
        have p_x : p.mate y = x := by rw [one,p.involutive]
        exact (outy (p_x ▸ xs)).elim
      · have same : p.mate x = p.mate y := ex.symm.trans ((congrArg Prod.fst equal).trans ey)
        exact Subtype.ext (p.involutive.injective same)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective forward inj
  exact roots_bound.trans exit_bound

end LeanTrominoes.TwoMatching
