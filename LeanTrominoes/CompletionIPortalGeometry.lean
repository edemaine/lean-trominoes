/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionITileOwnership

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

/-- The two connector cells at the top of a microcell. -/
def portalCell (i : Cell) (right : Bool) : Cell :=
  (18 * i.1 + if right then 14 else 5,27 * i.2)

def aboveMicro (i : Cell) : Cell := (i.1,i.2 - 1)

theorem portal_membership (i j : Cell) (right : Bool) :
    portalCell i right ∈ microRegion j ↔ j = i ∨ j = aboveMicro i := by
  rw [mem_microRegion]
  cases right <;> simp only [portalCell,Bool.false_eq_true,ite_false,ite_true,
    aboveMicro,Prod.ext_iff] <;> unfold MemberAt <;> omega

/-- Any subbrick containing a connector pixel owns one of its two adjacent microcells. -/
theorem portal_group_membership (s : Finset Cell) (i : Cell) (right : Bool) :
    portalCell i right ∈ groupRegion s ↔ i ∈ s ∨ aboveMicro i ∈ s := by
  constructor
  · intro hc
    obtain ⟨j,hj,hjc⟩ := Finset.mem_biUnion.mp hc
    rcases (portal_membership i j right).mp hjc with rfl | rfl
    · exact Or.inl hj
    · exact Or.inr hj
  · intro hc
    rcases hc with hi | hi
    · exact Finset.mem_biUnion.mpr ⟨i,hi,(portal_membership i i right).mpr (Or.inl rfl)⟩
    · exact Finset.mem_biUnion.mpr
        ⟨aboveMicro i,hi,(portal_membership i _ right).mpr (Or.inr rfl)⟩

/-- The only possible owners of either connector pixel are the subbricks
owning the microcells immediately above and below it. -/
theorem portal_region_owners (palette : Cell → Fin 24) (i : Cell) (right : Bool)
    {below above other : Cell} {a b e : Atom × Cell}
    (ha : a ∈ layout (palette below)) (hb : b ∈ layout (palette above))
    (he : e ∈ layout (palette other))
    (ownBelow : i ∈ groupAt below a) (ownAbove : aboveMicro i ∈ groupAt above b)
    (contains : portalCell i right ∈ e.1.pattern.region.image (Cell.add (atomOffset other e))) :
    (other = below ∧ e = a) ∨ (other = above ∧ e = b) := by
  change portalCell i right ∈ e.1.pattern.region.image (Cell.add (Cell.add (origin other) e.2)) at contains
  rw [← group_at_region palette other he,portal_group_membership] at contains
  rcases contains with own | own
  · have eq := group_locations_eq palette he ha own ownBelow
    subst other
    exact Or.inl ⟨rfl,group_entries_eq palette below he ha own ownBelow⟩
  · have eq := group_locations_eq palette he hb own ownAbove
    subst other
    exact Or.inr ⟨rfl,group_entries_eq palette above he hb own ownAbove⟩

end LeanTrominoes.CompletionPattern.IBricks
