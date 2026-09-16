/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletionUnion
import LeanTrominoes.TrominoCompletionTranslation

/-! # Adding and removing a fully prescribed surrounding region -/
namespace LeanTrominoes.Tromino

theorem IsFootprint.nonempty {t : Tromino} {f : Finset Cell} (h : t.IsFootprint f) : f.Nonempty := by
  obtain ⟨p,rfl⟩ := h
  apply Finset.Nonempty.image
  exact ⟨(0,0),by change (0,0) ∈ t.cells; cases t <;> decide⟩

theorem occupied_translate (p : Set (Finset Cell)) (v : Cell) :
    occupied ((fun f => f.image (Cell.add v)) '' p) = Cell.add v '' occupied p := by
  ext c
  constructor
  · rintro ⟨_,⟨f,hf,rfl⟩,hc⟩
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨d,⟨f,hf,hd⟩,rfl⟩
  · rintro ⟨d,⟨f,hf,hd⟩,rfl⟩
    exact ⟨f.image (Cell.add v),⟨f,hf,rfl⟩,Finset.mem_image.mpr ⟨d,hd,rfl⟩⟩

theorem occupied_union (p q : Set (Finset Cell)) : occupied (p ∪ q) = occupied p ∪ occupied q := by
  ext c
  simp only [occupied,Set.mem_setOf_eq,Set.mem_union]
  aesop

/-- A completely prefilled collar can be removed without changing completion
of the interior, provided interior preplacements stay in the interior. -/
theorem completable_attach_filled_iff {t : Tromino} {a b : Set Cell} {p q : Set (Finset Cell)}
    (shell : t.Completable b q) (filled : occupied q = b) (apart : Disjoint a b)
    (inside : ∀ f ∈ p, ∀ c ∈ f, c ∈ a) :
    t.Completable (a ∪ b) (p ∪ q) ↔ t.Completable a p := by
  constructor
  · rintro ⟨tiles,tiled,retained⟩
    have sub : q ⊆ tiles := fun f hf => retained (Or.inr hf)
    have removed := tiled.remove sub
    have region : (a ∪ b) \ occupied q = a := by
      rw [filled]
      ext c
      have disjoint := Set.disjoint_left.mp apart
      simp only [Set.mem_sdiff,Set.mem_union]
      constructor
      · rintro ⟨ha | hb,hout⟩
        · exact ha
        · exact False.elim (hout hb)
      · intro ha
        exact ⟨Or.inl ha,fun hb => disjoint ha hb⟩
    rw [region] at removed
    refine ⟨tiles \ q,removed,?_⟩
    intro f hf
    have member := retained (Or.inl hf)
    refine ⟨member,?_⟩
    intro shellMember
    obtain ⟨c,hc⟩ := (tiled.tilesInside f member).1.nonempty
    have outside : c ∈ b := filled ▸ (show c ∈ occupied q from ⟨f,shellMember,hc⟩)
    exact Set.disjoint_left.mp apart (inside f hf c hc) outside
  · intro core
    exact core.union shell apart

end LeanTrominoes.Tromino
