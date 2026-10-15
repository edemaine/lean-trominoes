/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.Tiling.Basic.ExactCover
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite.Basic

/-! # Exact covers after identifying equivalent pieces -/

namespace LeanTrominoes.ExactCover

variable {Piece Image CellType : Type*}
  [DecidableEq Piece] [DecidableEq Image] [DecidableEq CellType]

omit [DecidableEq Piece] in
theorem IsExactCover.image {f : Piece → Image}
    {footprint : Image → Finset CellType} {target : Finset CellType}
    {selection : Finset Piece}
    (cover : IsExactCover (fun piece => footprint (f piece)) target selection) :
    IsExactCover footprint target (selection.image f) := by
  constructor
  · intro image member
    obtain ⟨piece, pieceMember, rfl⟩ := Finset.mem_image.mp member
    exact cover.nonempty piece pieceMember
  · rw [Finset.image_biUnion]
    exact cover.union_eq
  · intro first firstMember second secondMember distinct
    obtain ⟨left, leftMember, rfl⟩ := Finset.mem_image.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := Finset.mem_image.mp secondMember
    exact cover.pairwiseDisjoint leftMember rightMember
      (fun equality => distinct (congrArg f equality))

omit [DecidableEq Piece] in
theorem IsExactCover.of_image {f : Piece → Image}
    {footprint : Image → Finset CellType} {target : Finset CellType}
    {selection : Finset Piece}
    (injective : Set.InjOn f (selection : Set Piece))
    (cover : IsExactCover footprint target (selection.image f)) :
    IsExactCover (fun piece => footprint (f piece)) target selection := by
  constructor
  · intro piece member
    exact cover.nonempty (f piece) (Finset.mem_image_of_mem f member)
  · simpa only [Finset.image_biUnion] using cover.union_eq
  · intro first firstMember second secondMember distinct
    exact cover.pairwiseDisjoint
      (Finset.mem_image_of_mem f firstMember)
      (Finset.mem_image_of_mem f secondMember)
      (fun equality => distinct (injective firstMember secondMember equality))

/-- A cover by images lifts to a cover by one representative of each image. -/
theorem exists_cover_image_iff (f : Piece → Image)
    (footprint : Image → Finset CellType) (candidates : Finset Piece)
    (target : Finset CellType) (selection : Finset Image) :
    selection ⊆ candidates.image f ∧ IsExactCover footprint target selection ↔
      ∃ representatives : Finset Piece,
        representatives ⊆ candidates ∧
          IsExactCover (fun piece => footprint (f piece)) target representatives ∧
            representatives.image f = selection := by
  classical
  constructor
  · rintro ⟨subset, cover⟩
    have surjective : Set.SurjOn f (candidates : Set Piece)
        (selection : Set Image) := by
      intro image member
      exact Finset.mem_image.mp (subset member)
    obtain ⟨representatives, contained, injective, imageEq⟩ :=
      surjective.exists_subset_injOn_image_eq
    have finite := candidates.finite_toSet.subset contained
    have finsetImage : finite.toFinset.image f = selection := by
      apply Finset.coe_injective
      simpa only [Finset.coe_image, Set.Finite.coe_toFinset] using imageEq
    refine ⟨finite.toFinset, ?_, ?_, finsetImage⟩
    · intro piece member
      exact contained (finite.mem_toFinset.mp member)
    · apply IsExactCover.of_image
        (by simpa only [Set.Finite.coe_toFinset] using injective)
      rw [finsetImage]
      exact cover
  · rintro ⟨representatives, subset, cover, rfl⟩
    exact ⟨Finset.image_subset_image subset, cover.image⟩

end LeanTrominoes.ExactCover
