/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnaryParentGeometry

/-! # Biased natural-coordinate tables for exact cross refinement -/

namespace LeanTrominoes.Theorem55StripUnary

def unbias (p : Nat×Nat) : Cell := ((p.1 : Int)-1,(p.2 : Int)-1)

theorem unbias_injective : Function.Injective unbias := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> dsimp [unbias] at hx hy <;> omega

theorem crossOffsets_image : (crossOffsets.map unbias).toFinset = PlusRefinement.cross := by decide

theorem crossOffsets_bound {q : Nat×Nat} (hq : q ∈ crossOffsets) : q.1 ≤ 2 ∧ q.2 ≤ 2 := by
  simp only [crossOffsets,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide

def refinedPoints (parents : List (Nat×Nat)) : List (Nat×Nat) :=
  parents.flatMap fun p => crossOffsets.map fun q => (p.1*3+q.1,p.2*3+q.2)

theorem holeTable_rows (source : PeriodicStrip) :
    holeTable.rows source = refinedPoints (parentTable.rows source) ++ refinedPoints paddingParents := by
  simp [holeTable,UnaryPointTable.append,UnaryPointTable.sum,UnaryPointTable.sumRows,
    UnaryPointTable.affine,UnaryPointTable.constant,refinedPoints,List.flatMap_map,List.map_map,Function.comp_def]

theorem unbias_refined (p q : Nat×Nat) :
    unbias (p.1*3+q.1,p.2*3+q.2) = PlusRefinement.pixel (natCell p) (unbias q) := by
  apply Prod.ext <;> simp [unbias,PlusRefinement.pixel,natCell,Cell.add,Cell.scale] <;> ring

theorem refinedPoints_iff (parents : List (Nat×Nat)) (point : Nat×Nat) :
    point ∈ refinedPoints parents ↔
      ∃ p ∈ parents, ∃ u ∈ PlusRefinement.cross, PlusRefinement.pixel (natCell p) u = unbias point := by
  constructor
  · intro h
    obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
    refine ⟨p,hp,unbias q,?_,(unbias_refined p q).symm⟩
    rw [← crossOffsets_image]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,hq,rfl⟩)
  · rintro ⟨p,hp,u,hu,he⟩
    rw [← crossOffsets_image,List.mem_toFinset] at hu
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hu
    have equal : (p.1*3+q.1,p.2*3+q.2) = point :=
      unbias_injective ((unbias_refined p q).trans he)
    exact List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨q,hq,equal⟩⟩

theorem paddingParents_region (source : PeriodicStrip) (positive : 0 < source.period)
    {p : Nat×Nat} (hp : p ∈ paddingParents) : natCell p ∈ StripTrominoPadding.region (Theorem55StripSource.period source) := by
  have large := Theorem55StripSource.period_large source positive
  simp only [paddingParents,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [natCell,StripTrominoPadding.region,
      Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 14) (by omega : (14 : Int) < Theorem55StripSource.period source),
      Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 15) (by omega : (15 : Int) < Theorem55StripSource.period source)]

theorem holeTable_region (source : PeriodicStrip) (valid : source.IsWellFormed)
    {point : Nat×Nat} (hp : point ∈ holeTable.rows source) :
    unbias point ∈ PlusRefinement.region (Theorem55StripSource.region source) := by
  rw [holeTable_rows,List.mem_append] at hp
  rcases hp with hp | hp
  · obtain ⟨p,hp,u,hu,he⟩ := (refinedPoints_iff _ _).mp hp
    exact ⟨natCell p,Or.inl (parentTable_shifted source valid hp),u,hu,he⟩
  · obtain ⟨p,hp,u,hu,he⟩ := (refinedPoints_iff _ _).mp hp
    exact ⟨natCell p,Or.inr (paddingParents_region source valid.2.1 hp),u,hu,he⟩

theorem padding_parent_exists (source : PeriodicStrip) (positive : 0 < source.period)
    (c : Cell) (hx₀ : 0 ≤ c.1) (hx₁ : c.1 ≤ Theorem55StripSource.period source)
    (hc : c ∈ StripTrominoPadding.region (Theorem55StripSource.period source)) :
    ∃ p ∈ paddingParents, natCell p = c := by
  have large := Theorem55StripSource.period_large source positive
  have hlt : c.1 < Theorem55StripSource.period source := by
    by_contra bad
    have he : c.1 = Theorem55StripSource.period source := by omega
    have h := hc.1
    rw [he,Int.emod_self] at h
    omega
  have hx : c.1 = 14 ∨ c.1 = 15 := by
    simpa [Int.emod_eq_of_lt hx₀ hlt] using hc.1
  have hy := hc.2
  refine ⟨(c.1.toNat,c.2.toNat),?_,?_⟩
  · simp only [paddingParents,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
    omega
  · apply Prod.ext <;> dsimp [natCell] <;> omega

theorem cross_bounds {u : Cell} (hu : u ∈ PlusRefinement.cross) :
    -1 ≤ u.1 ∧ u.1 ≤ 1 ∧ -1 ≤ u.2 ∧ u.2 ≤ 1 := by
  simp only [PlusRefinement.cross,Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The extra final copy contains every cross that straddles the right period edge. -/
theorem holeTable_exact (source : PeriodicStrip) (valid : source.IsWellFormed)
    (point : Nat×Nat) (inside : unbias point ∈ KeyedPeriodicComplement.square (side source)) :
    point ∈ holeTable.rows source ↔ unbias point ∈ Theorem55StripSource.holes source := by
  rw [Theorem55StripSource.holes,KeyedPeriodicComplement.mem_mask]
  constructor
  · intro member
    exact ⟨inside,holeTable_region source valid member⟩
  · rintro ⟨_,parent,hparent,u,hu,equal⟩
    have cb := (KeyedPeriodicComplement.mem_square _ _).mp inside
    have ub := cross_bounds hu
    have hx : 0 ≤ parent.1 ∧ parent.1 ≤ Theorem55StripSource.period source := by
      have ex := congrArg Prod.fst equal
      dsimp [PlusRefinement.pixel,Cell.add,Cell.scale] at ex
      dsimp [side] at cb
      push_cast at cb
      omega
    rw [holeTable_rows,List.mem_append]
    rcases hparent with shifted | padding
    · obtain ⟨p,hp,he⟩ := shifted_parent_exists source valid parent hx.1 hx.2 shifted
      left
      exact (refinedPoints_iff _ _).mpr ⟨p,hp,u,hu,by rw [he]; exact equal⟩
    · obtain ⟨p,hp,he⟩ := padding_parent_exists source valid.2.1 parent hx.1 hx.2 padding
      right
      exact (refinedPoints_iff _ _).mpr ⟨p,hp,u,hu,by rw [he]; exact equal⟩

end LeanTrominoes.Theorem55StripUnary
