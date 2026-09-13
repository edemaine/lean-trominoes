/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnaryKeyGeometry

/-! # The emitted disconnected tile is the exact keyed complement -/

namespace LeanTrominoes.Theorem55StripUnary

theorem gridPoints_mem (source : PeriodicStrip) (p : Nat×Nat) :
    p ∈ gridPoints source ↔ p.1 < side source ∧ p.2 < side source := by
  rcases p with ⟨x,y⟩
  simp [gridPoints]

theorem unbias_add_one (p : Nat×Nat) : unbias (p.1+1,p.2+1) = natCell p := by
  simp [unbias,natCell]

theorem ordinaryTable_mem (source : PeriodicStrip) (valid : source.IsWellFormed) (p : Nat×Nat) :
    p ∈ ordinaryTable.rows source ↔ p.1 < side source ∧ p.2 < side source ∧
      natCell p ∉ Theorem55StripSource.holes source ∧
      natCell p ∉ KeyedPeriodicComplement.horizontalLock (side source) := by
  change p ∈ (gridTable.rows source).filter (keep source) ↔ _
  rw [List.mem_filter,gridTable_rows,gridPoints_mem]
  constructor
  · rintro ⟨⟨hx,hy⟩,kept⟩
    have inside : unbias (p.1+1,p.2+1) ∈ KeyedPeriodicComplement.square (side source) := by
      rw [unbias_add_one,KeyedPeriodicComplement.mem_square]
      dsimp [natCell]
      exact ⟨by omega,by omega,by omega,by omega⟩
    have semantic := excludedKeys_exact source valid (p.1+1,p.2+1) inside
    rw [unbias_add_one] at semantic
    exact ⟨hx,hy,by simpa [keep,semantic] using kept⟩
  · rintro ⟨hx,hy,hh,hl⟩
    have inside : unbias (p.1+1,p.2+1) ∈ KeyedPeriodicComplement.square (side source) := by
      rw [unbias_add_one,KeyedPeriodicComplement.mem_square]
      dsimp [natCell]
      exact ⟨by omega,by omega,by omega,by omega⟩
    have semantic := excludedKeys_exact source valid (p.1+1,p.2+1) inside
    rw [unbias_add_one] at semantic
    exact ⟨⟨hx,hy⟩,by simp [keep,semantic,hh,hl]⟩

theorem ordinaryTable_cells (source : PeriodicStrip) (valid : source.IsWellFormed) :
    ((ordinaryTable.rows source).map natCell).toFinset =
      KeyedPeriodicComplement.background (side source) (Theorem55StripSource.holes source) \
        KeyedPeriodicComplement.horizontalLock (side source) := by
  ext c
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_sdiff,KeyedPeriodicComplement.background]
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨hx,hy,hh,hl⟩ := (ordinaryTable_mem source valid p).mp hp
    exact ⟨⟨(KeyedPeriodicComplement.mem_square _ _).mpr ⟨by simp [natCell],by simpa [natCell] using hx,
      by simp [natCell],by simpa [natCell] using hy⟩,hh⟩,hl⟩
  · rintro ⟨⟨hc,hh⟩,hl⟩
    obtain ⟨hx₀,hx₁,hy₀,hy₁⟩ := (KeyedPeriodicComplement.mem_square _ _).mp hc
    have he : natCell (c.1.toNat,c.2.toNat) = c := by
      apply Prod.ext <;> dsimp [natCell] <;> omega
    refine ⟨(c.1.toNat,c.2.toNat),(ordinaryTable_mem source valid _).mpr ?_,he⟩
    exact ⟨by omega,by omega,by simpa [he] using hh,by simpa [he] using hl⟩

theorem horizontalLock_background (source : PeriodicStrip) (positive : 0 < source.period) :
    KeyedPeriodicComplement.horizontalLock (side source) ⊆
      KeyedPeriodicComplement.background (side source) (Theorem55StripSource.holes source) := by
  intro c hc
  have large := side_large source positive
  have coordinate : (side source : Int)-4 ≤ c.1 ∧ c.1 < side source ∧ 2 ≤ c.2 ∧ c.2 ≤ 3 := by
    simp only [KeyedPeriodicComplement.horizontalLock,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  refine Finset.mem_sdiff.mpr ⟨(KeyedPeriodicComplement.mem_square _ _).mpr ⟨by omega,coordinate.2.1,by omega,by omega⟩,?_⟩
  intro hole
  rw [Theorem55StripSource.holes,KeyedPeriodicComplement.mem_mask] at hole
  obtain ⟨_,parent,hparent,u,hu,he⟩ := hole
  have parentBounds := Theorem55StripSource.region_bounds source positive hparent
  have subBounds := cross_bounds hu
  have y := congrArg Prod.snd he
  dsimp [PlusRefinement.pixel,Cell.add,Cell.scale] at y
  omega

theorem leftKeyCells_image (n : Nat) : leftKeyCells.toFinset =
    (KeyedPeriodicComplement.horizontalLock n).image (fun c => Cell.add c (-(n : Int),0)) := by
  ext c
  simp [leftKeyCells,KeyedPeriodicComplement.horizontalLock,Cell.add,Prod.ext_iff]
  omega

end LeanTrominoes.Theorem55StripUnary
