/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoTilingTranslation
import LeanTrominoes.Periodic

/-! # Cutting isolated finite motifs out of periodic tromino instances

A three-cell gap between translated motif bounding boxes prevents a tromino
from crossing between copies. Finite and periodic tileability then agree,
including when the periodic tiling itself has no period.
-/
namespace LeanTrominoes.Tromino.FinitePeriodicBridge

def offset (width height : Int) (index : Cell) : Cell :=
  (width*index.1,height*index.2)

def copies (width height : Int) (region : Set Cell) (index : Cell) : Set Cell :=
  translatedRegion (offset width height index) region

private theorem coordinate_gap (period x y first second : Int)
    (positive : 0≤period) (hx : 0≤x ∧ x≤period-3) (hy : 0≤y ∧ y≤period-3)
    (different : first≠second) :
    2<(period*first+x)-(period*second+y) ∨
      2<(period*second+y)-(period*first+x) := by
  rcases lt_or_gt_of_ne different with h | h
  · right
    have translated := mul_le_mul_of_nonneg_left (show first+1≤second by omega) positive
    nlinarith
  · left
    have translated := mul_le_mul_of_nonneg_left (show second+1≤first by omega) positive
    nlinarith

theorem copies_separated (width height : Int) (region : Set Cell)
    (widthPositive : 0≤width) (heightPositive : 0≤height)
    (bounds : ∀ cell∈region,
      0≤cell.1 ∧ cell.1≤width-3 ∧ 0≤cell.2 ∧ cell.2≤height-3) :
    RegionsSeparated (copies width height region) := by
  rintro first second different x ⟨base,hb,rfl⟩ y ⟨other,ho,rfl⟩
  have firstBounds := bounds base hb
  have secondBounds := bounds other ho
  by_cases horizontal : first.1=second.1
  · have vertical : first.2≠second.2 := by intro equal; exact different (Prod.ext horizontal equal)
    have gap := coordinate_gap height base.2 other.2 first.2 second.2 heightPositive
      ⟨firstBounds.2.2.1,firstBounds.2.2.2⟩ ⟨secondBounds.2.2.1,secondBounds.2.2.2⟩ vertical
    simpa [offset,Cell.add] using Or.inr (Or.inr gap)
  · have gap := coordinate_gap width base.1 other.1 first.1 second.1 widthPositive
      ⟨firstBounds.1,firstBounds.2.1⟩ ⟨secondBounds.1,secondBounds.2.1⟩ horizontal
    rcases gap with gap | gap
    · exact Or.inl gap
    · exact Or.inr (Or.inl gap)

theorem copies_disjoint (width height : Int) (region : Set Cell)
    (separated : RegionsSeparated (copies width height region)) :
    ∀ first second, first≠second → Disjoint (copies width height region first)
      (copies width height region second) := by
  intro first second different
  apply Set.disjoint_left.mpr
  intro cell member other
  have gap := separated first second different cell member cell other
  omega

/-- A tiling of the repeated carrier exists exactly when one finite motif is
 tileable, provided its translated bounding boxes have the stated gap. -/
theorem tileable_copies_iff (t : Tromino) (width height : Int) (region : Set Cell)
    (widthPositive : 0≤width) (heightPositive : 0≤height)
    (bounds : ∀ cell∈region,
      0≤cell.1 ∧ cell.1≤width-3 ∧ 0≤cell.2 ∧ cell.2≤height-3) :
    t.Tileable {cell | ∃ index, cell∈copies width height region index} ↔ t.Tileable region := by
  have separated := copies_separated width height region widthPositive heightPositive bounds
  constructor
  · intro tileable
    have finite := tileable_component (copies width height region) separated tileable (0,0)
    simpa [copies,offset] using finite
  · intro tileable
    exact tileable_union (copies width height region) (copies_disjoint width height region separated)
      (fun index => tileable_translate tileable (offset width height index))

def periodicRegion (motif : List Cell) (width height : Int) : PeriodicRegion :=
  ⟨motif,(width,0),(0,height)⟩

theorem carrier_eq_copies (motif : List Cell) (width height : Int) :
    (periodicRegion motif width height).carrier=
      {cell | ∃ index, cell∈copies width height (motif.toFinset : Set Cell) index} := by
  ext cell
  constructor
  · rintro ⟨base,hb,i,j,rfl⟩
    refine ⟨(i,j),base,List.mem_toFinset.mpr hb,?_⟩
    apply Prod.ext <;> simp [offset,Cell.add,Cell.scale,periodicRegion] <;> ring
  · rintro ⟨index,base,hb,rfl⟩
    refine ⟨base,List.mem_toFinset.mp hb,index.1,index.2,?_⟩
    apply Prod.ext <;> simp [offset,Cell.add,Cell.scale,periodicRegion] <;> ring

/-- The finite-target geometric bridge for isolated periodic gadget copies. -/
theorem finite_tileable_iff_periodic (t : Tromino) (motif : List Cell) (width height : Int)
    (widthPositive : 0≤width) (heightPositive : 0≤height)
    (bounds : ∀ cell∈motif,
      0≤cell.1 ∧ cell.1≤width-3 ∧ 0≤cell.2 ∧ cell.2≤height-3) :
    t.Tileable (motif.toFinset : Set Cell) ↔
      t.Tileable (periodicRegion motif width height).carrier := by
  rw [carrier_eq_copies]
  exact (tileable_copies_iff t width height _ widthPositive heightPositive
    (by simpa using bounds)).symm

end LeanTrominoes.Tromino.FinitePeriodicBridge
