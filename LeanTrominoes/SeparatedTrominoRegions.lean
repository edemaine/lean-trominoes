/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetAssembly

/-! # Restricting tromino tilings to geometrically separated components

A separation of more than two in some coordinate prevents an I or L tromino
from crossing between components. This permits finite components to be cut out
of an infinite gadget carrier without imposing periodicity on its tiling.
-/
namespace LeanTrominoes.Tromino
open Gadget

/-- Distinct regions have a gap larger than either tromino's coordinate span. -/
def RegionsSeparated {Index : Type*} (regions : Index → Set Cell) : Prop :=
  ∀ first second, first≠second → ∀ x∈regions first, ∀ y∈regions second,
    2<x.1-y.1 ∨ 2<y.1-x.1 ∨ 2<x.2-y.2 ∨ 2<y.2-x.2

/-- A footprint meeting one separated component lies entirely in it. -/
theorem IsFootprint.component {Index : Type*} {t : Tromino} {tile : Finset Cell}
    {regions : Index → Set Cell} (shape : t.IsFootprint tile)
    (separated : RegionsSeparated regions)
    (inside : ∀ cell∈tile, ∃ index, cell∈regions index)
    {index : Index} {cell : Cell} (member : cell∈tile) (inRegion : cell∈regions index) :
    ∀ other∈tile, other∈regions index := by
  intro other otherMember
  obtain ⟨otherIndex,otherRegion⟩ := inside other otherMember
  by_cases same : index=otherIndex
  · exact same ▸ otherRegion
  · have gap := separated index otherIndex same cell inRegion other otherRegion
    have bounds := Gadget.Tromino.IsFootprint.coordinate_bounds shape member otherMember
    omega

/-- Restrict an exact cover whenever all tiles meeting the smaller region stay
inside that region. -/
theorem IsFootprintTiling.restrictSeparated {t : Tromino} {large small : Set Cell}
    {tiles : Set (Finset Cell)} (tiling : IsFootprintTiling t large tiles)
    (subset : small⊆large)
    (closed : ∀ tile∈tiles, (∃ cell∈small, cell∈tile) → ∀ cell∈tile, cell∈small) :
    IsFootprintTiling t small {tile | tile∈tiles ∧ ∃ cell∈small, cell∈tile} := by
  constructor
  · rintro tile ⟨ht,meets⟩
    exact ⟨(tiling.tilesInside tile ht).1,closed tile ht meets⟩
  · intro cell member
    obtain ⟨tile,⟨ht,hc⟩,unique⟩ := tiling.uniqueCover cell (subset member)
    refine ⟨tile,⟨⟨ht,cell,member,hc⟩,hc⟩,?_⟩
    rintro other ⟨⟨ho,_⟩,covers⟩
    exact unique other ⟨ho,covers⟩

/-- An arbitrary tiling of a separated union restricts to each component. -/
theorem tileable_component {Index : Type*} {t : Tromino} (regions : Index → Set Cell)
    (separated : RegionsSeparated regions)
    (tileable : t.Tileable {cell | ∃ index, cell∈regions index}) (index : Index) :
    t.Tileable (regions index) := by
  obtain ⟨tiles,tiling⟩ := (t.tileable_iff_exists_footprintTiling _).mp tileable
  apply (t.tileable_iff_exists_footprintTiling _).mpr
  refine ⟨_,tiling.restrictSeparated (fun cell member => ⟨index,member⟩) ?_⟩
  intro tile member meets
  obtain ⟨cell,inRegion,inTile⟩ := meets
  exact (tiling.tilesInside tile member).1.component separated
    (tiling.tilesInside tile member).2 inTile inRegion

/-- Exact component covers glue when their target regions are disjoint. -/
theorem tileable_union {Index : Type*} {t : Tromino} (regions : Index → Set Cell)
    (disjoint : ∀ first second, first≠second → Disjoint (regions first) (regions second))
    (tileable : ∀ index, t.Tileable (regions index)) :
    t.Tileable {cell | ∃ index, cell∈regions index} := by
  classical
  have witnesses : ∀ index, ∃ tiles, IsFootprintTiling t (regions index) tiles :=
    fun index => (t.tileable_iff_exists_footprintTiling _).mp (tileable index)
  choose tiles tilings using witnesses
  apply (t.tileable_iff_exists_footprintTiling _).mpr
  refine ⟨{tile | ∃ index, tile∈tiles index},?_⟩
  constructor
  · rintro tile ⟨index,member⟩
    exact ⟨(tilings index |>.tilesInside tile member).1,
      fun cell hc => ⟨index,(tilings index |>.tilesInside tile member).2 cell hc⟩⟩
  · rintro cell ⟨index,member⟩
    obtain ⟨tile,⟨ht,hc⟩,unique⟩ := (tilings index).uniqueCover cell member
    refine ⟨tile,⟨⟨index,ht⟩,hc⟩,?_⟩
    rintro other ⟨⟨otherIndex,ho⟩,covers⟩
    have same : index=otherIndex := by
      by_contra different
      exact Set.disjoint_left.mp (disjoint index otherIndex different) member
        (((tilings otherIndex).tilesInside other ho).2 cell covers)
    subst otherIndex
    exact unique other ⟨ho,covers⟩

end LeanTrominoes.Tromino
