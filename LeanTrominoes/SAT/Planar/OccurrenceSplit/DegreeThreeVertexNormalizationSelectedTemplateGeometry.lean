/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.DegreeThreeVertexNormalizationSelectedTemplates
import LeanTrominoes.Common.Geometry.GridPolylineRealPeriodicSeparation

/-! # Isolated boxes for the uncolored selected-incidence templates -/
namespace LeanTrominoes.DegreeThreeVertexNormalization
open PeriodicOrthocrossing

def selectedTemplateAt (position : Cell) (omitted selected : VertexSide) (port : CanonicalVertexPort) : List Cell :=
  translatePolyline (Cell.scale 32 position) (selectedTemplate omitted selected port)

theorem selectedTemplateAt_real_bounds (position : Cell) (omitted selected : VertexSide) (port : CanonicalVertexPort)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (selectedTemplateAt position omitted selected port) point) :
    (-8 : ℝ)+32*position.1 ≤ point.1 ∧ point.1 ≤ (8 : ℝ)+32*position.1 ∧
      (-8 : ℝ)+32*position.2 ≤ point.2 ∧ point.2 ≤ (8 : ℝ)+32*position.2 := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have bounds := GridPolyline.realContains_bounds (selectedTemplate_points_in_square omitted selected port) original
  simp only [Cell.scale,Prod.fst,Prod.snd,Int.cast_mul,Int.cast_ofNat] at bounds
  norm_num only [Int.cast_neg,Int.cast_ofNat] at bounds
  constructor
  · linarith [bounds.1]
  constructor
  · linarith [bounds.2.1]
  constructor <;> linarith [bounds.2.2.1,bounds.2.2.2]

theorem selectedTemplateAt_contacts_same_position {firstPosition secondPosition : Cell}
    (firstOmitted firstSelected secondOmitted secondSelected : VertexSide) (firstPort secondPort : CanonicalVertexPort)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (selectedTemplateAt firstPosition firstOmitted firstSelected firstPort) point)
    (secondContains : GridPolyline.RealContains (selectedTemplateAt secondPosition secondOmitted secondSelected secondPort) point) :
    firstPosition = secondPosition := by
  have firstBounds := selectedTemplateAt_real_bounds _ _ _ _ firstContains
  have secondBounds := selectedTemplateAt_real_bounds _ _ _ _ secondContains
  apply Prod.ext
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := 32) (lower := -8) (upper := 8)
      (point := point.1) (by norm_num) (by norm_num)
    · simpa using And.intro firstBounds.1 firstBounds.2.1
    · simpa using And.intro secondBounds.1 secondBounds.2.1
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := 32) (lower := -8) (upper := 8)
      (point := point.2) (by norm_num) (by norm_num)
    · simpa using And.intro firstBounds.2.2.1 firstBounds.2.2.2
    · simpa using And.intro secondBounds.2.2.1 secondBounds.2.2.2

theorem selectedTemplateAt_contacts_center (position : Cell) (omitted selected : VertexSide)
    (firstPort secondPort : CanonicalVertexPort) (different : firstPort ≠ secondPort) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (selectedTemplateAt position omitted selected firstPort) point)
    (secondContains : GridPolyline.RealContains (selectedTemplateAt position omitted selected secondPort) point) :
    point = realCell (Cell.scale 32 position) := by
  have firstOriginal := (GridPolyline.realContains_translate_inverse _ _ _).mp firstContains
  have secondOriginal := (GridPolyline.realContains_translate_inverse _ _ _).mp secondContains
  have contact := selectedTemplate_real_contacts_center omitted selected firstPort secondPort different firstOriginal secondOriginal
  have hx := congrArg Prod.fst contact
  have hy := congrArg Prod.snd contact
  apply Prod.ext <;> simp only [realCell,Prod.fst,Prod.snd,Int.cast_zero] at hx hy ⊢ <;> linarith

end LeanTrominoes.DegreeThreeVertexNormalization
