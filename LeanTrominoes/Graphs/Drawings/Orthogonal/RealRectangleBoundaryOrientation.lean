/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealOppositeSides
import Mathlib.Data.Prod.Lex

/-! # Clockwise rectangle boundary intervals lie on one side of their chord -/
namespace LeanTrominoes.RealRectangleBoundary

structure Port where
  side : Fin 4
  coordinate : ℝ

def Port.extent (width height : ℝ) (port : Port) : ℝ :=
  if port.side.val = 0 ∨ port.side.val = 2 then height else width

def Port.Inside (width height : ℝ) (port : Port) : Prop :=
  0 < port.coordinate ∧ port.coordinate < port.extent width height

def Port.point (width height : ℝ) (port : Port) : ℝ × ℝ :=
  match port.side.val with
  | 0 => (0,port.coordinate)
  | 1 => (port.coordinate,height)
  | 2 => (width,port.coordinate)
  | _ => (port.coordinate,0)

def Port.clockwiseCode (port : Port) : Nat ×ₗ ℝ :=
  toLex (port.side.val,if port.side.val < 2 then port.coordinate else -port.coordinate)

def Port.Before (first second : Port) : Prop := first.clockwiseCode < second.clockwiseCode

def Port.gap (first second : Port) : ℝ :=
  if first.side = second.side then
    if first.side.val < 2 then second.coordinate-first.coordinate else first.coordinate-second.coordinate
  else 1

theorem Port.gap_positive {first second : Port} (ordered : first.Before second) : 0 < first.gap second := by
  unfold gap
  split_ifs with same forward
  · simp only [Before,clockwiseCode,Prod.Lex.toLex_lt_toLex] at ordered
    rw [same] at ordered forward
    simp [forward] at ordered
    linarith
  · simp only [Before,clockwiseCode,Prod.Lex.toLex_lt_toLex] at ordered
    rw [same] at ordered forward
    simp [forward] at ordered
    linarith
  · norm_num

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

theorem orientedArea_positive_between {width height : ℝ} {first middle last : Port}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (firstInside : first.Inside width height) (middleInside : middle.Inside width height)
    (lastInside : last.Inside width height)
    (firstOrder : first.Before middle) (lastOrder : middle.Before last)
    (differentSides : first.side ≠ last.side) :
    0 < GridSegment.orientedArea (first.point width height) (last.point width height) (middle.point width height) := by
  have wholeOrder : first.Before last := lt_trans firstOrder lastOrder
  have firstGap := Port.gap_positive firstOrder
  have lastGap := Port.gap_positive lastOrder
  have wholeGap := Port.gap_positive wholeOrder
  let values := [width,height,first.coordinate,first.extent width height-first.coordinate,
    middle.coordinate,middle.extent width height-middle.coordinate,
    last.coordinate,last.extent width height-last.coordinate,
    first.gap middle,middle.gap last,first.gap last]
  have piecesPositive : ∀ value ∈ values, 0 < value := by
    simp only [values,List.forall_mem_cons]
    exact ⟨widthPositive,heightPositive,firstInside.1,sub_pos.mpr firstInside.2,
      middleInside.1,sub_pos.mpr middleInside.2,lastInside.1,sub_pos.mpr lastInside.2,
      firstGap,lastGap,wholeGap,by simp⟩
  have products : ∀ x ∈ values, ∀ y ∈ values, 0 < x*y :=
    fun x xm y ym => mul_pos (piecesPositive x xm) (piecesPositive y ym)
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨middleSide,middleCoordinate⟩ := middle
  obtain ⟨lastSide,lastCoordinate⟩ := last
  fin_cases firstSide <;> fin_cases middleSide <;> fin_cases lastSide <;>
    simp [Port.Before,Port.clockwiseCode,Prod.Lex.toLex_lt_toLex] at firstOrder lastOrder differentSides
  all_goals
    simp [values,Port.extent,Port.gap] at products
    simp [Port.point,GridSegment.orientedArea]
    ring_nf at products ⊢
    linarith only [products]

end LeanTrominoes.RealRectangleBoundary
