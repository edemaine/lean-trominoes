/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealSimpleCertificate
import Mathlib.Tactic

/-! # Simple horizontal tracks, boundary detours, and gate tracks -/
namespace LeanTrominoes

theorem horizontal_track_simple_certificate (sourceX targetX row : Int)
    (different : sourceX ≠ targetX) (above : 3 < row) :
    GridPolyline.SimpleBoxCertificate [(sourceX,3),(sourceX,row),(targetX,row),(targetX,3)] := by
  simp [GridPolyline.SimpleBoxCertificate,gridPolylineSegments,GridSegment.BoxIntersectionIsPoint]
  omega

theorem boundary_track_simple_certificate (sourceX boundaryX targetX row : Int)
    (ordered : (sourceX < boundaryX ∧ boundaryX < targetX) ∨
      (targetX < boundaryX ∧ boundaryX < sourceX)) (above : 3 < row) :
    GridPolyline.SimpleBoxCertificate [(sourceX,3),(sourceX,row),(boundaryX,row),
      (boundaryX,row+1),(targetX,row+1),(targetX,3)] := by
  simp [GridPolyline.SimpleBoxCertificate,gridPolylineSegments,GridSegment.BoxIntersectionIsPoint]
  omega

theorem gate_track_simple_certificate (sourceX targetX gate sourceY targetY firstRow secondRow : Int)
    (sourceLeft : sourceX < gate) (targetLeft : targetX < gate)
    (firstAbove : sourceY < firstRow) (secondAbove : targetY < secondRow)
    (separated : firstRow < targetY ∨ secondRow < sourceY) :
    GridPolyline.SimpleBoxCertificate [(sourceX,sourceY),(sourceX,firstRow),(gate,firstRow),
      (gate,secondRow),(targetX,secondRow),(targetX,targetY)] := by
  simp [GridPolyline.SimpleBoxCertificate,gridPolylineSegments,GridSegment.BoxIntersectionIsPoint]
  omega

end LeanTrominoes
