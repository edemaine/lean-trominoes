/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMGeometry
import LeanTrominoes.SignedRouteFieldsCompiler
import LeanTrominoes.UnaryFieldClosure

/-! # Complete unit-subdivided native 3DM route and segment tables -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget UnaryColumn DelimitedDirectionDisplacement PeriodicThreeDM
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

abbrev nativeThreeDMUnitDrawing (s : List encoding.Γ) := (nativeThreeDMDrawing decider s).unitSubdivide

omit [Inhabited encoding.Γ] in
theorem nativeThreeDMRoute_rebuild (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) :
    rebuildRoute (nativeThreeDMSourcePoint decider s tag)
      (unitSubdivisionDirections (nativeThreeDMRoute decider s tag)) =
      AxisDirection.unitSubdividePolyline (nativeThreeDMRoute decider s tag) := by
  have head := (nativeThreeDMRoute_endpoints decider s tag ht).1
  have orthogonal := nativeThreeDMRoute_orthogonal decider s tag ht
  have nonempty : nativeThreeDMRoute decider s tag ≠ [] := by intro h; simp [h] at head
  have unithead := (AxisDirection.unitSubdividePolyline_head? nonempty).trans head
  have h := (rebuildRoute_eq_vertices _ _).trans
    (unitRoute_eq_vertices _ _ unithead (AxisDirection.unitSubdividePolyline_unitSteps orthogonal)).symm
  rw [unitSubdivisionDirections_unitSubdividePolyline (nativeThreeDMRoute decider s tag) orthogonal] at h
  exact h

omit [Inhabited encoding.Γ] in
theorem nativeThreeDMUnitDrawing_routes (s : List encoding.Γ) :
    (nativeThreeDMUnitDrawing decider s).edgeRoutes = (nativeThreeDMIncidences decider s).map
      (fun tag => rebuildRoute (nativeThreeDMSourcePoint decider s tag)
        (unitSubdivisionDirections (nativeThreeDMRoute decider s tag))) := by
  simp only [nativeThreeDMUnitDrawing,PeriodicGridDrawing.unitSubdivide,nativeThreeDMDrawing,
    horizontalThreeDMDrawingComputed_edgeRoutes,horizontalThreeDMEdgeRoutesComputed,
    horizontalThreeDMIncidenceTagsComputed,List.map_map]
  apply List.map_congr_left
  intro tag ht
  exact (nativeThreeDMRoute_rebuild decider s tag ht).symm

def nativeThreeDMRouteFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (nativeThreeDMUnitDrawing decider s).edgeRoutes.flatMap PeriodicGridDrawing.Arithmetic.routeFields) := by
  let physical := signedRouteFieldsCompiler (nativeThreeDMIncidences decider)
    (fun s tag => unitSubdivisionDirections (nativeThreeDMRoute decider s tag)) (nativeThreeDMSourcePoint decider)
    (nativeThreeDMDirectionsCompiler decider)
    (nativeThreeDMSourcePointCompiler decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [nativeThreeDMUnitDrawing_routes,List.flatMap_map]

def nativeThreeDMSegmentFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (nativeThreeDMUnitDrawing decider s).indexedSegments.flatMap PeriodicGridDrawing.Arithmetic.segmentFields) := by
  let physical := signedSegmentFieldsCompiler (nativeThreeDMIncidences decider)
    (fun s tag => unitSubdivisionDirections (nativeThreeDMRoute decider s tag)) (nativeThreeDMSourcePoint decider)
    (nativeThreeDMDirectionsCompiler decider)
    (nativeThreeDMSourcePointCompiler decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [← segmentTableFields_drawing,nativeThreeDMUnitDrawing_routes]

end LeanTrominoes.PeriodicCNFStripReduction
end
