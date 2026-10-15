/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendContractionPieces
import LeanTrominoes.Common.Geometry.GridPolylineRealRouteChainClosure

/-! # Joining all refined pieces of an original protoedge preserves simplicity -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

theorem parentPieces_openSimple {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) {route : List Cell}
    (member : route ∈ parentPieces source drawing parent) : GridPolyline.IsRealOpenSimple route := by
  obtain ⟨record,recordMember,rfl⟩ := List.mem_map.mp member
  exact refinedPiece_openSimple planar localDrawing localGraph degree (parentRecord_mem parentMember recordMember)

theorem parentPieces_chain {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) :
    (parentPieces source drawing parent).IsChain (fun first second => first.getLast?=second.head?) := by
  apply List.isChain_iff_getElem.mpr
  intro index valid
  obtain ⟨first,firstMember,_,firstRoute,firstPiece⟩ := parentPiece_data planar parentMember (by omega : index < _)
  obtain ⟨second,secondMember,_,secondRoute,secondPiece⟩ := parentPiece_data planar parentMember valid
  have firstEnds := refinedPiece_endpoints planar localDrawing localGraph degree firstMember
  have secondEnds := refinedPiece_endpoints planar localDrawing localGraph degree secondMember
  have boundary := indexed_gridPolylineSegments_consecutive firstPiece secondPiece rfl
  rw [firstRoute,secondRoute,firstEnds.2,secondEnds.1,boundary]

theorem parentPieces_contactPattern {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) :
    GridPolyline.RouteContactPattern (parentPieces source drawing parent) := by
  intro i j hi hj ordered p firstContains secondContains
  obtain ⟨first,firstMember,firstKey,firstRoute,firstPiece⟩ := parentPiece_data planar parentMember hi
  obtain ⟨second,secondMember,secondKey,secondRoute,secondPiece⟩ := parentPiece_data planar parentMember hj
  rw [firstRoute] at firstContains
  rw [secondRoute] at secondContains
  have different : first.1≠second.1 := by rw [firstKey,secondKey]; intro equal; have := congrArg Prod.snd equal; omega
  have endpoints := refinedPiece_endpoint_contacts planar localDrawing localGraph degree firstMember secondMember different
    firstContains secondContains
  have firstEnds := refinedPiece_endpoints planar localDrawing localGraph degree firstMember
  have secondEnds := refinedPiece_endpoints planar localDrawing localGraph degree secondMember
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph (bendRefinementFactor_spacing drawing)
  have oldSimple := movedPlanar.1.2.1 _ (edgeRoute_mem_of_compatible movedPlanar.1.1 parentMember)
  have scalePositive : (0:Int) < subdivisionScale drawing := by
    exact_mod_cast paddedRefinementFactor_positive (bendRefinementFactor drawing*drawing.gridSize)
  have contact := oldSimple.replacement_contacts (Cell.scale (subdivisionScale drawing))
    (Cell.scale_injective scalePositive.ne') firstPiece secondPiece ordered
    (GridPolyline.realEndpoint_of_prescribed_endpoints firstEnds.1 firstEnds.2 endpoints.1)
    (GridPolyline.realEndpoint_of_prescribed_endpoints secondEnds.1 secondEnds.2 endpoints.2)
  rcases contact with adjacent | closed
  · exact Or.inl ⟨_,by rw [firstRoute]; exact firstEnds.2,adjacent.2⟩
  · refine Or.inr ⟨closed.1,?_,_,?_,?_,closed.2.2.1⟩
    · rw [parentPieces_length planar parentMember]
      exact closed.2.1
    · rw [firstRoute]
      exact firstEnds.1
    · rw [secondRoute,secondEnds.2]
      exact congrArg some (realCell_injective (closed.2.2.2.symm.trans closed.2.2.1))

theorem contractedRoute_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) : GridPolyline.IsRealSimple (contractedRoute source drawing parent) := by
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph (bendRefinementFactor_spacing drawing)
  have oldSimple := movedPlanar.1.2.1 _ (edgeRoute_mem_of_compatible movedPlanar.1.1 parentMember)
  have length := parentPieces_length planar parentMember
  rw [gridPolylineSegments_length] at length
  have piecesNonempty : parentPieces source drawing parent≠[] := by
    intro empty
    rw [empty,List.length_nil] at length
    have long := oldSimple.1
    omega
  exact GridPolyline.joinRouteChain_simple piecesNonempty
    (fun _ member => parentPieces_openSimple planar localDrawing localGraph degree parentMember member)
    (parentPieces_chain planar localDrawing localGraph degree parentMember)
    (parentPieces_contactPattern planar localDrawing localGraph degree parentMember)

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
