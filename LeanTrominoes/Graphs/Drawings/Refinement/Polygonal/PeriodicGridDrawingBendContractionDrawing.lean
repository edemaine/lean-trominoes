/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendContractionEndpoints
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineSymmetries

/-! # The original periodic graph drawn by joining its refined subedges -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicOrthocrossing

def contractedDrawing {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing where
  gridSizePred := polygonalScale drawing*drawing.gridSize-1
  vertexPositions := drawing.vertexPositions.map (Cell.scale (polygonalScale drawing))
  edgeRoutes := source.edges.zipIdx.map (contractedRoute source drawing)

theorem contractedDrawing_gridSize {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) :
    (contractedDrawing source drawing).gridSize=polygonalScale drawing*drawing.gridSize := by
  have positive : 0 < polygonalScale drawing*drawing.gridSize :=
    Nat.mul_pos (polygonalScale_positive drawing) (Nat.zero_lt_succ drawing.gridSizePred)
  change polygonalScale drawing*drawing.gridSize-1+1=_
  omega

theorem contractedDrawing_periodTranslation {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (copy : Cell) :
    (contractedDrawing source drawing).periodTranslation copy=(orthogonalSubdivision source drawing).periodTranslation copy := by
  rw [periodTranslation,periodTranslation,contractedDrawing_gridSize,orthogonalSubdivision_gridSize,polygonalScale]
  simp only [Nat.mul_assoc]

theorem contractedDrawing_vertexPosition {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (vertex : V) :
    (contractedDrawing source drawing).vertexPosition source vertex=
      Cell.scale (polygonalScale drawing) (drawing.vertexPosition source vertex) := by
  simp only [vertexPosition,contractedDrawing]
  change (drawing.vertexPositions.map (Cell.scale (polygonalScale drawing))).getD
    (source.vertices.idxOf vertex) (Cell.scale (polygonalScale drawing) (0,0))=_
  exact List.getD_map _ _ _

theorem contractedDrawing_edgeRoute {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} {parent : PeriodicEdge V × Nat}
    (member : parent ∈ source.edges.zipIdx) :
    (contractedDrawing source drawing).edgeRoute parent.2=contractedRoute source drawing parent := by
  have atIndex := List.mem_zipIdx_iff_getElem?.mp member
  have taggedAt : source.edges.zipIdx[parent.2]?=some parent := by
    rw [List.getElem?_zipIdx,atIndex]
    simp
  simp only [contractedDrawing,edgeRoute,List.getD_eq_getElem?_getD,List.getElem?_map,taggedAt,
    Option.map_some,Option.getD_some]

theorem contractedDrawing_compatible {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsCompatible source := by
  have scaled := isCompatible_scale (polygonalScale_positive drawing) source drawing planar.1.1
  have sameSize : (contractedDrawing source drawing).gridSize=(drawing.scale (polygonalScale drawing)).gridSize := by
    rw [contractedDrawing_gridSize,gridSize_scale (polygonalScale_positive drawing)]
  unfold IsCompatible
  refine ⟨scaled.1,?_,?_,?_,?_,?_⟩
  · simpa only [contractedDrawing,scale] using scaled.2.1
  · simp only [contractedDrawing,List.length_map,List.length_zipIdx]
  · simpa only [contractedDrawing,scale] using scaled.2.2.2.1
  · intro position member
    have bounds := scaled.2.2.2.2.1 position member
    simpa only [PositionInFundamentalSquare,sameSize] using bounds
  · intro parent member
    rw [contractedDrawing_edgeRoute member,contractedDrawing_vertexPosition,contractedDrawing_vertexPosition]
    have endpoints := contractedRoute_endpoints planar localDrawing localGraph degree member
    constructor
    · exact endpoints.1
    · simpa only [contractedDrawing_periodTranslation] using endpoints.2

theorem contractedDrawing_routesSimple {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).RealRoutesAreSimple := by
  intro route member
  obtain ⟨parent,parentMember,rfl⟩ := List.mem_map.mp member
  exact contractedRoute_simple planar localDrawing localGraph degree parentMember

theorem refinedPiece_orthogonal {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) {record : (Nat × Nat) × PeriodicEdge (PeriodicGraph.BendSubdivision.Vertex V)}
    (member : record ∈ records source drawing (bendRefinementFactor drawing)) :
    OrthogonalPolyline (refinedPiece source drawing record) := by
  have outputPlanar := orthogonalSubdivision_planar planar localDrawing localGraph degree
  have routeMember := edgeRoute_mem_of_compatible outputPlanar.1.1 (recordIndex_tagged member)
  have orthogonal := (isOrthogonal_iff_routes _).mp (orthogonalSubdivision_orthogonal planar localDrawing localGraph degree)
    _ routeMember
  exact orthogonal.translate _

theorem contractedDrawing_orthogonal {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsOrthogonal := by
  apply (isOrthogonal_iff_routes _).mpr
  intro route member
  obtain ⟨parent,parentMember,rfl⟩ := List.mem_map.mp member
  apply GridPolyline.joinRouteChain_orthogonal (parentPieces_chain planar localDrawing localGraph degree parentMember)
    (fun route member => (parentPieces_openSimple planar localDrawing localGraph degree parentMember member).1)
  intro piece pieceMember
  obtain ⟨record,recordMember,rfl⟩ := List.mem_map.mp pieceMember
  exact refinedPiece_orthogonal planar localDrawing localGraph degree (parentRecord_mem parentMember recordMember)

theorem contractedDrawing_gridSize_bound {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : (contractedDrawing source drawing).gridSize≤865075200*drawing.gridSize^6 := by
  have bound := orthogonalSubdivision_gridSize_bound source drawing
  rw [orthogonalSubdivision_gridSize] at bound
  rw [contractedDrawing_gridSize,polygonalScale]
  simpa only [Nat.mul_assoc] using bound

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
