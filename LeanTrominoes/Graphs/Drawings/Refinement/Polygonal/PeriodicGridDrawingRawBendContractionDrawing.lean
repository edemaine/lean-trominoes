/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendContractionEndpoints
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineSymmetries

/-! # The original periodic graph drawn by joining its refined subedges -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicOrthocrossing OrthogonalDrawingRefinement

def cubicFactor (drawing : PeriodicGridDrawing) : Nat :=
  Cubic.rasterFactor drawing.gridSize*Cubic.coreFactor drawing.gridSize

theorem cubicFactor_positive (drawing : PeriodicGridDrawing) : 0 < cubicFactor drawing :=
  Nat.mul_pos (Cubic.rasterFactor_positive _) (Cubic.coreFactor_positive _)

theorem cubicFactor_cast (drawing : PeriodicGridDrawing) : (cubicFactor drawing : Int)=cubicScale drawing := by
  simp only [cubicFactor,cubicScale,Nat.cast_mul]


noncomputable def contractedDrawing {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing where
  gridSizePred := cubicFactor drawing*drawing.gridSize-1
  vertexPositions := drawing.vertexPositions.map (Cell.scale (cubicFactor drawing))
  edgeRoutes := source.edges.zipIdx.map (contractedRoute source drawing)

theorem contractedDrawing_gridSize {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) :
    (contractedDrawing source drawing).gridSize=cubicFactor drawing*drawing.gridSize := by
  have positive : 0 < cubicFactor drawing*drawing.gridSize :=
    Nat.mul_pos (cubicFactor_positive drawing) (Nat.zero_lt_succ drawing.gridSizePred)
  change cubicFactor drawing*drawing.gridSize-1+1=_
  omega

theorem contractedDrawing_periodTranslation {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (copy : Cell) :
    (contractedDrawing source drawing).periodTranslation copy=Cell.scale (cubicScale drawing*drawing.gridSize) copy := by
  rw [periodTranslation,contractedDrawing_gridSize,Nat.cast_mul,cubicFactor_cast]

theorem contractedDrawing_vertexPosition {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (vertex : V) :
    (contractedDrawing source drawing).vertexPosition source vertex=
      Cell.scale (cubicFactor drawing) (drawing.vertexPosition source vertex) := by
  simp only [vertexPosition,contractedDrawing]
  change (drawing.vertexPositions.map (Cell.scale (cubicFactor drawing))).getD
    (source.vertices.idxOf vertex) (Cell.scale (cubicFactor drawing) (0,0))=_
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
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsCompatible source := by
  have scaled := isCompatible_scale (cubicFactor_positive drawing) source drawing planar.1.1
  have sameSize : (contractedDrawing source drawing).gridSize=(drawing.scale (cubicFactor drawing)).gridSize := by
    rw [contractedDrawing_gridSize,gridSize_scale (cubicFactor_positive drawing)]
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
    have endpoints := contractedRoute_endpoints planar degree member
    constructor
    · simpa only [cubicFactor_cast] using endpoints.1
    · simpa only [contractedDrawing_periodTranslation,cubicFactor_cast] using endpoints.2

theorem contractedDrawing_routesSimple {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).RealRoutesAreSimple := by
  intro route member
  obtain ⟨parent,parentMember,rfl⟩ := List.mem_map.mp member
  exact contractedRoute_simple planar localDrawing localGraph degree parentMember

theorem refinedPiece_orthogonal {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {record : (Nat × Nat) × PeriodicEdge (PeriodicGraph.BendSubdivision.Vertex V)}
    (member : record ∈ records source drawing) :
    OrthogonalPolyline (refinedPiece source drawing record) :=
  (pieceRoute_orthogonal planar (recordIndex_tagged member)).translate _

theorem contractedDrawing_orthogonal {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsOrthogonal := by
  apply (isOrthogonal_iff_routes _).mpr
  intro route member
  obtain ⟨parent,parentMember,rfl⟩ := List.mem_map.mp member
  apply GridPolyline.joinRouteChain_orthogonal (parentPieces_chain planar parentMember)
    (fun route member => (parentPieces_openSimple planar degree parentMember member).1)
  intro piece pieceMember
  obtain ⟨record,recordMember,rfl⟩ := List.mem_map.mp pieceMember
  exact refinedPiece_orthogonal planar (parentRecord_mem parentMember recordMember)

theorem contractedDrawing_gridSize_bound {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : (contractedDrawing source drawing).gridSize≤84480*drawing.gridSize^3 := by
  rw [contractedDrawing_gridSize]
  have bounds := Cubic.refined_period_le_cubic (show 0 < drawing.gridSize from Nat.zero_lt_succ drawing.gridSizePred)
  simpa only [cubicFactor,Cubic.refinementFactor,Nat.mul_comm] using bounds

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
