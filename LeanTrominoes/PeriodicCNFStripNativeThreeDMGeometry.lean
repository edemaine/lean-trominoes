/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMSourceCoordinates
import LeanTrominoes.PeriodicCNFStripNativeThreeDMRoutes
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDrawingPresentationBridge
import LeanTrominoes.PeriodicGridDrawingVertexCoverage
import LeanTrominoes.OrthogonalRouteEndpointDisplacement

/-! # Geometric endpoint contracts for the native 3DM incidence compiler -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Gadget PeriodicThreeDM PeriodicOrthocrossing DelimitedDirectionDisplacement
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

private theorem tripleVertex_index (p : PeriodicThreeDM) (n : Nat) (hn : n < p.triples.length) :
    p.incidenceGraph.vertices.idxOf (.triple n) = n := by
  have bound : n < p.incidenceGraph.vertices.length := by
    simp only [incidenceGraph,List.length_append,tripleVertices,List.length_map,List.length_range]
    omega
  have value : p.incidenceGraph.vertices[n] = .triple n := by
    simp [incidenceGraph,tripleVertices,List.getElem_append_left,hn]
  have index := p.incidenceGraph_vertices_nodup.idxOf_getElem n bound
  rw [value] at index
  exact index

private theorem tripleVertex_position (p : PeriodicThreeDM) (d : PeriodicGridDrawing)
    (first rest : List Cell) (positions : d.vertexPositions = first ++ rest)
    (len : first.length = p.triples.length) (n : Nat) (hn : n < p.triples.length) :
    d.vertexPosition p.incidenceGraph (.triple n) = first.getD n (0,0) := by
  rw [PeriodicGridDrawing.vertexPosition,tripleVertex_index p n hn,positions]
  have h : n < first.length := by omega
  rw [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_append_left h,List.getD_eq_getElem _ _ h]

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeThreeDMGeometryStack (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

abbrev nativeThreeDMDrawing (s : List encoding.Γ) :=
  horizontalThreeDMDrawingComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)

abbrev nativeThreeDMReference (s : List encoding.Γ) (tag : IncidenceTag) :=
  ((nativeThreeDMProblem decider s).triples.getD tag.tripleIndex default).reference tag.color

abbrev nativeThreeDMTargetPoint (s : List encoding.Γ) (tag : IncidenceTag) :=
  (nativeThreeDMDrawing decider s).vertexPosition (nativeThreeDMProblem decider s).incidenceGraph
    (.element tag.color (nativeThreeDMReference decider s tag).atom)

theorem nativeThreeDMDrawing_compatible (s : List encoding.Γ) :
    (nativeThreeDMDrawing decider s).IsCompatible (nativeThreeDMProblem decider s).incidenceGraph := by
  rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_eq_presentationDrawing,
    nativeThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact (presentation _).toPlanarPresentation.compatible

theorem nativeThreeDMDrawing_orthogonal (s : List encoding.Γ) : (nativeThreeDMDrawing decider s).IsOrthogonal := by
  rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_eq_presentationDrawing]
  exact (presentation _).toPlanarPresentation.orthogonal

theorem nativeThreeDMDrawing_period (s : List encoding.Γ) :
    (nativeThreeDMDrawing decider s).gridSize = nativeThreeDMPeriod decider s := by
  simp only [nativeThreeDMDrawing,PeriodicGridDrawing.gridSize,
    horizontalThreeDMDrawingComputed_gridSizePred,horizontalThreeDMGridSizePredComputed]
  exact Nat.sub_add_cancel (nativeThreeDMPeriod_positive decider s)

theorem nativeThreeDMRoute_eq_edgeRoute (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) :
    (nativeThreeDMDrawing decider s).edgeRoute ((nativeThreeDMProblem decider s).incidenceRouteIndex tag) =
      nativeThreeDMRoute decider s tag := by
  simp only [nativeThreeDMDrawing,PeriodicGridDrawing.edgeRoute,
    horizontalThreeDMDrawingComputed_edgeRoutes,horizontalThreeDMEdgeRoutesComputed,
    horizontalThreeDMIncidenceTagsComputed,incidenceRouteIndex,List.getD_eq_getElem?_getD,
    List.getElem?_map,List.getElem?_idxOf ht,Option.map_some,Option.getD_some]

theorem nativeThreeDMSourcePoint_eq_vertex (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) :
    (nativeThreeDMDrawing decider s).vertexPosition (nativeThreeDMProblem decider s).incidenceGraph
      (.triple tag.tripleIndex) = nativeThreeDMSourcePoint decider s tag := by
  apply tripleVertex_position (nativeThreeDMProblem decider s) (nativeThreeDMDrawing decider s)
    (nativeThreeDMTriplePositions decider s)
    (horizontalThreeDMColoredPositionsComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))
  · rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_vertexPositions]
    rfl
  · exact nativeThreeDMTriplePositions_length decider s
  · exact incidenceTag_tripleIndex_lt (nativeThreeDMProblem decider s) ht

theorem nativeThreeDMRoute_endpoints (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) :
    (nativeThreeDMRoute decider s tag).head? = some (nativeThreeDMSourcePoint decider s tag) ∧
    (nativeThreeDMRoute decider s tag).getLast? = some (Cell.add (nativeThreeDMTargetPoint decider s tag)
      (Cell.scale (nativeThreeDMPeriod decider s) (nativeThreeDMReference decider s tag).offset)) := by
  have h := (nativeThreeDMDrawing_compatible decider s).2.2.2.2.2
    ((nativeThreeDMProblem decider s).incidenceEdgeAt tag,(nativeThreeDMProblem decider s).incidenceRouteIndex tag)
    (incidenceEdge_zipIdx_mem (nativeThreeDMProblem decider s) ht)
  dsimp only at h
  rw [nativeThreeDMRoute_eq_edgeRoute decider s tag ht] at h
  simp only [incidenceEdgeAt,incidenceEdge,PeriodicGridDrawing.periodTranslation,
    nativeThreeDMDrawing_period,nativeThreeDMSourcePoint_eq_vertex decider s tag ht] at h
  exact h

theorem nativeThreeDMRoute_orthogonal (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) : OrthogonalPolyline (nativeThreeDMRoute decider s tag) := by
  have member : nativeThreeDMRoute decider s tag ∈ (nativeThreeDMDrawing decider s).edgeRoutes := by
    simp only [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_edgeRoutes,
      horizontalThreeDMEdgeRoutesComputed,horizontalThreeDMIncidenceTagsComputed]
    exact List.mem_map.mpr ⟨tag,ht,rfl⟩
  exact (PeriodicGridDrawing.isOrthogonal_iff_routes (nativeThreeDMDrawing decider s)).1
    (nativeThreeDMDrawing_orthogonal decider s) (nativeThreeDMRoute decider s tag) member

theorem nativeThreeDMTargetPoint_inside (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) :
    (nativeThreeDMDrawing decider s).PositionInFundamentalSquare (nativeThreeDMTargetPoint decider s tag) := by
  have compatible := nativeThreeDMDrawing_compatible decider s
  apply compatible.2.2.2.2.1
  apply compatible.vertexPosition_mem
  have he := (nativeThreeDMElement_mem decider s _).1 (nativeThreeDMIncidenceElement_mem decider s tag ht)
  cases hc : tag.color <;>
    simp [PeriodicThreeDM.incidenceGraph,elementVertices,coloredElementVertices,incidenceElement,
      nativeThreeDMReference,hc] at he ⊢ <;> exact Or.inr (by simp [he])

theorem nativeThreeDMOffset_recovery (s : List encoding.Γ) (tag : IncidenceTag)
    (ht : tag ∈ nativeThreeDMIncidences decider s) (horizontal : Bool) :
    (component horizontal (nativeThreeDMSourcePoint decider s tag) +
      displacement horizontal (unitSubdivisionDirections (nativeThreeDMRoute decider s tag))) /
      (nativeThreeDMPeriod decider s:Int) = component horizontal (nativeThreeDMReference decider s tag).offset := by
  have endpoints := nativeThreeDMRoute_endpoints decider s tag ht
  apply translatedEndpoint_offset horizontal _ (nativeThreeDMPeriod_positive decider s) _ _ _ _
    endpoints.1 endpoints.2 (nativeThreeDMRoute_orthogonal decider s tag ht)
  have inside := nativeThreeDMTargetPoint_inside decider s tag ht
  rw [PeriodicGridDrawing.PositionInFundamentalSquare,nativeThreeDMDrawing_period] at inside
  cases horizontal <;> simp only [component] <;> omega

end LeanTrominoes.PeriodicCNFStripReduction
end
