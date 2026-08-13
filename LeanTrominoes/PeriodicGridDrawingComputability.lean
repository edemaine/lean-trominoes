/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computability
import LeanTrominoes.OrthogonalDrawing
import LeanTrominoes.PeriodicGridDrawingEndpointContacts
import LeanTrominoes.PeriodicThreeDMComputability
import LeanTrominoes.PeriodicThreeDMGraph
import LeanTrominoes.PeriodicThreeSATThreeComputability

/-!
# Computability of periodic grid-drawing data

This module supplies canonical encodings and primitive-recursive data
operations for the finite periodic graph drawings used by the drawing
certificate.  Geometric predicates and the combined verifier are handled in
the subsequent certificate-computability module.
-/

noncomputable section

namespace LeanTrominoes

namespace GridSegment

theorem equivData_primrec : Primrec GridSegment.equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec GridSegment.equivData.symm :=
  Primrec.of_equiv_symm

theorem start_primrec : Primrec GridSegment.start :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem finish_primrec : Primrec GridSegment.finish :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec : Primrec₂ fun start finish : Cell =>
    GridSegment.mk start finish :=
  (equivData_symm_primrec.comp₂ Primrec₂.pair).of_eq fun _ _ => rfl

end GridSegment

namespace IndexedGridSegment

/-- Product representation used by the standard computability encoding. -/
def equivData : IndexedGridSegment ≃ Nat × Nat × GridSegment where
  toFun indexed :=
    (indexed.routeIndex, indexed.segmentIndex, indexed.segment)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv indexed := by cases indexed; rfl
  right_inv data := by rcases data with ⟨route, segment, geometry⟩; rfl

noncomputable instance : Primcodable IndexedGridSegment :=
  Primcodable.ofEquiv (Nat × Nat × GridSegment) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem routeIndex_primrec : Primrec IndexedGridSegment.routeIndex :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem segmentIndex_primrec : Primrec IndexedGridSegment.segmentIndex :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem segment_primrec : Primrec IndexedGridSegment.segment :=
  ((Primrec.snd.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec : Primrec fun data : Nat × Nat × GridSegment =>
    IndexedGridSegment.mk data.1 data.2.1 data.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end IndexedGridSegment

namespace IndexedRoutePoint

/-- Product representation used by the standard computability encoding. -/
def equivData : IndexedRoutePoint ≃ Nat × Nat × Nat × Cell where
  toFun indexed :=
    (indexed.routeIndex, indexed.pointIndex,
      indexed.routeLength, indexed.point)
  invFun data := ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  left_inv indexed := by cases indexed; rfl
  right_inv data :=
    by rcases data with ⟨route, point, length, location⟩; rfl

noncomputable instance : Primcodable IndexedRoutePoint :=
  Primcodable.ofEquiv (Nat × Nat × Nat × Cell) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem routeIndex_primrec : Primrec IndexedRoutePoint.routeIndex :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem pointIndex_primrec : Primrec IndexedRoutePoint.pointIndex :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem routeLength_primrec : Primrec IndexedRoutePoint.routeLength :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    equivData_primrec).of_eq fun _ => rfl

theorem point_primrec : Primrec IndexedRoutePoint.point :=
  ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp
    equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec : Primrec fun data : Nat × Nat × Nat × Cell =>
    IndexedRoutePoint.mk data.1 data.2.1 data.2.2.1 data.2.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end IndexedRoutePoint

namespace PeriodicGridDrawing

theorem equivData_primrec : Primrec PeriodicGridDrawing.equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec PeriodicGridDrawing.equivData.symm :=
  Primrec.of_equiv_symm

theorem gridSizePred_primrec : Primrec PeriodicGridDrawing.gridSizePred :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem vertexPositions_primrec :
    Primrec PeriodicGridDrawing.vertexPositions :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem edgeRoutes_primrec : Primrec PeriodicGridDrawing.edgeRoutes :=
  ((Primrec.snd.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem gridSize_primrec : Primrec PeriodicGridDrawing.gridSize := by
  exact (Primrec.succ.comp gridSizePred_primrec).of_eq fun _ => rfl

theorem periodTranslation_primrec :
    Primrec₂ PeriodicGridDrawing.periodTranslation := by
  unfold PeriodicGridDrawing.periodTranslation
  exact Computability.cell_scale_primrec.comp₂
    ((Computability.int_ofNat_primrec.comp gridSize_primrec).comp₂
      Primrec₂.left)
    Primrec₂.right

theorem edgeRoute_primrec : Primrec₂ PeriodicGridDrawing.edgeRoute := by
  unfold PeriodicGridDrawing.edgeRoute
  exact (Primrec.list_getD ([] : List Cell)).comp₂
    (edgeRoutes_primrec.comp₂ Primrec₂.left) Primrec₂.right

end PeriodicGridDrawing

/-- Consecutive grid-polyline segments are primitive recursive data. -/
theorem gridPolylineSegments_primrec : Primrec gridPolylineSegments := by
  have step : Primrec₂ fun (_points : List Cell)
      (state : Cell × List Cell × List GridSegment) =>
      match state.2.1.head? with
      | none => []
      | some second => GridSegment.mk state.1 second :: state.2.2 := by
    change Primrec fun combined :
        List Cell × (Cell × List Cell × List GridSegment) =>
      match combined.2.2.1.head? with
      | none => []
      | some second =>
          GridSegment.mk combined.2.1 second :: combined.2.2.2
    have next : Primrec (fun combined :
        List Cell × (Cell × List Cell × List GridSegment) =>
        (combined.2.2.1.head? : Option Cell)) :=
      Primrec.list_head?.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    exact (Primrec.option_casesOn next (Primrec.const [])
      (Primrec.list_cons.comp₂
        (GridSegment.mk_primrec.comp₂
          ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
          Primrec₂.right)
        ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp₂
          Primrec₂.left))).of_eq fun combined => by
            cases combined.2.2.1.head? <;> rfl
  have recursion := Primrec.list_rec
    (f := fun points : List Cell => points)
    (g := fun _ => ([] : List GridSegment))
    (h := fun _ state =>
      match state.2.1.head? with
      | none => []
      | some second => GridSegment.mk state.1 second :: state.2.2)
    Primrec.id (Primrec.const []) step
  exact recursion.of_eq fun points => by
    induction points with
    | nil => rfl
    | cons first rest induction =>
        cases rest with
        | nil => rfl
        | cons second tail =>
            simp only [List.head?_cons, gridPolylineSegments]
            exact congrArg (GridSegment.mk first second :: ·) induction

namespace PeriodicGridDrawing

theorem indexedSegments_primrec :
    Primrec PeriodicGridDrawing.indexedSegments := by
  have taggedRoutes : Primrec fun drawing : PeriodicGridDrawing =>
      drawing.edgeRoutes.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp edgeRoutes_primrec
  apply Primrec.list_flatMap taggedRoutes
  change Primrec fun input :
      PeriodicGridDrawing × (List Cell × Nat) =>
      (gridPolylineSegments input.2.1).zipIdx.map fun taggedSegment =>
        IndexedGridSegment.mk input.2.2 taggedSegment.2 taggedSegment.1
  have taggedSegments : Primrec fun input :
      PeriodicGridDrawing × (List Cell × Nat) =>
      (gridPolylineSegments input.2.1).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (gridPolylineSegments_primrec.comp
        (Primrec.fst.comp Primrec.snd))
  apply Primrec.list_map taggedSegments
  change Primrec₂ fun
      (input : PeriodicGridDrawing × (List Cell × Nat))
      (taggedSegment : GridSegment × Nat) =>
      IndexedGridSegment.mk input.2.2 taggedSegment.2 taggedSegment.1
  exact IndexedGridSegment.mk_primrec.comp
    (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)))

theorem indexedRoutePoints_primrec :
    Primrec PeriodicGridDrawing.indexedRoutePoints := by
  have taggedRoutes : Primrec fun drawing : PeriodicGridDrawing =>
      drawing.edgeRoutes.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp edgeRoutes_primrec
  apply Primrec.list_flatMap taggedRoutes
  change Primrec fun input :
      PeriodicGridDrawing × (List Cell × Nat) =>
      input.2.1.zipIdx.map fun taggedPoint =>
        IndexedRoutePoint.mk input.2.2 taggedPoint.2
          input.2.1.length taggedPoint.1
  have taggedPoints : Primrec fun input :
      PeriodicGridDrawing × (List Cell × Nat) =>
      input.2.1.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  apply Primrec.list_map taggedPoints
  change Primrec₂ fun
      (input : PeriodicGridDrawing × (List Cell × Nat))
      (taggedPoint : Cell × Nat) =>
      IndexedRoutePoint.mk input.2.2 taggedPoint.2
        input.2.1.length taggedPoint.1
  exact IndexedRoutePoint.mk_primrec.comp
    (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.pair
          ((Primrec.list_length.comp
            (Primrec.fst.comp Primrec.snd)).comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))))

end PeriodicGridDrawing

namespace PeriodicThreeDMVertex

/-- Sum representation used by the standard computability encoding. -/
def equivData : PeriodicThreeDMVertex ≃ Sum Nat (Gadget.WireColor × Nat) where
  toFun
    | .triple index => .inl index
    | .element color atom => .inr (color, atom)
  invFun
    | .inl index => .triple index
    | .inr data => .element data.1 data.2
  left_inv vertex := by cases vertex <;> rfl
  right_inv data := by cases data <;> rfl

noncomputable instance : Primcodable PeriodicThreeDMVertex :=
  Primcodable.ofEquiv (Sum Nat (Gadget.WireColor × Nat)) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem triple_primrec : Primrec PeriodicThreeDMVertex.triple :=
  equivData_symm_primrec.comp Primrec.sumInl

theorem element_primrec : Primrec₂ PeriodicThreeDMVertex.element :=
  equivData_symm_primrec.comp₂
    (Primrec.sumInr.comp₂ Primrec₂.pair)

end PeriodicThreeDMVertex

namespace PeriodicEdge

theorem equivData_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicEdge.equivData Vertex) :=
  Primrec.of_equiv

theorem equivData_symm_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicEdge.equivData Vertex).symm :=
  Primrec.of_equiv_symm

theorem source_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicEdge.source Vertex) :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem target_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicEdge.target Vertex) :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem offset_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicEdge.offset Vertex) :=
  ((Primrec.snd.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

end PeriodicEdge

namespace PeriodicGraph

theorem equivData_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicGraph.equivData Vertex) :=
  Primrec.of_equiv

theorem equivData_symm_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicGraph.equivData Vertex).symm :=
  Primrec.of_equiv_symm

theorem vertices_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicGraph.vertices Vertex) :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem edges_primrec {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@PeriodicGraph.edges Vertex) :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

end PeriodicGraph

namespace PeriodicThreeDMTriple

/-- Selecting the reference of a finite wire color is primitive recursive. -/
theorem reference_primrec :
    Primrec₂ PeriodicThreeDMTriple.reference := by
  change Primrec fun input : PeriodicThreeDMTriple × Gadget.WireColor =>
    input.1.reference input.2
  let is (color : Gadget.WireColor) : PrimrecPred fun input :
      PeriodicThreeDMTriple × Gadget.WireColor => input.2 = color :=
    Primrec.eq.comp Primrec.snd (Primrec.const color)
  exact (Primrec.ite (is .red)
    (PeriodicThreeDMTriple.red_primrec.comp Primrec.fst)
    (Primrec.ite (is .green)
      (PeriodicThreeDMTriple.green_primrec.comp Primrec.fst)
      (PeriodicThreeDMTriple.blue_primrec.comp Primrec.fst))).of_eq
        fun input => by cases input.2 <;> rfl

end PeriodicThreeDMTriple

namespace PeriodicThreeDM

/-- Selecting the number of elements of a finite wire color is primitive
recursive. -/
theorem elementCount_primrec :
    Primrec₂ PeriodicThreeDM.elementCount := by
  change Primrec fun input : PeriodicThreeDM × Gadget.WireColor =>
    input.1.elementCount input.2
  let is (color : Gadget.WireColor) : PrimrecPred fun input :
      PeriodicThreeDM × Gadget.WireColor => input.2 = color :=
    Primrec.eq.comp Primrec.snd (Primrec.const color)
  exact (Primrec.ite (is .red)
    (PeriodicThreeDM.redCount_primrec.comp Primrec.fst)
    (Primrec.ite (is .green)
      (PeriodicThreeDM.greenCount_primrec.comp Primrec.fst)
      (PeriodicThreeDM.blueCount_primrec.comp Primrec.fst))).of_eq
        fun input => by cases input.2 <;> rfl

theorem coloredElementVertices_primrec :
    Primrec₂ PeriodicThreeDM.coloredElementVertices := by
  change Primrec fun input : PeriodicThreeDM × Gadget.WireColor =>
    input.1.coloredElementVertices input.2
  have atoms : Primrec fun input : PeriodicThreeDM × Gadget.WireColor =>
      List.range (input.1.elementCount input.2) :=
    Primrec.list_range.comp elementCount_primrec
  exact Primrec.list_map atoms
    (PeriodicThreeDMVertex.element_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

theorem elementVertices_primrec :
    Primrec PeriodicThreeDM.elementVertices := by
  have red := coloredElementVertices_primrec.comp
    Primrec.id (Primrec.const Gadget.WireColor.red)
  have green := coloredElementVertices_primrec.comp
    Primrec.id (Primrec.const Gadget.WireColor.green)
  have blue := coloredElementVertices_primrec.comp
    Primrec.id (Primrec.const Gadget.WireColor.blue)
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp red green) blue).of_eq fun _ => rfl

theorem tripleVertices_primrec :
    Primrec PeriodicThreeDM.tripleVertices := by
  have indices : Primrec fun problem : PeriodicThreeDM =>
      List.range problem.triples.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicThreeDM.triples_primrec)
  exact Primrec.list_map indices
    (PeriodicThreeDMVertex.triple_primrec.comp Primrec.snd).to₂

/-- Constructing one colored incidence edge is primitive recursive. -/
theorem incidenceEdge_primrec : Primrec fun input :
    (Nat × PeriodicThreeDMTriple) × Gadget.WireColor =>
    incidenceEdge input.1.1 input.1.2 input.2 := by
  let reference : Primrec fun input :
      (Nat × PeriodicThreeDMTriple) × Gadget.WireColor =>
      input.1.2.reference input.2 :=
    PeriodicThreeDMTriple.reference_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  let source : Primrec fun input :
      (Nat × PeriodicThreeDMTriple) × Gadget.WireColor =>
      PeriodicThreeDMVertex.triple input.1.1 :=
    PeriodicThreeDMVertex.triple_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  let target : Primrec fun input :
      (Nat × PeriodicThreeDMTriple) × Gadget.WireColor =>
      PeriodicThreeDMVertex.element input.2
        (input.1.2.reference input.2).atom :=
    PeriodicThreeDMVertex.element_primrec.comp Primrec.snd
      (PeriodicThreeDMReference.atom_primrec.comp reference)
  let offset : Primrec fun input :
      (Nat × PeriodicThreeDMTriple) × Gadget.WireColor =>
      (input.1.2.reference input.2).offset :=
    PeriodicThreeDMReference.offset_primrec.comp reference
  exact (PeriodicEdge.equivData_symm_primrec.comp
    (Primrec.pair source (Primrec.pair target offset))).of_eq fun _ => rfl

theorem tripleIncidenceEdges_primrec :
    Primrec₂ PeriodicThreeDM.tripleIncidenceEdges := by
  change Primrec fun input : Nat × PeriodicThreeDMTriple =>
    tripleIncidenceEdges input.1 input.2
  exact Primrec.list_map (Primrec.const incidenceColors)
    incidenceEdge_primrec.to₂

theorem incidenceGraph_primrec :
    Primrec PeriodicThreeDM.incidenceGraph := by
  have vertices : Primrec fun problem : PeriodicThreeDM =>
      problem.tripleVertices ++ problem.elementVertices :=
    Primrec.list_append.comp tripleVertices_primrec
      elementVertices_primrec
  have taggedTriples : Primrec fun problem : PeriodicThreeDM =>
      problem.triples.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicThreeDM.triples_primrec
  have edges : Primrec fun problem : PeriodicThreeDM =>
      problem.triples.zipIdx.flatMap fun tagged =>
        tripleIncidenceEdges tagged.2 tagged.1 := by
    apply Primrec.list_flatMap taggedTriples
    exact (tripleIncidenceEdges_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)).to₂
  exact (PeriodicGraph.equivData_symm_primrec.comp
    (Primrec.pair vertices edges)).of_eq fun _ => rfl

end PeriodicThreeDM

end LeanTrominoes
