/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificateComputability

/-! # Effective finite certificates for arbitrary periodic graph drawings -/
noncomputable section
namespace LeanTrominoes.PeriodicGridDrawing.FiniteCertificate
open PeriodicThreeDM.FiniteDrawingCertificate
variable {V : Type} [Primcodable V] [DecidableEq V]
set_option maxHeartbeats 600000

private abbrev RoutesMatchTaggedInput (V : Type) :=
  (PeriodicGraph V × PeriodicGridDrawing) ×
    (PeriodicEdge V × Nat)

private def routesMatchTaggedRoute
    (combined : RoutesMatchTaggedInput V) : List Cell :=
  combined.1.2.edgeRoute combined.2.2

omit [DecidableEq V] in
private theorem routesMatchTaggedRoute_primrec :
    Primrec (routesMatchTaggedRoute (V := V)) := by
  unfold routesMatchTaggedRoute
  exact PeriodicGridDrawing.edgeRoute_primrec.comp
    (Primrec.snd.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd)

private def routesMatchTaggedPosition (source : Bool)
    (combined : RoutesMatchTaggedInput V) : Cell :=
  combined.1.2.vertexPosition combined.1.1
    (if source then combined.2.1.source else combined.2.1.target)

private theorem routesMatchTaggedPosition_primrec (source : Bool) :
    Primrec (routesMatchTaggedPosition (V := V) source) := by
  unfold routesMatchTaggedPosition PeriodicGridDrawing.vertexPosition
  let graph : Primrec fun combined : RoutesMatchTaggedInput V =>
      combined.1.1 :=
    Primrec.id.comp
      (Primrec.fst.comp Primrec.fst)
  let vertex : Primrec fun combined : RoutesMatchTaggedInput V =>
      if source then combined.2.1.source else combined.2.1.target := by
    cases source
    · exact PeriodicEdge.target_primrec.comp
        (Primrec.fst.comp Primrec.snd)
    · exact PeriodicEdge.source_primrec.comp
        (Primrec.fst.comp Primrec.snd)
  exact (Primrec.list_getD (0, 0)).comp
    (PeriodicGridDrawing.vertexPositions_primrec.comp
      (Primrec.snd.comp Primrec.fst))
    (Primrec.list_idxOf.comp vertex
      (PeriodicGraph.vertices_primrec.comp graph))

private def routesMatchTaggedTranslation
    (combined : RoutesMatchTaggedInput V) : Cell :=
  combined.1.2.periodTranslation combined.2.1.offset

omit [DecidableEq V] in
private theorem routesMatchTaggedTranslation_primrec :
    Primrec (routesMatchTaggedTranslation (V := V)) := by
  unfold routesMatchTaggedTranslation
  exact PeriodicGridDrawing.periodTranslation_primrec.comp
    (Primrec.snd.comp Primrec.fst)
    (PeriodicEdge.offset_primrec.comp
      (Primrec.fst.comp Primrec.snd))

private def routesMatchTaggedPredicate
    (combined : RoutesMatchTaggedInput V) : Prop :=
  (routesMatchTaggedRoute combined).head? =
      some (routesMatchTaggedPosition true combined) ∧
    (routesMatchTaggedRoute combined).getLast? =
      some (Cell.add (routesMatchTaggedPosition false combined)
        (routesMatchTaggedTranslation combined))

private instance : DecidablePred (routesMatchTaggedPredicate (V := V)) :=
  fun combined => by
    unfold routesMatchTaggedPredicate
    infer_instance

private theorem routesMatchTaggedPredicate_primrec :
    PrimrecPred (routesMatchTaggedPredicate (V := V)) := by
  let expectedTarget : Primrec fun combined : RoutesMatchTaggedInput V =>
      Cell.add (routesMatchTaggedPosition false combined)
        (routesMatchTaggedTranslation combined) :=
    Computability.cell_add_primrec.comp
      (routesMatchTaggedPosition_primrec false)
      routesMatchTaggedTranslation_primrec
  exact ((Primrec.eq.comp
    (Primrec.list_head?.comp routesMatchTaggedRoute_primrec)
    (Primrec.option_some.comp (routesMatchTaggedPosition_primrec true))).and
    (Primrec.eq.comp
      (Primrec.list_head?.comp
        (Primrec.list_reverse.comp routesMatchTaggedRoute_primrec))
      (Primrec.option_some.comp expectedTarget))).of_eq fun combined => by
        simp [routesMatchTaggedPredicate]

theorem routesMatch_primrec : PrimrecRel fun
    (problem : PeriodicGraph V) (drawing : PeriodicGridDrawing) =>
    drawing.RoutesMatch problem := by
  change PrimrecPred fun input : PeriodicGraph V × PeriodicGridDrawing =>
    input.2.RoutesMatch input.1
  let taggedEdges : Primrec fun input :
      PeriodicGraph V × PeriodicGridDrawing =>
      input.1.edges.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicGraph.edges_primrec.comp
        (Primrec.id.comp Primrec.fst))
  have property : PrimrecPred fun input :
      PeriodicGraph V × PeriodicGridDrawing =>
      ∀ tagged ∈ input.1.edges.zipIdx,
        routesMatchTaggedPredicate (input, tagged) := by
    apply primrecPred_forall_mem taggedEdges
    exact routesMatchTaggedPredicate_primrec.primrecRel
  exact property.of_eq fun input => by
    simp [PeriodicGridDrawing.RoutesMatch, routesMatchTaggedPredicate,
      routesMatchTaggedRoute, routesMatchTaggedPosition,
      routesMatchTaggedTranslation]


def Compatible (g : PeriodicGraph V) (d : PeriodicGridDrawing) : Prop :=
  d.vertexPositions.length = g.vertices.length ∧ d.edgeRoutes.length = g.edges.length ∧
  d.vertexPositions.Nodup ∧
  (∀ p ∈ d.vertexPositions, d.PositionInFundamentalSquare p) ∧ d.RoutesMatch g

theorem compatible_primrec : PrimrecRel (Compatible (V := V)) := by
  let positions := PeriodicGridDrawing.vertexPositions_primrec.comp
    (Primrec.snd : Primrec (fun p : PeriodicGraph V × PeriodicGridDrawing => p.2))
  have nodup : PrimrecPred fun p : PeriodicGraph V × PeriodicGridDrawing => p.2.vertexPositions.Nodup :=
    (Primrec.eq.comp (PeriodicThreeSATThree.dedup_primrec.comp positions) positions).of_eq
      fun _ => List.dedup_eq_self
  have bounds : PrimrecPred fun p : PeriodicGraph V × PeriodicGridDrawing =>
      ∀ q ∈ p.2.vertexPositions, p.2.PositionInFundamentalSquare q :=
    primrecPred_forall_mem positions
      (positionInFundamentalSquare_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (Primrec.eq.comp (Primrec.list_length.comp positions)
    (Primrec.list_length.comp (PeriodicGraph.vertices_primrec.comp Primrec.fst))).and
    ((Primrec.eq.comp (Primrec.list_length.comp (PeriodicGridDrawing.edgeRoutes_primrec.comp Primrec.snd))
      (Primrec.list_length.comp (PeriodicGraph.edges_primrec.comp Primrec.fst))).and
    (nodup.and (bounds.and (routesMatch_primrec.comp Primrec.fst Primrec.snd))))

def Geometry (d : PeriodicGridDrawing) : Prop :=
  endpointBoundsCheck d = true ∧
  d.expandedFiniteRoutesAvoidInteriors = true ∧
  d.finiteVerticesAvoidRouteInteriors = true ∧
  d.expandedFiniteRoutesHaveDisjointInteriors = true

theorem geometry_primrec : PrimrecPred Geometry :=
  (Primrec.eq.comp endpointBoundsCheck_primrec (Primrec.const true)).and
    ((Primrec.eq.comp expandedFiniteRoutesAvoidInteriors_primrec (Primrec.const true)).and
    ((Primrec.eq.comp finiteVerticesAvoidRouteInteriors_primrec (Primrec.const true)).and
      (Primrec.eq.comp expandedFiniteRoutesHaveDisjointInteriors_primrec (Primrec.const true))))

def Valid (g : PeriodicGraph V) (d : PeriodicGridDrawing) : Prop :=
  Compatible g d ∧ Geometry d

theorem valid_primrec : PrimrecRel (Valid (V := V)) :=
  compatible_primrec.and (geometry_primrec.comp Primrec.snd)

omit [Primcodable V] in
theorem valid_sound {g : PeriodicGraph V} {d : PeriodicGridDrawing}
    (wf : g.IsWellFormed) (h : Valid g d) :
    d.IsCompatible g ∧ d.IsContinuouslyPlanar := by
  refine ⟨⟨wf,h.1⟩,?_⟩
  exact isContinuouslyPlanar_of_expandedFinite (endpointBoundsCheck_spec h.2.1)
    h.1.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

omit [Primcodable V] in
theorem valid_complete {g : PeriodicGraph V} {d : PeriodicGridDrawing}
    (compatible : d.IsCompatible g)
    (bounds : d.SegmentEndpointsInExpandedSquare) (planar : d.IsContinuouslyPlanar) :
    Valid g d :=
  ⟨compatible.2,endpointBoundsCheck_complete bounds,
    expandedFiniteRoutesAvoidInteriors_complete planar.1.1,
    finiteVerticesAvoidRouteInteriors_complete planar.1.2,
    expandedFiniteRoutesHaveDisjointInteriors_complete planar.2⟩

end LeanTrominoes.PeriodicGridDrawing.FiniteCertificate
