/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Simplicity of final gauged retained routes

Every stored route in the final gauged, anchor-normalized, deduplicated
periodic drawing is a translate of one genuine route in the continuously
planar finite retained drawing.  Finite route simplicity and translation
invariance therefore give route-local simplicity in the quotient.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Every genuine route selected by the final retained route family is
simple. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (taggedClause :
      PositionedPeriodicClause
          (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedClauseMember :
      taggedClause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    (taggedLiteral :
      PeriodicLiteral
          (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedLiteralMember :
      taggedLiteral ∈ taggedClause.1.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula taggedClause.2 taggedLiteral.2) := by
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula wellFormed degree isLocal clausesNonempty
        taggedClause taggedClauseMember
        taggedLiteral taggedLiteralMember (0, 0) with
    ⟨witness⟩
  let drawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
  have retainedPlanar :
      drawing.IsPlanar :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
      formula wellFormed degree isLocal clausesNonempty
  rcases List.mem_iff_get.mp witness.incidenceMember with
    ⟨incidenceIndex, incidenceAtEq⟩
  have physicalSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (drawing.routeAt
          (metadataPhysicalIncidence
            witness.metadata witness.metadataIndex
            witness.literal taggedLiteral.2)) := by
    have selected := retainedPlanar.1 incidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (drawing.routeAt
          (drawing.incidenceAt incidenceIndex)) at selected
    have incidenceAtEq' :
        drawing.incidenceAt incidenceIndex =
          metadataPhysicalIncidence
            witness.metadata witness.metadataIndex
            witness.literal taggedLiteral.2 := by
      simpa [drawing,
        EmbeddedCNFIncidenceDrawing.incidenceAt] using
        incidenceAtEq
    rw [incidenceAtEq'] at selected
    exact selected
  let physicalOffset :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation
      (Cell.sub (0, 0)
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula witness.metadata).literals))
  have translatedSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (translatePolyline physicalOffset
          (drawing.routeAt
            (metadataPhysicalIncidence
              witness.metadata witness.metadataIndex
              witness.literal taggedLiteral.2))) := by
    exact
      EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
        physicalSimple physicalOffset
  have occurrenceEq := witness.routeEq
  unfold finalGaugedRouteOccurrence
    metadataPhysicalRouteOccurrence at occurrenceEq
  have zeroTranslation :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation (0, 0) = (0, 0) := by
    simp [PeriodicVariablePlacement.translation, Cell.scale]
  rw [zeroTranslation] at occurrenceEq
  have translatePolyline_zero (points : List Cell) :
      translatePolyline (0, 0) points = points := by
    induction points with
    | nil => rfl
    | cons point points induction =>
        change
          List.map (Cell.add (0, 0)) points = points at induction
        simp only [translatePolyline, List.map_cons]
        rw [induction]
        simp [Cell.add]
  rw [translatePolyline_zero] at occurrenceEq
  change
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula taggedClause.2 taggedLiteral.2 =
      translatePolyline physicalOffset
        (drawing.routeAt
          (metadataPhysicalIncidence
            witness.metadata witness.metadataIndex
            witness.literal taggedLiteral.2)) at occurrenceEq
  rw [occurrenceEq]
  exact translatedSimple

/-- Membership form: every route stored in the final incidence drawing is
simple. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAreSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    ∀ route ∈
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro route routeMember
  rcases exists_incidenceRoute_coordinates
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      (by
        simpa only [
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
          using routeMember) with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteral, taggedLiteralMember, routeEq⟩
  subst route
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
      formula wellFormed degree isLocal clausesNonempty
      taggedClause taggedClauseMember
      taggedLiteral taggedLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
