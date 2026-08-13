/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalOrthogonalPrefixes
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences

/-!
# Orthogonal route prefixes after periodic quotient bookkeeping

The final retained planar-SAT route family is obtained from the finite local
drawing by variable gauging, clause-anchor normalization, and first-orbit
representative selection.  Every genuine final route occurrence is a
translate of one genuine finite route.

Translation preserves the orthogonality of `dropLast`, so the local
route-prefix certificate transfers to every genuine final route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- Every genuine final retained planar-SAT incidence route is orthogonal
before its final point. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_prefixOrthogonal
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
    OrthogonalPolyline
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula taggedClause.2 taggedLiteral.2).dropLast := by
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula wellFormed degree isLocal clausesNonempty
      taggedClause taggedClauseMember
        taggedLiteral taggedLiteralMember (0, 0) with
    ⟨witness⟩
  let drawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
  have finiteOrthogonal :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_routePrefixesOrthogonal
      formula wellFormed degree isLocal
  rcases List.mem_iff_get.mp witness.incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have localOrthogonal :=
    finiteOrthogonal incidenceIndex
  simp only [EmbeddedCNFIncidenceDrawing.incidenceAt]
    at localOrthogonal
  rw [incidenceEqual] at localOrthogonal
  let physicalOffset :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation
      (Cell.sub (0, 0)
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula witness.metadata).literals))
  have translatedLocal :
      OrthogonalPolyline
        (translatePolyline physicalOffset
          (drawing.routeAt
            (metadataPhysicalIncidence
              witness.metadata witness.metadataIndex
              witness.literal taggedLiteral.2))).dropLast := by
    simpa only [translatePolyline, List.map_dropLast] using
      localOrthogonal.translate physicalOffset
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
  exact translatedLocal

/-- Every genuine final retained planar-SAT incidence route is either fully
orthogonal or has a singleton prefix. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_orthogonalOrSingletonPrefix
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
    OrthogonalPolyline
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula taggedClause.2 taggedLiteral.2) ∨
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula taggedClause.2 taggedLiteral.2).dropLast.length = 1 := by
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula wellFormed degree isLocal clausesNonempty
      taggedClause taggedClauseMember
        taggedLiteral taggedLiteralMember (0, 0) with
    ⟨witness⟩
  let drawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
  have finiteShape :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_routesOrthogonalOrSingletonPrefix
      formula wellFormed degree isLocal
  rcases List.mem_iff_get.mp witness.incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have localShape :=
    finiteShape incidenceIndex
  simp only [EmbeddedCNFIncidenceDrawing.incidenceAt]
    at localShape
  rw [incidenceEqual] at localShape
  let physicalOffset :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation
      (Cell.sub (0, 0)
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula witness.metadata).literals))
  have translatedLocal :
      OrthogonalPolyline
          (translatePolyline physicalOffset
            (drawing.routeAt
              (metadataPhysicalIncidence
                witness.metadata witness.metadataIndex
                witness.literal taggedLiteral.2))) ∨
        (translatePolyline physicalOffset
          (drawing.routeAt
            (metadataPhysicalIncidence
              witness.metadata witness.metadataIndex
              witness.literal taggedLiteral.2))).dropLast.length = 1 := by
    rcases localShape with orthogonal | singleton
    · exact Or.inl (orthogonal.translate physicalOffset)
    · right
      change
        (List.map (Cell.add physicalOffset)
          (drawing.routeAt
            (metadataPhysicalIncidence
              witness.metadata witness.metadataIndex
              witness.literal taggedLiteral.2))).dropLast.length = 1
      rw [← List.map_dropLast, List.length_map]
      exact singleton
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
  exact translatedLocal

end PeriodicOrthocrossing
end LeanTrominoes
