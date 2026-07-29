import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalRetainedRays
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences

/-!
# Retained rays after periodic quotient bookkeeping

The final retained planar-SAT route family is obtained from the finite local
drawing by variable gauging, clause-anchor normalization, and first-orbit
representative selection.  The existing quotient-to-finite occurrence
witness identifies every genuine final route occurrence with a translate of
one genuine finite route.

Because common translation preserves the retained-ray predicate, this file
transfers the finite certificate to every genuine route of the final gauged,
deduplicated periodic source.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- Every genuine final retained planar-SAT incidence route uses only the
eleven supported ray slopes. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
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
    RetainedRayPolyline
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
  have finiteRetained :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_routesRetainedRay
      formula wellFormed degree isLocal
  rcases List.mem_iff_get.mp witness.incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have localRetained :=
    finiteRetained incidenceIndex
  simp only [EmbeddedCNFIncidenceDrawing.incidenceAt] at localRetained
  rw [incidenceEqual] at localRetained
  let physicalOffset :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation
      (Cell.sub (0, 0)
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula witness.metadata).literals))
  have translatedLocal :
      RetainedRayPolyline
        (translatePolyline physicalOffset
          (drawing.routeAt
            (metadataPhysicalIncidence
              witness.metadata witness.metadataIndex
              witness.literal taggedLiteral.2))) := by
    exact localRetained.translate physicalOffset
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
