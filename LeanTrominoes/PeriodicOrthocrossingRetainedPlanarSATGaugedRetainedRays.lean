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
  have finiteRetained :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_routesRetainedRay
      formula wellFormed degree isLocal
  rcases List.mem_iff_get.mp witness.incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have localRetained :=
    finiteRetained incidenceIndex
  simp only [EmbeddedCNFIncidenceDrawing.incidenceAt] at localRetained
  rw [incidenceEqual] at localRetained
  have translatedLocal :
      RetainedRayPolyline
        (metadataPhysicalRouteOccurrence
          formula witness.metadata witness.metadataIndex
          witness.literal taggedLiteral.2 (0, 0)) := by
    unfold metadataPhysicalRouteOccurrence
    exact localRetained.translate _
  rw [← witness.routeEq] at translatedLocal
  simpa [finalGaugedRouteOccurrence,
    translatePolyline,
    PeriodicVariablePlacement.translation,
    Cell.scale, Cell.add] using translatedLocal

end PeriodicOrthocrossing
end LeanTrominoes
