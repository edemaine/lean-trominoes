import LeanTrominoes.PeriodicOrthocrossingPlanarSATFiniteIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingPlanarSATNoncarrierSeparation

/-!
# Isolating the carrier-lens separation obligation

Non-carrier components are now completely separated.  This file packages
the exact residual certificate: pairs for which at least one component is a
straight carrier lens.  Supplying that certificate yields the complete
component-level and globally indexed route-separation theorems.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every non-carrier component has its advertised macrocell center. -/
theorem DrawingPlanarSATComponent.exists_macrocellCenter_of_not_carrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (component : DrawingPlanarSATComponent Variable)
    (notCarrier :
      ¬∃ link, component = .carrier link) :
    ∃ center, component.macrocellCenter formula = some center := by
  cases component with
  | crossover crossing =>
      exact ⟨crossing.point, rfl⟩
  | carrier link =>
      exact (notCarrier ⟨link, rfl⟩).elim
  | bend routeBend =>
      exact
        ⟨routeBend.drawingPoint
            (PeriodicCNF.incidenceGraph formula),
          rfl⟩
  | routedClause site =>
      exact
        ⟨liftedIncidenceVertexPosition
            formula (.clause site.1) site.2,
          rfl⟩
  | routedVariable site arm link =>
      exact
        ⟨liftedIncidenceVertexPosition
            formula (.variable site.1) site.2,
          rfl⟩

/-- The remaining geometric obligation consists exactly of distinct
component pairs involving at least one straight carrier lens. -/
def DrawingPlanarSATCarrierComponentRoutesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ (firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable),
    firstMetadata.Valid formula →
      secondMetadata.Valid formula →
        ∀ {firstLiteral secondLiteral :
            PlanarSATVariable Variable × Bool}
          {firstLiteralIndex secondLiteralIndex : Nat},
          (firstLiteral, firstLiteralIndex) ∈
              firstMetadata.clause.literals.zipIdx →
            (secondLiteral, secondLiteralIndex) ∈
                secondMetadata.clause.literals.zipIdx →
              firstMetadata.source.component ≠
                  secondMetadata.source.component →
                ((∃ link,
                    firstMetadata.source.component = .carrier link) ∨
                  ∃ link,
                    secondMetadata.source.component = .carrier link) →
                  EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
                    ((firstMetadata.source.incidenceDrawing formula).routes
                      firstMetadata.source.localClauseIndex
                      firstLiteralIndex)
                    ((secondMetadata.source.incidenceDrawing formula).routes
                      secondMetadata.source.localClauseIndex
                      secondLiteralIndex)

/-- Carrier-involving separation plus the certified non-carrier theorem
gives separation for every pair of distinct local components. -/
theorem drawingPlanarSAT_componentRoutesSeparated_of_carriers
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (carriersSeparated :
      DrawingPlanarSATCarrierComponentRoutesSeparated formula) :
    DrawingPlanarSATComponentRoutesSeparated formula := by
  intro firstMetadata secondMetadata firstValid secondValid
    firstLiteral secondLiteral
    firstLiteralIndex secondLiteralIndex
    firstLiteralMem secondLiteralMem differentComponents
  by_cases firstCarrier :
      ∃ link, firstMetadata.source.component = .carrier link
  · exact
      carriersSeparated
        firstMetadata secondMetadata firstValid secondValid
        firstLiteralMem secondLiteralMem differentComponents
        (Or.inl firstCarrier)
  by_cases secondCarrier :
      ∃ link, secondMetadata.source.component = .carrier link
  · exact
      carriersSeparated
        firstMetadata secondMetadata firstValid secondValid
        firstLiteralMem secondLiteralMem differentComponents
        (Or.inr secondCarrier)
  rcases
      firstMetadata.source.component.exists_macrocellCenter_of_not_carrier
        formula firstCarrier with
    ⟨firstCenter, firstCenterEq⟩
  rcases
      secondMetadata.source.component.exists_macrocellCenter_of_not_carrier
        formula secondCarrier with
    ⟨secondCenter, secondCenterEq⟩
  exact
    drawingPlanarSATMetadata_noncarrierRoutesAvoidEachOther
      formula wellFormed degree isLocal
      firstMetadata secondMetadata firstValid secondValid
      firstCenter secondCenter firstCenterEq secondCenterEq
      differentComponents firstLiteralMem secondLiteralMem

/-- The residual carrier certificate also supplies the globally indexed
cross-component route-separation predicate. -/
theorem drawingPlanarSAT_crossComponentRoutesSeparated_of_carriers
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (carriersSeparated :
      DrawingPlanarSATCarrierComponentRoutesSeparated formula) :
    DrawingPlanarSATCrossComponentRoutesSeparated formula :=
  drawingPlanarSAT_crossComponentRoutesSeparated_of_components
    formula
    (drawingPlanarSAT_componentRoutesSeparated_of_carriers
      formula wellFormed degree isLocal carriersSeparated)

end PeriodicOrthocrossing
end LeanTrominoes
