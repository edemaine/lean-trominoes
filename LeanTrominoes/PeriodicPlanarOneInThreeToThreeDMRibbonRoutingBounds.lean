import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRouting

/-!
# Pointwise bounds for complete ribbon routes

Every listed point of a corrected three-strand route belongs either to the
source-variable endpoint block, to a block along the unitized corridor, or
to the lifted source-clause endpoint block.  This decomposition is the
coordinate-bound and far-separation interface for the complete joined route.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- The variable endpoint is one of the selected unit source route's listed
points. -/
theorem occurrenceUnitSourceRoute_variableEndpoint_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    placement.position entry.1.1 ∈
      occurrenceUnitSourceRoute presentation entry := by
  let data := occurrenceSpliceData presentation entry
  have atomEq :
      data.tagged.1.atom = entry.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase entry.1.1 entry.1.2 data.tagged
      data.occurrenceLookup).2
  have endpoint :=
    (occurrenceUnitSourceRoute_endpoints
      presentation entry).1
  have headEq :
      (occurrenceUnitSourceRoute presentation entry).head? =
        some (placement.position entry.1.1) := by
    simpa [data, atomEq] using endpoint
  cases routeEquation :
      occurrenceUnitSourceRoute presentation entry with
  | nil =>
      simp [routeEquation] at headEq
  | cons first rest =>
      have firstEq :
          first = placement.position entry.1.1 := by
        rw [routeEquation] at headEq
        exact Option.some.inj headEq
      subst first
      simp

/-- The lifted clause endpoint is one of the selected unit source route's
listed points. -/
theorem occurrenceUnitSourceRoute_clauseEndpoint_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    PositionedPeriodicCNF.variableToClauseTarget
        placement data.positionedClause data.tagged.1 ∈
      occurrenceUnitSourceRoute presentation entry := by
  let data := occurrenceSpliceData presentation entry
  exact
    mem_of_getLast?_eq_some
      (occurrenceUnitSourceRoute_endpoints
        presentation entry).2

/-- Pointwise ownership decomposition for one complete corrected colored
route. -/
theorem occurrenceRibbonThreeStrandRoute_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) {point : Cell}
    (member :
      point ∈ occurrenceRibbonThreeStrandRoute
        presentation entry color) :
    InRibbonMacrocell (placement.position entry.1.1) point ∨
      (∃ center ∈ occurrenceUnitSourceRoute presentation entry,
        InRibbonMacrocell center point) ∨
      let data := occurrenceSpliceData presentation entry
      InRibbonMacrocell
        (PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1)
        point := by
  unfold occurrenceRibbonThreeStrandRoute at member
  rcases mem_joinAtEndpoint member with
      prefixMember | clauseMember
  · rcases mem_joinAtEndpoint prefixMember with
        variableMember | coreMember
    · exact
        Or.inl
          (occurrenceRibbonVariableStub_points_bounded
            presentation entry color variableMember)
    · exact
        Or.inr
          (Or.inl
            (occurrenceRibbonCorridorCore_points_bounded
              presentation entry color coreMember))
  · exact
      Or.inr
        (Or.inr
          (occurrenceRibbonClauseStub_points_bounded
            presentation entry color clauseMember))

/-- Every point of a complete corrected route lies in the refined block of
some listed point on its selected unit source route. -/
theorem occurrenceRibbonThreeStrandRoute_point_in_source_macrocell
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) {point : Cell}
    (member :
      point ∈ occurrenceRibbonThreeStrandRoute
        presentation entry color) :
    ∃ center ∈ occurrenceUnitSourceRoute presentation entry,
      InRibbonMacrocell center point := by
  rcases
      occurrenceRibbonThreeStrandRoute_points_bounded
        presentation entry color member with
      variableBounded | coreBounded | clauseBounded
  · exact
      ⟨placement.position entry.1.1,
        occurrenceUnitSourceRoute_variableEndpoint_mem
          presentation entry,
        variableBounded⟩
  · exact coreBounded
  · let data := occurrenceSpliceData presentation entry
    exact
      ⟨PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1,
        occurrenceUnitSourceRoute_clauseEndpoint_mem
          presentation entry,
        clauseBounded⟩

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
