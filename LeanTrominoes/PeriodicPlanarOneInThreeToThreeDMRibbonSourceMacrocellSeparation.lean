import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation

/-!
# Separating ribbon tiles inherited from separated source routes

An interior tile of one source route and an interior tile of another cannot
realize the sole endpoint contact allowed by adjacent ribbon macrocells.
Either contact would identify a neighboring source-route point with the
other route's internal center, contradicting endpoint-only source contacts.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Interior ribbon tiles selected from two endpoint-contact-separated unit
routes strictly avoid each other, for arbitrary colors. -/
theorem interiorSourceRibbonMacrocellRoutes_strictlyAvoidEachOther
    {firstRoute secondRoute : List Cell}
    (meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute secondRoute)
    {firstPrevious firstCenter firstNext
      secondPrevious secondCenter secondNext : Cell}
    (firstCenterMember : firstCenter ∈ firstRoute)
    (firstNextMember : firstNext ∈ firstRoute)
    (secondCenterMember : secondCenter ∈ secondRoute)
    (secondNextMember : secondNext ∈ secondRoute)
    (firstCenterInternal :
      ¬RoutePointIsEndpoint firstRoute firstCenter)
    (secondCenterInternal :
      ¬RoutePointIsEndpoint secondRoute secondCenter)
    (firstIncomingUnit :
      AxisDirection.IsUnitAxisStep
        firstPrevious firstCenter)
    (firstOutgoingUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (secondIncomingUnit :
      AxisDirection.IsUnitAxisStep
        secondPrevious secondCenter)
    (secondOutgoingUnit :
      AxisDirection.IsUnitAxisStep secondCenter secondNext)
    (firstNoReverse :
      AxisDirection.between firstCenter firstNext ≠
        (AxisDirection.between
          firstPrevious firstCenter).opposite)
    (secondNoReverse :
      AxisDirection.between secondCenter secondNext ≠
        (AxisDirection.between
          secondPrevious secondCenter).opposite)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        (AxisDirection.between firstPrevious firstCenter)
        (AxisDirection.between firstCenter firstNext)
        firstColor)
      (ribbonMacrocellRoute secondCenter
        (AxisDirection.between secondPrevious secondCenter)
        (AxisDirection.between secondCenter secondNext)
        secondColor) := by
  have firstIncomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      firstIncomingUnit
  have firstOutgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      firstOutgoingUnit
  have secondIncomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondIncomingUnit
  have secondOutgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondOutgoingUnit
  have centersDifferent :
      firstCenter ≠ secondCenter :=
    routePoints_ne_of_routesMeetOnlyAtEndpoints
      meetOnly firstCenterMember secondCenterMember
      (Or.inl firstCenterInternal)
  apply
    ribbonMacrocellRoutes_strictlyAvoidEachOther_of_centers_ne
      centersDifferent
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor
  intro firstEnd secondEnd contact
  cases firstEnd <;> cases secondEnd
  · exact contact
  · rcases contact with
      ⟨offsetEq, sameOutgoing, _sameColor⟩
    have secondNextEquation :=
      AxisDirection.add_between_step_eq_of_unitAxisStep
        secondOutgoingUnit
    have secondCenterEquation :
        secondCenter =
          Cell.add firstCenter
            (AxisDirection.between
              firstPrevious firstCenter).opposite.step := by
      calc
        secondCenter =
            Cell.add firstCenter
              (Cell.sub secondCenter firstCenter) := by
          rcases firstCenter with ⟨firstX, firstY⟩
          rcases secondCenter with ⟨secondX, secondY⟩
          simp [Cell.add, Cell.sub]
        _ = Cell.add firstCenter
              (AxisDirection.between
                firstPrevious firstCenter).opposite.step := by
          rw [offsetEq]
    have shared : firstCenter = secondNext := by
      calc
        firstCenter =
            Cell.add
              (Cell.add firstCenter
                (AxisDirection.between
                  firstPrevious firstCenter).opposite.step)
              (AxisDirection.between
                firstPrevious firstCenter).step := by
          exact
            (AxisDirection.add_opposite_step_add_step
              firstCenter firstIncomingGenuine).symm
        _ = Cell.add secondCenter
              (AxisDirection.between
                firstPrevious firstCenter).step := by
          rw [secondCenterEquation]
        _ = Cell.add secondCenter
              (AxisDirection.between
                secondCenter secondNext).step := by
          rw [sameOutgoing]
        _ = secondNext := secondNextEquation.symm
    exact
      (routePoints_ne_of_routesMeetOnlyAtEndpoints
        meetOnly firstCenterMember secondNextMember
        (Or.inl firstCenterInternal)) shared
  · rcases contact with
      ⟨offsetEq, sameIncoming, _sameColor⟩
    have firstNextEquation :=
      AxisDirection.add_between_step_eq_of_unitAxisStep
        firstOutgoingUnit
    have shared : secondCenter = firstNext := by
      calc
        secondCenter =
            Cell.add firstCenter
              (Cell.sub secondCenter firstCenter) := by
          rcases firstCenter with ⟨firstX, firstY⟩
          rcases secondCenter with ⟨secondX, secondY⟩
          simp [Cell.add, Cell.sub]
        _ = Cell.add firstCenter
              (AxisDirection.between
                firstCenter firstNext).step := by
          rw [offsetEq]
        _ = firstNext := firstNextEquation.symm
    exact
      (routePoints_ne_of_routesMeetOnlyAtEndpoints
        meetOnly firstNextMember secondCenterMember
        (Or.inr secondCenterInternal)) shared.symm
  · exact contact

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
