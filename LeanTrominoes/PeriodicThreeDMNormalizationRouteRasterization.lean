import LeanTrominoes.PeriodicThreeDMNormalizationEndpointRasterization

/-!
# Rasterized normalized-route interiors

Endpoint matching handles the first and last routing cells separately.  This
module handles every internal adjacency uniformly.  Any displayed triple in
a route emits its middle routing assignment; under collision freedom lookup
recovers that cell exactly.  Two overlapping triples from a unit-step route
without immediate reversals then expose the same edge color on their common
side.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Removing a route's first point preserves absence of immediate
reversals. -/
theorem hasNoImmediateReversal_tail
    {points : List Cell}
    (noReversal : AxisDirection.HasNoImmediateReversal points) :
    AxisDirection.HasNoImmediateReversal points.tail := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [AxisDirection.HasNoImmediateReversal]
  | cons_cons first second rest induction =>
      cases rest with
      | nil => simp [AxisDirection.HasNoImmediateReversal]
      | cons third rest => exact noReversal.2

/-- Dropping any number of initial points preserves absence of immediate
reversals. -/
theorem hasNoImmediateReversal_drop
    {points : List Cell}
    (noReversal : AxisDirection.HasNoImmediateReversal points)
    (count : Nat) :
    AxisDirection.HasNoImmediateReversal (points.drop count) := by
  induction count generalizing points with
  | zero => simpa using noReversal
  | succ count induction =>
      rw [← List.drop_tail]
      exact induction (hasNoImmediateReversal_tail noReversal)

/-- A displayed consecutive triple anywhere in a route emits the routing
assignment at its middle point. -/
theorem routeInteriorAssignment_mem_append
    (period : Nat) (color : WireColor)
    (leading : List Cell) (before current after : Cell)
    (rest : List Cell) :
    (rasterLocation period current,
      routingCellTypeAt before current after color) ∈
      routeInteriorAssignments period color
        (leading ++ before :: current :: after :: rest) := by
  let suffix := before :: current :: after :: rest
  have suffixLength : 3 ≤ suffix.length := by simp [suffix]
  have suffixMember :
      (rasterLocation period current,
        routingCellTypeAt before current after color) ∈
        routeInteriorAssignments period color suffix := by
    simp [suffix, routeInteriorAssignments]
  exact routeInteriorAssignments_subset_append period color leading suffix
    suffixLength _ suffixMember

/-- Under collision freedom, lookup recovers the routing cell at any
displayed consecutive triple of a listed edge. -/
theorem PlanarPresentation.finalCellTypeAt_routeTriple
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current after : Cell)
    (rest : List Cell)
    (routeEquation : presentation.finalNormalizationRoute edge =
      leading ++ before :: current :: after :: rest) :
    presentation.finalCellTypeAt
        (rasterLocation presentation.finalNormalizationPeriod current) =
      routingCellTypeAt before current after edge.color := by
  apply presentation.finalCellTypeAt_routeInterior
    collisionFree edgeMember
  rw [routeEquation]
  exact routeInteriorAssignment_mem_append _ _ _ _ _ _ _

/-- A routing cell in a valid route triple exposes the route color toward
its successor. -/
theorem routingCellTypeAt_portColor_toward_after
    {before current after : Cell}
    (incoming : AxisDirection.IsUnitAxisStep before current)
    (outgoing : AxisDirection.IsUnitAxisStep current after)
    (noReverse :
      AxisDirection.between current after ≠
        (AxisDirection.between before current).opposite)
    (color : WireColor) :
    (routingCellTypeAt before current after color).portColor
        (Side.ofAxisDirection
          (AxisDirection.between current after)) =
      some color := by
  rw [routingCellTypeAt_portColor incoming outgoing noReverse]
  simp

/-- The next routing cell exposes the same color back toward its predecessor,
on the opposite drawing side. -/
theorem routingCellTypeAt_portColor_toward_before
    {before current after : Cell}
    (incoming : AxisDirection.IsUnitAxisStep before current)
    (outgoing : AxisDirection.IsUnitAxisStep current after)
    (noReverse :
      AxisDirection.between current after ≠
        (AxisDirection.between before current).opposite)
    (color : WireColor) :
    (routingCellTypeAt before current after color).portColor
        (Side.ofAxisDirection
          (AxisDirection.between before current)).opposite =
      some color := by
  have forwardGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep incoming
  have backward :
      AxisDirection.between current before =
        (AxisDirection.between before current).opposite :=
    AxisDirection.between_reverse_eq_opposite forwardGenuine
  have backwardSide :
      Side.ofAxisDirection (AxisDirection.between current before) =
        (Side.ofAxisDirection
          (AxisDirection.between before current)).opposite := by
    rw [backward]
    exact Side.ofAxisDirection_opposite forwardGenuine
  rw [routingCellTypeAt_portColor incoming outgoing noReverse]
  simp [backwardSide]

/-- Two adjacent routing cells from overlapping valid triples have matching
ports on their common side. -/
theorem routingCellTypes_portColor_match
    {before current next after : Cell}
    (firstStep : AxisDirection.IsUnitAxisStep before current)
    (middleStep : AxisDirection.IsUnitAxisStep current next)
    (lastStep : AxisDirection.IsUnitAxisStep next after)
    (currentNoReverse :
      AxisDirection.between current next ≠
        (AxisDirection.between before current).opposite)
    (nextNoReverse :
      AxisDirection.between next after ≠
        (AxisDirection.between current next).opposite)
    (color : WireColor) :
    (routingCellTypeAt before current next color).portColor
        (Side.ofAxisDirection (AxisDirection.between current next)) =
      (routingCellTypeAt current next after color).portColor
        (Side.ofAxisDirection
          (AxisDirection.between current next)).opposite := by
  rw [routingCellTypeAt_portColor_toward_after
    firstStep middleStep currentNoReverse]
  rw [routingCellTypeAt_portColor_toward_before
    middleStep lastStep nextNoReverse]

/-- Every four-point window in a valid listed normalized route compiles to
two routing cells with matching common ports. -/
theorem PlanarPresentation.finalCellTypeAt_routeWindow_port_matches
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (unitSteps :
      (presentation.finalNormalizationRoute edge).IsChain
        AxisDirection.IsUnitAxisStep)
    (noImmediateReversal :
      AxisDirection.HasNoImmediateReversal
        (presentation.finalNormalizationRoute edge))
    (leading : List Cell) (before current next after : Cell)
    (rest : List Cell)
    (routeEquation : presentation.finalNormalizationRoute edge =
      leading ++ before :: current :: next :: after :: rest) :
    (presentation.finalCellTypeAt
      (rasterLocation presentation.finalNormalizationPeriod current)).portColor
        (Side.ofAxisDirection (AxisDirection.between current next)) =
      (presentation.finalCellTypeAt
        (rasterLocation presentation.finalNormalizationPeriod next)).portColor
          (Side.ofAxisDirection
            (AxisDirection.between current next)).opposite := by
  have suffixUnitSteps :
      (before :: current :: next :: after :: rest).IsChain
        AxisDirection.IsUnitAxisStep := by
    rw [routeEquation] at unitSteps
    exact (List.isChain_append.mp unitSteps).2.1
  have firstStep := (List.isChain_cons_cons.mp suffixUnitSteps).1
  have afterFirst := (List.isChain_cons_cons.mp suffixUnitSteps).2
  have middleStep := (List.isChain_cons_cons.mp afterFirst).1
  have afterMiddle := (List.isChain_cons_cons.mp afterFirst).2
  have lastStep := (List.isChain_cons_cons.mp afterMiddle).1
  have suffixNoReversal :
      AxisDirection.HasNoImmediateReversal
        (before :: current :: next :: after :: rest) := by
    rw [routeEquation] at noImmediateReversal
    have dropped := hasNoImmediateReversal_drop
      noImmediateReversal leading.length
    simpa using dropped
  have currentNoReverse := suffixNoReversal.1
  have nextNoReverse := suffixNoReversal.2.1
  rw [presentation.finalCellTypeAt_routeTriple collisionFree edgeMember
    leading before current next (after :: rest) (by simpa using routeEquation)]
  rw [presentation.finalCellTypeAt_routeTriple collisionFree edgeMember
    (leading ++ [before]) current next after rest (by
      rw [routeEquation]
      simp)]
  exact routingCellTypes_portColor_match
    firstStep middleStep lastStep currentNoReverse nextNoReverse edge.color

end PeriodicThreeDM
end LeanTrominoes
