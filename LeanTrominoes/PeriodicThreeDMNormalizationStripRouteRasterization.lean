/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRouteRasterization
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentLookup

/-!
# Rasterized normalized-route interiors in the rectangular strip
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Assignments generated from a suffix of at least three points also occur
in the strip assignments generated from any longer leading route. -/
theorem stripRouteInteriorAssignments_subset_append
    (period : Nat) (color : WireColor)
    (leading suffix : List Cell)
    (suffixLength : 3 ≤ suffix.length) :
    ∀ assignment,
      assignment ∈ stripRouteInteriorAssignments period color suffix →
      assignment ∈
        stripRouteInteriorAssignments period color (leading ++ suffix) := by
  induction leading with
  | nil =>
      intro assignment member
      simpa using member
  | cons first leading induction =>
      intro assignment member
      cases leading with
      | nil =>
          obtain ⟨suffixFirst, suffixSecond, suffixThird, suffixRest,
              suffixEquation⟩ :=
            List.exists_eq_cons_cons_cons_of_length_ge_three suffixLength
          rw [suffixEquation] at member ⊢
          simp only [List.cons_append, List.nil_append]
          rw [stripRouteInteriorAssignments]
          exact List.mem_cons_of_mem _ member
      | cons second leading =>
          have recursive := induction assignment member
          obtain ⟨after, remainder, tailEquation⟩ :
              ∃ after remainder,
                leading ++ suffix = after :: remainder := by
            cases leading with
            | nil =>
                obtain ⟨suffixFirst, suffixSecond, suffixThird, suffixRest,
                    suffixEquation⟩ :=
                  List.exists_eq_cons_cons_cons_of_length_ge_three suffixLength
                rw [suffixEquation]
                exact ⟨suffixFirst,
                  suffixSecond :: suffixThird :: suffixRest, rfl⟩
            | cons after remainder => exact ⟨after, remainder ++ suffix, rfl⟩
          change assignment ∈ stripRouteInteriorAssignments period color
            (second :: (leading ++ suffix)) at recursive
          rw [tailEquation] at recursive
          change assignment ∈ stripRouteInteriorAssignments period color
            (first :: second :: (leading ++ suffix))
          rw [tailEquation]
          rw [stripRouteInteriorAssignments]
          exact List.mem_cons_of_mem _ recursive

/-- A displayed consecutive triple anywhere in a route emits its middle
strip routing assignment. -/
theorem stripRouteInteriorAssignment_mem_append
    (period : Nat) (color : WireColor)
    (leading : List Cell) (before current after : Cell)
    (rest : List Cell) :
    (stripRasterLocation period current,
      routingCellTypeAt before current after color) ∈
      stripRouteInteriorAssignments period color
        (leading ++ before :: current :: after :: rest) := by
  let suffix := before :: current :: after :: rest
  have suffixLength : 3 ≤ suffix.length := by simp [suffix]
  have suffixMember :
      (stripRasterLocation period current,
        routingCellTypeAt before current after color) ∈
        stripRouteInteriorAssignments period color suffix := by
    simp [suffix, stripRouteInteriorAssignments]
  exact stripRouteInteriorAssignments_subset_append period color leading
    suffix suffixLength _ suffixMember

/-- Under collision freedom, strip lookup recovers the routing cell at any
displayed consecutive triple of a listed edge. -/
theorem PlanarPresentation.finalStripCellTypeAt_routeTriple
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current after : Cell)
    (rest : List Cell)
    (routeEquation : presentation.finalNormalizationRoute edge =
      leading ++ before :: current :: after :: rest) :
    presentation.finalStripCellTypeAt
        (stripRasterLocation presentation.finalNormalizationPeriod current) =
      routingCellTypeAt before current after edge.color := by
  apply presentation.finalStripCellTypeAt_routeInterior
    collisionFree edgeMember
  rw [routeEquation]
  exact stripRouteInteriorAssignment_mem_append _ _ _ _ _ _ _

/-- Every four-point window in a valid normalized route compiles to two
strip routing cells with matching common ports. -/
theorem PlanarPresentation.finalStripCellTypeAt_routeWindow_port_matches
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
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
    (presentation.finalStripCellTypeAt
      (stripRasterLocation presentation.finalNormalizationPeriod current)).portColor
        (Side.ofAxisDirection (AxisDirection.between current next)) =
      (presentation.finalStripCellTypeAt
        (stripRasterLocation presentation.finalNormalizationPeriod next)).portColor
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
  rw [presentation.finalStripCellTypeAt_routeTriple collisionFree edgeMember
    leading before current next (after :: rest) (by simpa using routeEquation)]
  rw [presentation.finalStripCellTypeAt_routeTriple collisionFree edgeMember
    (leading ++ [before]) current next after rest (by
      rw [routeEquation]
      simp)]
  exact routingCellTypes_portColor_match
    firstStep middleStep lastStep currentNoReverse nextNoReverse edge.color

end PeriodicThreeDM
end LeanTrominoes
