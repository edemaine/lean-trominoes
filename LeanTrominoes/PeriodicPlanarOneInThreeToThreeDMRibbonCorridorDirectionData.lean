/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly

/-! # Direction words of assembled ribbon corridors -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- Finite direction table for one colored ribbon macrocell. -/
def ribbonMacrocellDirectionBlock
    (incoming outgoing : AxisDirection) (color : WireColor) :
    List AxisDirection :=
  unitSubdivisionDirections
    (standardRibbonMacrocellRoute incoming outgoing color)

/-- Apply the finite macrocell table to every adjacent pair of directions in
one unit-step source word.  The unmatched first or last half-edge belongs to
the endpoint fans, not the corridor core. -/
def ribbonCorridorDirectionWord
    (color : WireColor) : List AxisDirection → List AxisDirection
  | incoming :: outgoing :: rest =>
      ribbonMacrocellDirectionBlock incoming outgoing color ++
        ribbonCorridorDirectionWord color (outgoing :: rest)
  | _ => []
termination_by directions => directions.length

/-- Translating a finite macrocell table to an arbitrary source point does
not change its direction word. -/
theorem unitSubdivisionDirections_ribbonMacrocellRoute
    (center : Cell) (incoming outgoing : AxisDirection)
    (color : WireColor) :
    unitSubdivisionDirections
        (ribbonMacrocellRoute center incoming outgoing color) =
      ribbonMacrocellDirectionBlock incoming outgoing color := by
  simpa only [ribbonMacrocellRoute, ribbonMacrocellDirectionBlock,
    translatePolyline] using
    unitSubdivisionDirections_translatePolyline
      (ribbonMacrocellOrigin center)
      (standardRibbonMacrocellRoute incoming outgoing color)

/-- The complete assembled corridor core is exactly the adjacent-pair finite
transduction of its unit-step source direction word. -/
theorem unitSubdivisionDirections_ribbonCorridorCore
    (color : WireColor) (first center next : Cell) (rest : List Cell)
    (unitSteps :
      (first :: center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep) :
    unitSubdivisionDirections
        (ribbonCorridorCore color (first :: center :: next :: rest)) =
      ribbonCorridorDirectionWord color
        (unitSubdivisionDirections (first :: center :: next :: rest)) := by
  induction rest generalizing first center next with
  | nil =>
      have parts := unitSteps_cons_cons_cons unitSteps
      rw [ribbonCorridorCore]
      rw [unitSubdivisionDirections_ribbonMacrocellRoute]
      simp only [unitSubdivisionDirections,
        segmentLength_eq_one_of_unitAxisStep parts.1,
        segmentLength_eq_one_of_unitAxisStep parts.2.1,
        List.replicate_one, List.singleton_append,
        ribbonCorridorDirectionWord, List.append_nil]
  | cons fourth rest induction =>
      have parts := unitSteps_cons_cons_cons unitSteps
      have firstNonempty :
          ribbonMacrocellRoute center
              (AxisDirection.between first center)
              (AxisDirection.between center next) color ≠ [] := by
        intro empty
        have head := ribbonMacrocellRoute_head? center
          (AxisDirection.between first center)
          (AxisDirection.between center next) color
        rw [empty] at head
        simp at head
      have boundary :
          (ribbonMacrocellRoute center
              (AxisDirection.between first center)
              (AxisDirection.between center next) color).getLast? =
            (ribbonCorridorCore color
              (center :: next :: fourth :: rest)).head? := by
        rw [ribbonMacrocellRoute_getLast?,
          ribbonCorridorCore_head?]
        exact congrArg some
          (ribbonMacrocellExit_eq_entry_of_unitAxisStep
            parts.2.1 color)
      rw [ribbonCorridorCore]
      rw [unitSubdivisionDirections_joinAtEndpoint
        firstNonempty boundary]
      rw [unitSubdivisionDirections_ribbonMacrocellRoute]
      rw [induction center next fourth parts.2.2]
      simp only [unitSubdivisionDirections,
        segmentLength_eq_one_of_unitAxisStep parts.1,
        segmentLength_eq_one_of_unitAxisStep parts.2.1,
        List.replicate_one, List.singleton_append,
        ribbonCorridorDirectionWord]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
