/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionCanonical

/-! # Exact phase-major fixed-eight direction shapes -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFixedEightDirection

open ClauseProfileOccurrenceSplit
open UnaryProgramClauseProfile

/-- Clockwise clause ordering reverses four of the nine implication clauses
in the concrete Figure 7 ring. -/
def orderedCycleProfiles : List ClauseProfile :=
  List.replicate 4 implicationProfile ++
    List.replicate 4 (.binary (current true) (current false)) ++
      [implicationProfile]

/-- Exact profile list obtained by sorting the closed Figure 7 ring by its
routed directions. -/
@[simp] theorem clauseProfiles_shape_cycleClauseDescriptors :
    FormulaShape.clauseProfiles
        (FormulaShapeDirectionOrdering.shape cycleClauseDescriptors) =
      orderedCycleProfiles := by
  have zeroCell : (0 : Cell) = (0, 0) := rfl
  simp [cycleClauseDescriptors, localCycleFormula,
    OccurrenceSplitRing.cycleFormula,
    OccurrenceSplitRing.presentedCycleVertices,
    OccurrenceSplitRing.cycleVertices,
    localCycleClause, OccurrenceSplitRing.cycleClause,
    OccurrenceSplitRing.cycleRoutes, OccurrenceSplitRing.cycleRoute,
    OccurrenceSplitRing.cycleClausePosition,
    OccurrenceSplitRing.ringVariablePosition,
    OccurrenceSplitRing.separatorPosition,
    OccurrenceSplitRing.variablePosition,
    OccurrenceSplitRing.RingVertex.next,
    FormulaShapeDirectionOrdering.shape,
    FormulaShapeDirectionOrdering.tokenBlock,
    FormulaShapeDirectionOrdering.DirectedClauseProfile.orderedProfile,
    FormulaShapeDirectionOrdering.DirectedClauseProfile.orderedLiterals,
    FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause,
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList,
    FormulaShapeDirectionOrdering.annotatedLiterals,
    FormulaShapeDirectionOrdering.literalProfile,
    FormulaShapeDirectionOrdering.directionLE,
    FormulaShapeOfFormula.clauseProfile,
    FormulaShape.clauseProfiles,
    AxisDirection.polylineFirstDirection,
    AxisDirection.between, AxisDirection.clockwiseRank,
    orderedCycleProfiles, implicationProfile,
    UnaryProgramClauseProfile.current, zeroCell]

/-- The complete phase-major expansion has the incoming ordered profiles,
then one exact routed ring-profile block per incoming variable. -/
theorem clauseProfiles_shape_descriptors_exact
    (source : List FormulaShapeDirectionOrdering.Token) :
    FormulaShape.clauseProfiles
        (FormulaShapeDirectionOrdering.shape (descriptors source)) =
      FormulaShape.clauseProfiles
          (FormulaShapeDirectionOrdering.shape source) ++
        (sourceVariableMarkers source).flatMap fun _ =>
          orderedCycleProfiles := by
  rw [clauseProfiles_shape_descriptors]
  simp only [clauseProfiles_shape_cycleClauseDescriptors]

end LeanTrominoes.PeriodicCNF.FormulaShapeFixedEightDirection
