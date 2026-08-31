/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedSemanticModelRouteUnitSteps

/-! # Unit steps of public final retained-carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The public normalized route at an indexed final carrier consists of unit
lattice steps. -/
theorem FinalCarrierIndexedOccurrence.publicRouteUnitSteps
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      occurrence.retained occurrence.clauseIndex
      occurrence.literalIndex).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold FinalCarrierIndexedOccurrence.retained
  rw [retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_carrier_eq_model
    occurrence.source occurrence.sourceLocal occurrence.sourceWidth
    occurrence.sourceClausesNonempty occurrence.positiveOffsets
    occurrence.taggedLink occurrence.clauseIndex
    occurrence.taggedLinkIndexed occurrence.clauseMember
    occurrence.literalIndex occurrence.literalMember]
  have decEq :
      (finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq :
        DecidableEq (ThreeOccurrenceVariable Variable)) =
        drawingOrderedThreeOccurrenceVariableInstDecidableEq :=
    Subsingleton.elim _ _
  have unitSteps := occurrence.semanticFallbackRouteUnitSteps nextSlice
  rw [← decEq] at unitSteps
  exact unitSteps

end PeriodicEightOccurrenceSplit
end LeanTrominoes
