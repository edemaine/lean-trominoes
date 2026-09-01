/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSplicedRouteValidity
import LeanTrominoes.RetainedAngularFanFinalBendCornerGeometry
import LeanTrominoes.RetainedAngularFanFinalBendNormalizedRouteModel
import LeanTrominoes.RetainedAngularFanFinalBendScaledRouteEvidence

/-! # Unit steps of public final retained-bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The public normalized route at an indexed final bend consists of unit
lattice steps. -/
theorem FinalBendIndexedOccurrence.publicRouteUnitSteps
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      occurrence.retained occurrence.clauseIndex
      occurrence.literalIndex).IsChain AxisDirection.IsUnitAxisStep := by
  rw [occurrence.publicNormalizedRoute_eq_model]
  let terminal := scaleRetainedTerminalData
    retainedAngularFanSourceClearanceFactor
    (bendRouteTerminalData occurrence.taggedBend.1.incomingPort
      occurrence.taggedBend.1.outgoingPort occurrence.localClauseIndex
      occurrence.literalIndex)
  have certificate := bendRouteCardinalTangentCertificate_of_ne
    occurrence.taggedBend.1.incomingPort
    occurrence.taggedBend.1.outgoingPort occurrence.portsDifferent
    occurrence.localClauseIndex occurrence.literalIndex
    occurrence.localClauseIndex.isLt occurrence.literalIndex.isLt
  have terminalPositive : 0 < terminal.2 := by
    exact scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos
      certificate.terminalLengthPositive
  have valid : RetainedFallbackFanKind.ordinary.Valid terminal := by
    trivial
  have evidence := occurrence.scaledRoute_evidence
  have fullValid :=
    RetainedFallbackFanKind.splicedOwnFigure7Route_valid .ordinary
      occurrence.scaledRoute terminal occurrence.slot
      evidence.routeLength evidence.routeClassified
      evidence.routeOrthogonal terminalPositive valid
  exact AxisDirection.normalizeOrthogonalPolyline_unitSteps
    fullValid.1 fullValid.2

end PeriodicEightOccurrenceSplit
end LeanTrominoes
