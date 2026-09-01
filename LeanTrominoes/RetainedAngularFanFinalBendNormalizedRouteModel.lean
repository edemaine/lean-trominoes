/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendFallbackRouteModel
import LeanTrominoes.RetainedAngularFanFinalBendPublicFallbackRoute
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily

/-! # Public normalized-route model for final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- At an indexed retained bend, the public normalized route is the
normalized ordinary Figure 7 splice with the exact bend terminal. -/
theorem FinalBendIndexedOccurrence.publicNormalizedRoute_eq_model
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        occurrence.retained occurrence.clauseIndex occurrence.literalIndex =
      AxisDirection.normalizeOrthogonalPolyline
        (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
          occurrence.scaledRoute
          (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
            (bendRouteTerminalData occurrence.taggedBend.1.incomingPort
              occurrence.taggedBend.1.outgoingPort
              occurrence.localClauseIndex occurrence.literalIndex))
          occurrence.slot) := by
  unfold
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
  rw [occurrence.publicCoordinatedRoute_eq_fallback]
  rw [occurrence.fallbackOccurrenceRoute_eq_model]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
