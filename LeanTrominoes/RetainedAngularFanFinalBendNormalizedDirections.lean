/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendCornerGeometry
import LeanTrominoes.RetainedAngularFanFinalBendNormalizedRouteModel
import LeanTrominoes.RetainedAngularFanFinalBendRouteNormalizedDirectionExtensionality
import LeanTrominoes.RetainedAngularFanFinalBendScaledRouteEvidence

/-! # Exact public normalized direction words for final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The public normalized route of an indexed final bend has exactly the
finite compiler's normalized bend direction word. -/
theorem FinalBendIndexedOccurrence.publicNormalizedDirections_eq
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    Gadget.unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          occurrence.retained occurrence.clauseIndex occurrence.literalIndex) =
      bendRouteNormalizedFallbackDirections
        occurrence.taggedBend.1.incomingPort
        occurrence.taggedBend.1.outgoingPort
        occurrence.localClauseIndex occurrence.literalIndex occurrence.slot := by
  rw [occurrence.publicNormalizedRoute_eq_model]
  exact occurrence.scaledRoute_evidence.normalizedDirections
    occurrence.taggedBend.1.incomingPort
    occurrence.taggedBend.1.outgoingPort occurrence.portsDifferent
    occurrence.localClauseIndex occurrence.literalIndex occurrence.slot
    occurrence.scaledRoute

end PeriodicEightOccurrenceSplit
end LeanTrominoes
