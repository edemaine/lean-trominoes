/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidence

/-! # Scaled-route evidence at indexed final carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- The indexed-occurrence package supplies its four scaled-route facts. -/
theorem FinalCarrierIndexedOccurrence.scaledRouteEvidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    occurrence.ScaledRouteEvidence :=
  finalCarrierScaledRoute_evidence
    occurrence.source occurrence.sourceLocal occurrence.sourceWidth
    occurrence.sourceClausesNonempty occurrence.positiveOffsets
    occurrence.taggedLink occurrence.clauseIndex
    occurrence.taggedLinkIndexed occurrence.clauseMember
    occurrence.literalIndex occurrence.literalMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
