/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendRawRoutePrefixDirectionSemantics
import LeanTrominoes.RetainedAngularFanFinalBendScaledClassification
import LeanTrominoes.RetainedAngularFanFinalBendScaledOrthogonality
import LeanTrominoes.RetainedAngularFanFinalBendScaledRouteEvidenceData
import LeanTrominoes.RetainedAngularFanFinalThreeSATThreeScaledRouteLength

/-! # Collected scaled-route evidence for final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Indexed bend membership supplies all four source-side facts. -/
theorem FinalBendIndexedOccurrence.scaledRoute_evidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    FinalBendScaledRouteEvidence occurrence.scaledRoute
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (bendRouteTerminalData
          occurrence.taggedBend.1.incomingPort
          occurrence.taggedBend.1.outgoingPort
          occurrence.localClauseIndex occurrence.literalIndex))
      (Gadget.repeatDirections 1152
        (bendRoutePrefixDirections
          occurrence.taggedBend.1.incomingPort
          occurrence.taggedBend.1.outgoingPort
          occurrence.localClauseIndex occurrence.literalIndex)) := by
  exact ⟨
    finalCoordinatedScaledThreeSATThreeSourceRoute_length_ge_two
      occurrence.source occurrence.sourceLocal occurrence.sourceWidth
      occurrence.sourceClausesNonempty occurrence.clauseMember
      occurrence.literalMember,
    occurrence.scaledRoute_classified,
    occurrence.scaledRoute_orthogonal,
    occurrence.fallbackSourcePrefixDirections⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
