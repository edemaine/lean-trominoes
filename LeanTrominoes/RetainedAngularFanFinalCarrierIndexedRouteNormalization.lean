/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteNormalizedDirectionExtensionality

/-! # Normalization of indexed final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  drawingOrderedThreeOccurrenceVariableInstDecidableEq

/-- Indexed route evidence proves the occurrence's semantic-model direction
statement. -/
theorem FinalCarrierIndexedOccurrence.semanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (evidence : occurrence.ScaledRouteEvidence)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt occurrence.source
        occurrence.taggedLink nextSlice).span) :
    occurrence.SemanticModelDirections nextSlice := by
  unfold FinalCarrierIndexedOccurrence.ScaledRouteEvidence at evidence
  have decEq :
      (finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq :
        DecidableEq (ThreeOccurrenceVariable Variable)) =
        drawingOrderedThreeOccurrenceVariableInstDecidableEq :=
    Subsingleton.elim _ _
  rw [decEq] at evidence
  let normalize :=
    FinalCarrierScaledRouteEvidence.withNormalizedActualSemanticModelDirections
      occurrence.source occurrence.taggedLink nextSlice spanLarge
      occurrence.literalIndex occurrence.slot
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          (PeriodicThreeSATThree.formula occurrence.source)
          occurrence.clauseIndex occurrence.literalIndex))
  exact normalize evidence
      (P := occurrence.SemanticModelDirections nextSlice)
      (fun directions => by
        rw [← decEq] at directions
        unfold FinalCarrierIndexedOccurrence.SemanticModelDirections
          FinalCarrierIndexedOccurrence.scaledTerminalData
          FinalCarrierIndexedOccurrence.scaledRoute
          finalCarrierIndexedScaledRoute
        exact directions)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
