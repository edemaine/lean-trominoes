/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedRouteNormalization
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedRouteEvidence
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedRouteDirectionModel

/-! # Normalized direction words of final retained-carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- At a genuine indexed retained-carrier occurrence, the public normalized
route has exactly the finite compiler direction word. -/
theorem FinalCarrierIndexedOccurrence.publicDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt occurrence.source
        occurrence.taggedLink nextSlice).span) :
    occurrence.PublicDirections nextSlice := by
  constructor
  have decEq :
      (finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq :
        DecidableEq (ThreeOccurrenceVariable Variable)) =
        drawingOrderedThreeOccurrenceVariableInstDecidableEq :=
    Subsingleton.elim _ _
  dsimp only
  have publicDirections :=
    occurrence.publicDirections_eq_semanticModel
      occurrence.routeDirectionEvidence
  have semanticDirections :=
    occurrence.semanticModelDirections occurrence.scaledRouteEvidence
      nextSlice spanLarge
  unfold FinalCarrierIndexedOccurrence.PublicDirectionsEqSemanticModel at publicDirections
  dsimp only at publicDirections
  unfold FinalCarrierIndexedOccurrence.SemanticModelDirections
    finalCarrierNamedSemanticModelDirections finalCarrierSemanticDirectionWord
    FinalCarrierIndexedOccurrence.scaledTerminalData
    finalCarrierActualScaledTerminalData
    FinalCarrierIndexedOccurrence.scaledRoute
    finalCarrierIndexedScaledRoute
    FinalCarrierIndexedOccurrence.slot
    FinalCarrierIndexedOccurrence.retained at semanticDirections
  rw [← decEq] at semanticDirections
  rw [publicDirections]
  exact semanticDirections

end PeriodicEightOccurrenceSplit
end LeanTrominoes
