/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalCarrierTerminalCoordinateData
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Transport of final carrier coordinates to public direct-source names -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCoordinateTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCarrierCoordinateTransportVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The public direct-source carrier coordinate family is the raw
width-three family used by the pointwise semantic proof. -/
theorem directSourceFinalCarrierActualCoordinates_eq_raw
    (symbols : List encoding.Γ) :
    retainedFinalTerminalCoordinatesFrom
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols))
        (directSourceFinalCarrierStart decider symbols)
        (directSourceFinalCarrierClauses decider symbols) =
      directThreeCNFSourceFinalCarrierActualCoordinates
        decider symbols := by
  unfold directSourceFinalCarrierStart directSourceFinalCrossoverClauses
    directSourceFinalCarrierClauses
  rw [directSourceFormula_eq_finalNormalized]
  unfold directSourceFinalNormalizedFormula
    directThreeCNFSourceFinalCarrierActualCoordinates
  exact decidableEq_application_irrel
    (fun decEq : DecidableEq Variable =>
      retainedFinalTerminalCoordinatesFrom
        (@PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          Variable decEq
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols)))
        (@crossoverMetadataNormalizedClausesDedup
          Variable decEq
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))).length
        (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
          (directThreeCNFSourceFormula decider symbols)))
    directSourceVariableDecidableEq
    PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
