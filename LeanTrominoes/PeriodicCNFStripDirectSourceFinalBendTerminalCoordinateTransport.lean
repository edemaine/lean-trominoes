/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalBendTerminalCoordinateData
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Transport of final bend coordinates to public direct-source names -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBendCoordinateTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directBendCoordinateTransportVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The public direct-source bend coordinate family is the raw width-three
family used by the pointwise semantic proof. -/
theorem directSourceFinalBendActualCoordinates_eq_raw
    (symbols : List encoding.Γ) :
    retainedFinalTerminalCoordinatesFrom
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols))
        (directSourceFinalBendStart decider symbols)
        (directSourceFinalBendClauses decider symbols) =
      directThreeCNFSourceFinalBendActualCoordinates
        decider symbols := by
  unfold directSourceFinalBendStart directSourceFinalCarrierStart
    directSourceFinalCrossoverClauses directSourceFinalCarrierClauses
    directSourceFinalBendClauses
  rw [directSourceFormula_eq_finalNormalized]
  unfold directSourceFinalNormalizedFormula
    directThreeCNFSourceFinalBendActualCoordinates
  exact decidableEq_application_irrel
    (fun decEq : DecidableEq Variable =>
      retainedFinalTerminalCoordinatesFrom
        (@PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          Variable decEq
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols)))
        ((@crossoverMetadataNormalizedClausesDedup
            Variable decEq
            (PeriodicThreeSATThree.formula
              (directThreeCNFSourceFormula decider symbols))).length +
          (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
            (directThreeCNFSourceFormula decider symbols)).length)
        (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
          (directThreeCNFSourceFormula decider symbols)))
    directSourceVariableDecidableEq
    PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
