/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierNumericTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilies

/-! # Named carrier coordinate streams of the direct width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directThreeCarrierCoordinateDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directThreeCarrierCoordinateDataOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Descriptor-compiled carrier coordinates of the direct width-three
source. -/
def directThreeCNFSourceCarrierCompiledCoordinates
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  let retained := PeriodicThreeSATThree.formula
    (directThreeCNFSourceFormula decider symbols)
  List.map retainedTerminalDataCoordinate
    (CarrierRankOrderedPairs.retainedTerminalDataBlocks
      (numericRouteDescriptors retained)).flatten

/-- Actual final carrier-family coordinates of the same source. -/
def directThreeCNFSourceFinalCarrierActualCoordinates
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  let source := directThreeCNFSourceFormula decider symbols
  let retained := PeriodicThreeSATThree.formula source
  retainedFinalTerminalCoordinatesFrom
    (finalCoordinatedSourceRoutes retained)
    (crossoverMetadataNormalizedClausesDedup retained).length
    (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses source)

end LeanTrominoes.PeriodicCNFStripReduction

end
