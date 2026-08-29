/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalCarrierTerminalCoordinateData
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFacts
import LeanTrominoes.PeriodicCNFStripDirectSourceRetainedIncidencesNonempty

/-! # Carrier coordinates of the direct width-three source -/

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

noncomputable local instance directThreeFinalCarrierCoordinatesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directThreeFinalCarrierCoordinatesOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The generic final-carrier theorem specialized to the direct width-three
source, before rewriting to the public final-source family names. -/
theorem directThreeCNFSourceFinalCarrierTerminalCoordinates_eq_numeric
    (symbols : List encoding.Γ) :
    directThreeCNFSourceCarrierCompiledCoordinates decider symbols =
      directThreeCNFSourceFinalCarrierActualCoordinates
        decider symbols := by
  unfold directThreeCNFSourceCarrierCompiledCoordinates
    directThreeCNFSourceFinalCarrierActualCoordinates
  dsimp only
  symm
  exact finalCarrierTerminalCoordinates_eq_numeric
    (Variable := ThreeCNFVariable Nat)
    (directThreeCNFSourceFormula decider symbols)
    (directThreeCNFSource_isLocal decider symbols)
    (directThreeCNFSource_widthAtMostThree decider symbols)
    (directThreeCNFSource_clausesNonempty decider symbols)
    (directThreeCNFSource_positiveOffsets decider symbols)
    (directThreeCNFSource_retained_incidencesWithMetadata_ne_nil
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
