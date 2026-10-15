/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectThreeCNFSourceFinalBendTerminalCoordinateData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectThreeCNFSourceFacts

/-! # Bend coordinates of the direct width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directThreeFinalBendCoordinatesOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The generic final-bend theorem specialized to the direct width-three
source, before rewriting to public final-source family names. -/
theorem directThreeCNFSourceFinalBendTerminalCoordinates_eq_numeric
    (symbols : List encoding.Γ) :
    directThreeCNFSourceBendCompiledCoordinates decider symbols =
      directThreeCNFSourceFinalBendActualCoordinates
        decider symbols := by
  unfold directThreeCNFSourceBendCompiledCoordinates
    directThreeCNFSourceFinalBendActualCoordinates
  dsimp only
  symm
  exact finalBendTerminalCoordinates_eq_numeric
    (Variable := ThreeCNFVariable Nat)
    (directThreeCNFSourceFormula decider symbols)
    (directThreeCNFSource_isLocal decider symbols)
    (directThreeCNFSource_widthAtMostThree decider symbols)
    (directThreeCNFSource_clausesNonempty decider symbols)
    (directThreeCNFSource_positiveOffsets decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
