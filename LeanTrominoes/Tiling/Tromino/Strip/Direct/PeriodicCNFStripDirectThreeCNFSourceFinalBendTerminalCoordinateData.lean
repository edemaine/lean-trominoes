/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Bend.RetainedAngularFanFinalBendNumericTerminalColumnSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Clause.PeriodicCNFStripDirectSourceFinalClauseFamilies

/-! # Named bend coordinate streams of the direct width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directThreeBendCoordinateDataOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Compiler-ordered bend coordinates of the direct width-three source. -/
def directThreeCNFSourceBendCompiledCoordinates
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  let retained := PeriodicThreeSATThree.formula
    (directThreeCNFSourceFormula decider symbols)
  baseBendTerminalCoordinates retained

/-- Actual final bend-family coordinates of the same source. -/
def directThreeCNFSourceFinalBendActualCoordinates
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  let source := directThreeCNFSourceFormula decider symbols
  let retained := PeriodicThreeSATThree.formula source
  retainedFinalTerminalCoordinatesFrom
    (finalCoordinatedSourceRoutes retained)
    ((crossoverMetadataNormalizedClausesDedup retained).length +
      (PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
        source).length)
    (PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source)

end LeanTrominoes.PeriodicCNFStripReduction

end
