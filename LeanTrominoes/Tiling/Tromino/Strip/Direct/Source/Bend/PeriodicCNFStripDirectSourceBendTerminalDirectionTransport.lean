/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Base.PeriodicCNFStripDirectSourceBaseBendTerminalColumnData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Clause.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedAngularBendTerminalCoordinateData
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Transport of direct bend direction data to the width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directBendDirectionTransportVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Replacing the public final formula and equality implementation by the
raw five-family boundary leaves the bend direction stream unchanged. -/
theorem directSourceBaseBendTerminalDirectionRanks_eq_raw
    (symbols : List encoding.Γ) :
    directSourceBaseBendTerminalDirectionRanks decider symbols =
      @baseBendTerminalDirectionRanks Variable
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
        (directSourceFinalNormalizedFormula decider symbols) := by
  change @baseBendTerminalDirectionRanks Variable
      directSourceVariableDecidableEq
      (directSourceFormula decider symbols) = _
  calc
    @baseBendTerminalDirectionRanks Variable
          directSourceVariableDecidableEq
          (directSourceFormula decider symbols) =
        @baseBendTerminalDirectionRanks Variable
          directSourceVariableDecidableEq
          (directSourceFinalNormalizedFormula decider symbols) :=
      congrArg
        (@baseBendTerminalDirectionRanks Variable
          directSourceVariableDecidableEq)
        (directSourceFormula_eq_finalNormalized decider symbols)
    _ = _ :=
      decidableEq_application_irrel
        (fun decEq : DecidableEq Variable =>
          @baseBendTerminalDirectionRanks Variable decEq
            (directSourceFinalNormalizedFormula decider symbols))
        directSourceVariableDecidableEq
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
