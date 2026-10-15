/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierTerminalColumnData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Terminal.PeriodicOrthocrossingCarrierTerminalDirectionStreamSemantics

/-! # Direct retained-carrier terminal-direction data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

local instance directSourceCarrierTerminalDirectionDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The physical packed-span decoder has the semantic unary-column output. -/
theorem directSourceCarrierTerminalDirectionStream_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierTerminalDirectionStream decider symbols =
      UnaryFieldEncoderMachine.unaryFields
        (directSourceCarrierTerminalDirectionRanks decider symbols) := by
  unfold directSourceCarrierTerminalDirectionStream
    directSourceCarrierTerminalDirectionRanks
  exact
    CarrierRankOrderedPairs.directionRankStream_packedSpanStream_numericRouteDescriptors
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSourceFormula_isForwardLocal decider symbols)
      (directSource_incidencesWithMetadata_ne_nil decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
