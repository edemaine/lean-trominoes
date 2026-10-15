/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalDirectionCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalDirectionGlobalSemantics

/-! # Compiler for the semantic final direction projection -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalDirectionSemanticCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The existing five-family direction compiler computes the exact semantic
direction projection of the authoritative final coordinates. -/
noncomputable def
    directSourceFinalActualTerminalDirectionRanksComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (fun symbols =>
        directionRanks
          (coordinates
            (PeriodicOrthocrossing.finalCoordinatedSource
              (directSourceFormula decider symbols)).erase
            (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
              (directSourceFormula decider symbols)))) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalTerminalDirectionRanksComputableInPolyTime decider)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTerminalDirectionRanks_eq_globalCoordinates
        decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
