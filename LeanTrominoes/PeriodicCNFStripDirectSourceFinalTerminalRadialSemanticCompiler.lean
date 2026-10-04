/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalRadialCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalRadialGlobalSemantics

/-! # Compiler for the semantic final radial projection -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalRadialSemanticCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The existing five-family radial compiler computes the exact semantic
radial projection of the authoritative final coordinates. -/
noncomputable def
    directSourceFinalActualTerminalRadialLengthsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (fun symbols =>
        radialLengths
          (coordinates
            (PeriodicOrthocrossing.finalCoordinatedSource
              (directSourceFormula decider symbols)).erase
            (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
              (directSourceFormula decider symbols)))) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalTerminalRadialLengthsComputableInPolyTime decider)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTerminalRadialLengths_eq_globalCoordinates
        decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
