/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Theorem52Proof
import LeanTrominoes.Tiling.Polyomino.Theorem55StripUnaryCompiler

/-! # Unary hard-source machines for the two-tile strip reduction -/

noncomputable section
namespace LeanTrominoes.Theorem55StripHardSource
open Computability Turing PeriodicCNFStripReduction

variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
    {language : Input → Prop} (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

def symbolCompiler : TM2ComputableInPolyTime id Theorem55StripUnary.encode
    (directSparseCompiledTrominoStripOfSymbols (PeriodicCNF.ProgramSource.ofDecider decider) .I) := by
  let emitters : DirectSparseCompiledTrominoStripPreparedTokenEmitters := directSparseCompiledTrominoStripPreparedTokenEmitters_of_assignmentRecordEmitters
    (directSparseAssignmentRecordEmitters_of_splitAppenders directSparseSplitRecordAppenders)
  let emitter := Classical.choice (emitters encoding language decider .I)
  let counted := GadgetPixelFiniteTokenCompiler.computableInPolyTimeOfEmitter emitter
    (fun symbols => expand_directSparseCompiledTrominoStripPreparedTokensOfSymbols (PeriodicCNF.ProgramSource.ofDecider decider) .I symbols)
  let unary := CountedUnaryFieldTokenCompiler.computableInPolyTimeOfEmitter counted
    (fun symbols => postprocess_directSparseCompiledTrominoStripCountedTokensOfSymbols (PeriodicCNF.ProgramSource.ofDecider decider) .I symbols)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq unary (fun _ => rfl)

/-- Stop the established hard-source compiler before its final binary encoder. -/
def compiler : TM2ComputableInPolyTime encoding.encode Theorem55StripUnary.encode
    (directSparseCompiledTrominoStrip (PeriodicCNF.ProgramSource.ofDecider decider) .I) where
  tm := (symbolCompiler decider).tm
  inputAlphabet := (symbolCompiler decider).inputAlphabet
  outputAlphabet := (symbolCompiler decider).outputAlphabet
  time := (symbolCompiler decider).time
  outputsFun input := by
    rw [← directSparseCompiledTrominoStripOfSymbols_encode (PeriodicCNF.ProgramSource.ofDecider decider) .I input]
    exact (symbolCompiler decider).outputsFun (encoding.encode input)

theorem sparse_wellFormed (source : PeriodicCNF Nat) :
    (sparseCompiledTrominoStrip .I source).IsWellFormed := by
  unfold sparseCompiledTrominoStrip normalizationInput
  rw [PeriodicThreeDM.NormalizationCompiler.compileSparseStrip_inputOfPresentation]
  exact (presentation source).sparsePeriodicStrip_isWellFormed
    (presentation source).problemWellFormed (problem_degreeTwoOrThree source)
    (problem_isOneDimensional source) (presentation_routePointsInExpandedVerticalBand source)
    (presentation_separated source) (presentation_routesSimple source) .I

theorem wellFormed (input : Input) :
    (directSparseCompiledTrominoStrip (PeriodicCNF.ProgramSource.ofDecider decider) .I input).IsWellFormed :=
  sparse_wellFormed _

end LeanTrominoes.Theorem55StripHardSource
