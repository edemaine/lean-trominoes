/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPixelFiniteTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseCountedTokenSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparsePreparedTokenSemantics
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Machine bridge from sparse prepared tokens to flat strips -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparsePreparedBridgeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private theorem targetFlatEncoding_eq_trList_stripFields
    (strip : PeriodicStrip) :
    PeriodicStripFlatEncoding.finEncoding.encode strip =
      PartrecToTM2.trList (PeriodicStripFlatEncoding.stripFields strip) :=
  PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _

/-- Any polynomial-time emitter for the sparse prepared stream composes with
the three verified fixed postprocessors to compute the exact flat strip. -/
def directSparseCompiledTrominoStripPolyTimeOfPreparedTokenEmitter
    (tromino : Tromino)
    (emitter : TM2ComputableInPolyTime id id
      (directSparseCompiledTrominoStripPreparedTokensOfSymbols
        decider tromino)) :
    TM2ComputableInPolyTime id
      PeriodicStripFlatEncoding.finEncoding.encode
      (directSparseCompiledTrominoStripOfSymbols decider tromino) := by
  let counted :=
    GadgetPixelFiniteTokenCompiler.computableInPolyTimeOfEmitter emitter
      (fun symbols =>
        expand_directSparseCompiledTrominoStripPreparedTokensOfSymbols
          decider tromino symbols)
  let unary :=
    CountedUnaryFieldTokenCompiler.computableInPolyTimeOfEmitter counted
      (fun symbols =>
        postprocess_directSparseCompiledTrominoStripCountedTokensOfSymbols
          decider tromino symbols)
  let encoded := TM2CompositionMachine.computableInPolyTime unary
    UnaryFieldEncoderMachine.computableInPolyTime
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq encoded ?_
  intro symbols
  rw [targetFlatEncoding_eq_trList_stripFields]
  simp only [id_eq]

end PeriodicCNFStripReduction
end LeanTrominoes
