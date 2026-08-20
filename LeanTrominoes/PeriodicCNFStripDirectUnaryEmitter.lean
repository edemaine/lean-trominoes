/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSymbolCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Unary-field emitter interface for direct strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Natural target fields produced directly from source symbols. -/
def directCompiledTrominoStripFieldsOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) : List Nat :=
  PeriodicStripFlatEncoding.stripFields
    (directCompiledTrominoStripOfSymbols decider tromino symbols)

private theorem targetFlatEncoding_eq_trList_stripFields
    (strip : PeriodicStrip) :
    PeriodicStripFlatEncoding.finEncoding.encode strip =
      PartrecToTM2.trList
        (PeriodicStripFlatEncoding.stripFields strip) := by
  exact PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _

/-- Compose a unary target-field emitter with the verified unary-to-native
binary field encoder, then present the result at the semantic strip codomain. -/
def directCompiledTrominoStripPolyTimeOfUnaryFieldEmitter
    (tromino : Tromino)
    (emitter :
      TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
        (directCompiledTrominoStripFieldsOfSymbols decider tromino)) :
    TM2ComputableInPolyTime id
      PeriodicStripFlatEncoding.finEncoding.encode
      (directCompiledTrominoStripOfSymbols decider tromino) := by
  let encoded := TM2CompositionMachine.computableInPolyTime
    emitter UnaryFieldEncoderMachine.computableInPolyTime
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq encoded ?_
  intro symbols
  rw [targetFlatEncoding_eq_trList_stripFields]
  simp only [id_eq,
    directCompiledTrominoStripFieldsOfSymbols]

/-- Uniform unary-field emitter contract.  This is the interface implemented
by the existing affine, bivariate, and triangular polynomial-time template
machines. -/
def DirectCompiledTrominoStripUnaryFieldEmitters : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
        (directCompiledTrominoStripFieldsOfSymbols decider tromino))

theorem symbolMachines_of_unaryFieldEmitters
    (emitters : DirectCompiledTrominoStripUnaryFieldEmitters) :
    DirectCompiledTrominoStripSymbolMachines := by
  intro Input encoding language decider tromino
  exact (emitters encoding language decider tromino).map
    (directCompiledTrominoStripPolyTimeOfUnaryFieldEmitter
      decider tromino)

/-- Uniform unary-field emitters plus target membership prove the complete
strip half of Theorem 5.2. -/
theorem theorem52_stripStatement_of_directUnaryFieldEmitters
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (emitters : DirectCompiledTrominoStripUnaryFieldEmitters) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_directSymbolMachines membership
    (symbolMachines_of_unaryFieldEmitters emitters)

end PeriodicCNFStripReduction
end LeanTrominoes
