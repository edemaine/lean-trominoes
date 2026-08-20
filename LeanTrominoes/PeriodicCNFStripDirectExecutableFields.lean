/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectUnaryEmitter
import LeanTrominoes.GadgetStripFlatFields

/-! # Proof-free target fields for direct strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Rectangular normalized drawing generated directly from source symbols. -/
def directCompiledStripDrawingOfSymbols (symbols : List encoding.Γ) :
    PeriodicOrthogonalDrawing :=
  compiledStripDrawing
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- Natural-range enumeration of all fixed gadget pixels in that drawing. -/
def directCompiledTrominoMotifOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) : List Cell :=
  (directCompiledStripDrawingOfSymbols decider symbols)
    |>.computableExpandedMotif tromino

theorem directCompiledTrominoMotifOfSymbols_eq
    (tromino : Tromino) (symbols : List encoding.Γ) :
    directCompiledTrominoMotifOfSymbols decider tromino symbols =
      Gadget.PeriodicOrthogonalDrawing.computableExpandedMotif tromino
        (directCompiledStripDrawingOfSymbols decider symbols) := by
  rfl

/-- Shallow proof-free target field generator.  It consists of two arithmetic
header fields followed by the row-major natural-range gadget-pixel loop. -/
def directExecutableTrominoStripFieldsOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) : List Nat :=
  (directCompiledStripDrawingOfSymbols decider symbols)
    |>.computablePeriodicStripFields tromino

/-- The proof-free loop nest emits exactly the fields of the semantic strip
used by the correctness reduction. -/
theorem directExecutableTrominoStripFieldsOfSymbols_eq
    (tromino : Tromino) (symbols : List encoding.Γ) :
    directExecutableTrominoStripFieldsOfSymbols decider tromino symbols =
      directCompiledTrominoStripFieldsOfSymbols decider tromino symbols := by
  unfold directExecutableTrominoStripFieldsOfSymbols
  rw [← Gadget.PeriodicOrthogonalDrawing.stripFields_computablePeriodicStrip]
  rw [Gadget.PeriodicOrthogonalDrawing.computablePeriodicStrip_eq]
  unfold directCompiledTrominoStripFieldsOfSymbols
  unfold directCompiledTrominoStripOfSymbols compiledTrominoStrip
  rfl

/-- It is enough for the machine to implement the shallow proof-free field
generator; equality transport recovers the exact semantic unary emitter. -/
def directCompiledTrominoStripPolyTimeOfExecutableUnaryFieldEmitter
    (tromino : Tromino)
    (emitter :
      TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
        (directExecutableTrominoStripFieldsOfSymbols decider tromino)) :
    TM2ComputableInPolyTime id
      PeriodicStripFlatEncoding.finEncoding.encode
      (directCompiledTrominoStripOfSymbols decider tromino) := by
  let semanticEmitter :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq emitter
      (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
        (directExecutableTrominoStripFieldsOfSymbols_eq
          decider tromino symbols))
  exact directCompiledTrominoStripPolyTimeOfUnaryFieldEmitter
    decider tromino semanticEmitter

/-- Uniform machine contract on the explicit natural-range target generator. -/
def DirectCompiledTrominoStripExecutableUnaryFieldEmitters : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
        (directExecutableTrominoStripFieldsOfSymbols decider tromino))

theorem unaryFieldEmitters_of_executableUnaryFieldEmitters
    (emitters : DirectCompiledTrominoStripExecutableUnaryFieldEmitters) :
    DirectCompiledTrominoStripUnaryFieldEmitters := by
  intro Input encoding language decider tromino
  exact (emitters encoding language decider tromino).map fun emitter =>
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq emitter
      (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
        (directExecutableTrominoStripFieldsOfSymbols_eq
          decider tromino symbols))

/-- Explicit natural-range unary emitters plus target membership prove the
complete strip half of Theorem 5.2. -/
theorem theorem52_stripStatement_of_directExecutableUnaryFieldEmitters
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (emitters : DirectCompiledTrominoStripExecutableUnaryFieldEmitters) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_directUnaryFieldEmitters membership
    (unaryFieldEmitters_of_executableUnaryFieldEmitters emitters)

end PeriodicCNFStripReduction
end LeanTrominoes
