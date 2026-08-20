/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseHardnessPackaging

/-! # Raw source-symbol interface for sparse strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseSymbolStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Sparse strip target generated directly from raw source symbols. -/
def directSparseCompiledTrominoStripOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) : PeriodicStrip :=
  sparseCompiledTrominoStrip tromino
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)

@[simp] theorem directSparseCompiledTrominoStripOfSymbols_encode
    (tromino : Tromino) (input : Input) :
    directSparseCompiledTrominoStripOfSymbols decider tromino
        (encoding.encode input) =
      directSparseCompiledTrominoStrip decider tromino input := by
  simp [directSparseCompiledTrominoStripOfSymbols,
    directSparseCompiledTrominoStrip]

/-- Reinterpret a raw-symbol sparse compiler at the original source
encoding. -/
def directSparseCompiledTrominoStripPolyTimeOfSymbols
    (tromino : Tromino)
    (compiler : TM2ComputableInPolyTime id
      PeriodicStripFlatEncoding.finEncoding.encode
      (directSparseCompiledTrominoStripOfSymbols decider tromino)) :
    TM2ComputableInPolyTime encoding.encode
      PeriodicStripFlatEncoding.finEncoding.encode
      (directSparseCompiledTrominoStrip decider tromino) where
  tm := compiler.tm
  inputAlphabet := compiler.inputAlphabet
  outputAlphabet := compiler.outputAlphabet
  time := compiler.time
  outputsFun input := by
    rw [← directSparseCompiledTrominoStripOfSymbols_encode
      decider tromino input]
    exact compiler.outputsFun (encoding.encode input)

/-- Uniform raw-symbol sparse compiler contract. -/
def DirectSparseCompiledTrominoStripSymbolMachines : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime id
        PeriodicStripFlatEncoding.finEncoding.encode
        (directSparseCompiledTrominoStripOfSymbols decider tromino))

theorem directSparseMachines_of_symbolMachines
    (machines : DirectSparseCompiledTrominoStripSymbolMachines) :
    DirectSparseCompiledTrominoStripMachines := by
  intro Input encoding language decider tromino
  exact (machines encoding language decider tromino).map
    (directSparseCompiledTrominoStripPolyTimeOfSymbols decider tromino)

end PeriodicCNFStripReduction
end LeanTrominoes
