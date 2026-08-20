/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectHardnessPackaging

/-! # Raw source-symbol interface for direct strip hardness -/

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

/-- Compile directly from the original encoded source symbols through the
bounded periodic-CNF formula template and the verified tromino geometry. -/
def directCompiledTrominoStripOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) : PeriodicStrip :=
  compiledTrominoStrip tromino
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)

@[simp] theorem directCompiledTrominoStripOfSymbols_encode
    (tromino : Tromino) (input : Input) :
    directCompiledTrominoStripOfSymbols decider tromino
        (encoding.encode input) =
      directCompiledTrominoStrip decider tromino input := by
  simp [directCompiledTrominoStripOfSymbols,
    directCompiledTrominoStrip]

/-- Reinterpret a raw-symbol compiler machine as the direct semantic
PSPACE-source reduction machine. -/
def directCompiledTrominoStripPolyTimeOfSymbols
    (tromino : Tromino)
    (compiler :
      TM2ComputableInPolyTime id
        PeriodicStripFlatEncoding.finEncoding.encode
        (directCompiledTrominoStripOfSymbols decider tromino)) :
    TM2ComputableInPolyTime encoding.encode
      PeriodicStripFlatEncoding.finEncoding.encode
      (directCompiledTrominoStrip decider tromino) where
  tm := compiler.tm
  inputAlphabet := compiler.inputAlphabet
  outputAlphabet := compiler.outputAlphabet
  time := compiler.time
  outputsFun input := by
    rw [← directCompiledTrominoStripOfSymbols_encode
      decider tromino input]
    exact compiler.outputsFun (encoding.encode input)

/-- Uniform raw-symbol machine contract, matching the polynomial emitter
pipelines already used by the periodic-CNF PSPACE reduction. -/
def DirectCompiledTrominoStripSymbolMachines : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime id
        PeriodicStripFlatEncoding.finEncoding.encode
        (directCompiledTrominoStripOfSymbols decider tromino))

theorem directMachines_of_symbolMachines
    (machines : DirectCompiledTrominoStripSymbolMachines) :
    DirectCompiledTrominoStripMachines := by
  intro Input encoding language decider tromino
  exact (machines encoding language decider tromino).map
    (directCompiledTrominoStripPolyTimeOfSymbols decider tromino)

/-- Uniform raw-symbol compilers therefore suffice for the complete strip
statement. -/
theorem theorem52_stripStatement_of_directSymbolMachines
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (machines : DirectCompiledTrominoStripSymbolMachines) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_directMachines membership
    (directMachines_of_symbolMachines machines)

end PeriodicCNFStripReduction
end LeanTrominoes
