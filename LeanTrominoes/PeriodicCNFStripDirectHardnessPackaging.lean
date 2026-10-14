/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.GadgetStripReduction
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.PeriodicCNFStripCompiledTromino

/-! # Direct PSPACE-source packaging for strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compose the established PSPACE-to-local-CNF formula with the verified
semantic tromino-strip compiler. -/
def directCompiledTrominoStrip (tromino : Tromino) (input : Input) :
    PeriodicStrip :=
  compiledTrominoStrip tromino
    (PeriodicCNF.ProgramSource.formula decider input)

theorem directCompiledTrominoStrip_correct
    (tromino : Tromino)
    (behavior : Gadget.OrientationBehaviorCorrect tromino)
    (input : Input) :
    language input ↔
      PeriodicStripTrominoTiling tromino
        (directCompiledTrominoStrip decider tromino input) := by
  exact
    (PeriodicCNF.ProgramSource.mem_iff_localPeriodicCNF1DSAT
      decider input).trans
      (compiledTrominoStrip_correct tromino behavior
        (PeriodicCNF.ProgramSource.formula decider input))

/-- A direct machine for the bounded generated formulas gives the required
many-one reduction without implementing the general local-CNF guard. -/
theorem directPolyTimeManyOneReducible
    (tromino : Tromino)
    (behavior : Gadget.OrientationBehaviorCorrect tromino)
    (compiler : Nonempty
      (TM2ComputableInPolyTime encoding.encode
        PeriodicStripFlatEncoding.finEncoding.encode
        (directCompiledTrominoStrip decider tromino))) :
    Complexity.PolyTimeManyOneReducible encoding
      PeriodicStripFlatEncoding.finEncoding language
      (PeriodicStripTrominoTiling tromino) := by
  exact Complexity.PolyTimeManyOneReducible.of_computableInPolyTime
    (directCompiledTrominoStrip decider tromino) compiler
    (directCompiledTrominoStrip_correct decider tromino behavior)

/-- Uniform machine contract on the highly structured formulas emitted by
the existing PSPACE reduction. -/
def DirectCompiledTrominoStripMachines : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.LeanTrominoes.FiniteEncoding Input)
      (language : Input → Prop)
      (decider : PeriodicCNF.ProgramSource encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime encoding.encode
        PeriodicStripFlatEncoding.finEncoding.encode
        (directCompiledTrominoStrip decider tromino))

theorem periodicStripTrominoTiling_PSPACEHard_of_directMachines
    (machines : DirectCompiledTrominoStripMachines)
    (tromino : Tromino)
    (behavior : Gadget.OrientationBehaviorCorrect tromino) :
    Complexity.PSPACEHard PeriodicStripFlatEncoding.finEncoding
      (PeriodicStripTrominoTiling tromino) := by
  intro Input encoding language sourceInPSPACE
  obtain ⟨decider⟩ := sourceInPSPACE
  let source := PeriodicCNF.ProgramSource.ofDecider decider
  exact directPolyTimeManyOneReducible (encoding := encoding) (language := language)
    source tromino behavior (machines encoding language source tromino)

/-- Direct bounded-formula machines plus the existing target membership prove
the full strip half of Theorem 5.2. -/
theorem theorem52_stripStatement_of_directMachines
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (machines : DirectCompiledTrominoStripMachines) :
    Theorem52.stripStatement := by
  intro tromino
  refine ⟨membership tromino, ?_⟩
  cases tromino with
  | I =>
      exact periodicStripTrominoTiling_PSPACEHard_of_directMachines
        machines .I Gadget.iOrientationBehaviorCorrect
  | L =>
      exact periodicStripTrominoTiling_PSPACEHard_of_directMachines
        machines .L Gadget.lOrientationBehaviorCorrect

end PeriodicCNFStripReduction
end LeanTrominoes
