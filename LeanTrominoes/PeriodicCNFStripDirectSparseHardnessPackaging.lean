/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.PeriodicCNFStripSparseCompiledTromino

/-! # Direct PSPACE hardness through sparse strip presentations -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseHardnessStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct PSPACE-source reduction with the sparse assignment-order motif. -/
def directSparseCompiledTrominoStrip
    (tromino : Tromino) (input : Input) : PeriodicStrip :=
  sparseCompiledTrominoStrip tromino
    (PeriodicCNF.PolySpaceReduction.formula decider input)

theorem directSparseCompiledTrominoStrip_correct
    (tromino : Tromino)
    (behavior : Gadget.OrientationBehaviorCorrect tromino)
    (input : Input) :
    language input ↔ PeriodicStripTrominoTiling tromino
      (directSparseCompiledTrominoStrip decider tromino input) := by
  exact
    (PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT
      decider input).trans
      (sparseCompiledTrominoStrip_correct tromino behavior
        (PeriodicCNF.PolySpaceReduction.formula decider input))

/-- A polynomial-time sparse compiler supplies the desired many-one
reduction. -/
theorem directSparsePolyTimeManyOneReducible
    (tromino : Tromino)
    (behavior : Gadget.OrientationBehaviorCorrect tromino)
    (compiler : Nonempty
      (TM2ComputableInPolyTime encoding.encode
        PeriodicStripFlatEncoding.finEncoding.encode
        (directSparseCompiledTrominoStrip decider tromino))) :
    Complexity.PolyTimeManyOneReducible encoding
      PeriodicStripFlatEncoding.finEncoding language
      (PeriodicStripTrominoTiling tromino) :=
  Complexity.PolyTimeManyOneReducible.of_computableInPolyTime
    (directSparseCompiledTrominoStrip decider tromino) compiler
    (directSparseCompiledTrominoStrip_correct decider tromino behavior)

/-- Uniform sparse compiler contract for the remaining machine construction. -/
def DirectSparseCompiledTrominoStripMachines : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime encoding.encode
        PeriodicStripFlatEncoding.finEncoding.encode
        (directSparseCompiledTrominoStrip decider tromino))

/-- Sparse direct compilers plus the established membership theorem prove the
complete strip statement. -/
theorem theorem52_stripStatement_of_directSparseMachines
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (machines : DirectSparseCompiledTrominoStripMachines) :
    Theorem52.stripStatement := by
  intro tromino
  refine ⟨membership tromino, ?_⟩
  intro Input encoding language sourceInPSPACE
  obtain ⟨decider⟩ := sourceInPSPACE
  cases tromino with
  | I =>
      exact directSparsePolyTimeManyOneReducible decider .I
        Gadget.iOrientationBehaviorCorrect
        (machines encoding language decider .I)
  | L =>
      exact directSparsePolyTimeManyOneReducible decider .L
        Gadget.lOrientationBehaviorCorrect
        (machines encoding language decider .L)

end PeriodicCNFStripReduction
end LeanTrominoes
