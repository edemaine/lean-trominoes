/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionOrientationStripCompiler
import LeanTrominoes.PeriodicCNFStripCompiledDrawing
import LeanTrominoes.PeriodicCNFPolySpaceHardness

/-! # Correctness of the source-to-completion-strip construction

This file proves semantic equivalence. PSPACE hardness additionally requires
polynomial-time computation under the actual finite encodings.
-/
noncomputable section
namespace LeanTrominoes.CompletionPattern.StripOrientation
open PeriodicCNFStripReduction

def compileCNF (t : Tromino) (source : PeriodicCNF Nat) : PeriodicStripTrominoPrefill :=
  compile t (compiledStripDrawing source)

theorem compileCNF_correct (t : Tromino) (source : PeriodicCNF Nat) :
    PeriodicStripTrominoPrefill.problem t (compileCNF t source) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT source := by
  exact (compile_correct t _ (compiledStripDrawing_isWellFormed source)
    (compiledStripDrawing_hasBlankVerticalBoundary source)).trans
      (compiledStripDrawing_correct source).symm

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
  {language : Input → Prop}

def compileSource (decider : Complexity.DeciderInPolySpace encoding language)
    (t : Tromino) (input : Input) : PeriodicStripTrominoPrefill :=
  compileCNF t (PeriodicCNF.PolySpaceReduction.formula decider input)

theorem compileSource_correct (decider : Complexity.DeciderInPolySpace encoding language)
    (t : Tromino) (input : Input) :
    PeriodicStripTrominoPrefill.problem t (compileSource decider t input) ↔ language input :=
  (compileCNF_correct t _).trans
    (PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input).symm
end LeanTrominoes.CompletionPattern.StripOrientation
