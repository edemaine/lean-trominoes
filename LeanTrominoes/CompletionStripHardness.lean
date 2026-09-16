/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripHardnessCompiler
import LeanTrominoes.CompletionStripSourceReduction
import LeanTrominoes.CompletionStripMembership

/-! # PSPACE completeness of periodic strip tromino completion

The reduction uses the explicit unary encoding of the height, period, and
prescribed motif. Satisfying completions need not be periodic.
-/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
  {language : Input → Prop} (decider : Complexity.DeciderInPolySpace encoding language)

/-- The empty source alphabet has only one symbol word and is compiled by a
constant-output machine. No inhabited-alphabet premise remains. -/
def sourceCompletionCompilerTotal (t : Tromino) :
    TM2ComputableInPolyTime id CompletionStripEncoding.finEncoding.encode
      (fun s => StripOrientation.compile t (sourceDrawing decider s)) := by
  classical
  by_cases existsSymbol : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice existsSymbol⟩
    exact sourceCompletionCompiler decider t
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => existsSymbol ⟨symbol⟩⟩
    letI : Inhabited CompletionStripEncoding.finEncoding.Γ := ⟨false⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime CompletionStripEncoding.finEncoding.encode _

/-- End-to-end certificate from an arbitrary PSPACE source encoding to the
actual finite strip-completion input. -/
def sourceReductionCompiler (t : Tromino) :
    TM2ComputableInPolyTime encoding.encode CompletionStripEncoding.finEncoding.encode
      (StripOrientation.compileSource decider t) := by
  apply TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (sourceCompletionCompilerTotal decider t)
    (fun _ => rfl)
  intro input
  unfold sourceDrawing PeriodicCNFStripReduction.directCompiledStripDrawingOfSymbols
    StripOrientation.compileSource StripOrientation.compileCNF
  rw [PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
end LeanTrominoes.CompletionPattern.Runtime

namespace LeanTrominoes.PeriodicStripTrominoPrefill

/-- Periodic completion by either tromino in a horizontal strip is PSPACE-hard. -/
theorem problem_PSPACEHard (t : Tromino) :
    Complexity.PSPACEHard CompletionStripEncoding.finEncoding (problem t) := by
  intro Input encoding language sourceInPSPACE
  obtain ⟨decider⟩ := sourceInPSPACE
  exact Complexity.PolyTimeManyOneReducible.of_computableInPolyTime
    (CompletionPattern.StripOrientation.compileSource decider t)
    ⟨CompletionPattern.Runtime.sourceReductionCompiler decider t⟩
    (fun input => (CompletionPattern.StripOrientation.compileSource_correct decider t input).symm)

/-- Both L- and I-tromino periodic horizontal-strip completion are PSPACE-complete
under the explicit unary geometric encoding. -/
theorem problem_PSPACEComplete (t : Tromino) :
    Complexity.PSPACEComplete CompletionStripEncoding.finEncoding (problem t) :=
  ⟨problem_inPSPACE t,problem_PSPACEHard t⟩
end LeanTrominoes.PeriodicStripTrominoPrefill
