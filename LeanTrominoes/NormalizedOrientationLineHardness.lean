/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationSparseCompiler
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Native PSPACE hardness of normalized one-dimensional orientation

The blank vertical boundary separates successive horizontal strips. All cell
colors and types, including the full supplied normalized drawing, are part of
the native input. The compiler does not substitute a tiling encoding.
-/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation
open Turing CompletionPattern.Runtime PeriodicCNFStripReduction

/-- Normalized planar orientation on a horizontally periodic strip. Malformed
cell tables, touching vertices, and nonblank vertical seams are rejected. -/
def LineProblem (drawing : PeriodicOrthogonalDrawing) : Prop :=
  drawing.VerticesSeparated ∧ drawing.HasBlankVerticalBoundary ∧ drawing.HasOrientation

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance orientationHardnessStack (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

def sourceEncodingCompilerTotal : TM2ComputableInPolyTime id FlatEncoding.finEncoding.encode (sourceDrawing decider) := by
  classical
  by_cases h : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice h⟩
    exact sourceEncodingCompiler decider
  · letI : IsEmpty encoding.Γ := ⟨fun x => h ⟨x⟩⟩
    letI : Inhabited FlatEncoding.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime FlatEncoding.finEncoding.encode _

theorem sourceDrawing_line_correct (s : List encoding.Γ) :
    LineProblem (sourceDrawing decider s) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
  constructor
  · intro h
    exact (compiledStripDrawing_correct _).2 h.2.2
  · intro h
    exact ⟨compiledStripDrawing_verticesSeparated _,compiledStripDrawing_hasBlankVerticalBoundary _,
      (compiledStripDrawing_correct _).1 h⟩

def lineReduction (input : Input) : PeriodicOrthogonalDrawing :=
  sourceDrawing decider (encoding.encode input)

def lineReductionCompiler : TM2ComputableInPolyTime encoding.encode FlatEncoding.finEncoding.encode
    (lineReduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (sourceEncodingCompilerTotal decider)
    (fun _ => rfl) (fun _ => rfl)

theorem lineReduction_correct (input : Input) : language input ↔ LineProblem (lineReduction decider input) := by
  rw [lineReduction,sourceDrawing_line_correct,PeriodicCNF.PolySpaceCompiler.formulaOfSymbols_encode]
  exact PeriodicCNF.PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

include decider in
theorem lineManyOne : Complexity.PolyTimeManyOneReducible encoding FlatEncoding.finEncoding language LineProblem := by
  refine ⟨lineReduction decider,?_,lineReduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (lineReductionCompiler decider)⟩

theorem lineProblem_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding LineProblem := by
  intro Input encoding language hs
  obtain ⟨decider⟩ := hs
  exact lineManyOne decider

end LeanTrominoes.Gadget.NormalizedOrientation
end
