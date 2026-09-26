/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationDenseCompiler
import LeanTrominoes.CompletionGenericDrawingPalette
import LeanTrominoes.CompletionStripHardnessCompiler
import LeanTrominoes.CompletionStripMembership

/-! # A bounded native orientation input compiles to unary strip completion -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.SafePreparation
open Turing CompletionPattern CompletionPattern.Runtime

def completion (d : PeriodicOrthogonalDrawing) : PeriodicStripTrominoPrefill :=
  StripOrientation.compile .I (drawing (FlatEncoding.finEncoding.encode d))

def rawCompletionCompiler : TM2ComputableInPolyTime id CompletionStripEncoding.finEncoding.encode
    (fun s => StripOrientation.compile .I (drawing s)) := by
  let cp := GenericDrawing.brickPeriodCompiler drawing widthCompiler
  let ch := GenericDrawing.brickCountCompiler drawing heightCompiler
  let palette := GenericDrawing.sourcePaletteCompiler drawing (fun s => denseEntries (drawing s))
    widthCompiler heightCompiler denseXCompiler denseYCompiler denseKindCompiler (fun s => denseModel (drawing s))
  exact prefillEncodingCompiler (targetHeightCompiler ch .I) (targetPeriodCompiler cp .I)
    (drawingMotifCompiler cp ch palette .I)

def completionCompiler : TM2ComputableInPolyTime FlatEncoding.finEncoding.encode
    CompletionStripEncoding.finEncoding.encode completion :=
  TM2PolyTimeInputEncodingTransport.of_prepare FlatEncoding.finEncoding.encode rawCompletionCompiler
    (fun _ => rfl) (fun _ => rfl)

def completionFieldsCompiler : TM2ComputableInPolyTime FlatEncoding.finEncoding.encode
    PartrecToTM2.trList (fun d => PeriodicStripTrominoPrefill.Raw.fields (completion d)) :=
  TM2CompositionMachine.computableInPolyTime completionCompiler
    PeriodicStripTrominoPrefill.Raw.Preparation.nativePreparation_compiler

theorem completion_correct (d : PeriodicOrthogonalDrawing) (wf : d.IsWellFormed)
    (blank : d.HasBlankVerticalBoundary) :
    PeriodicStripTrominoPrefill.problem .I (completion d) ↔ d.HasOrientation := by
  rw [completion,drawing_encoded d wf]
  exact StripOrientation.compile_correct .I d wf blank

end LeanTrominoes.Gadget.NormalizedOrientation.SafePreparation
end
