/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteProgramDrawingColumns
import LeanTrominoes.Tiling.Completion.Finite.FiniteDrawingPrefillCompiler
import LeanTrominoes.Tiling.Completion.FiniteCompletionEncodingCompiler

/-! # Unconditional original-source finite completion reduction machine -/
noncomputable section
namespace LeanTrominoes.FiniteProgramCompletion
open _root_.Computability Turing PeriodicCNF CompletionPattern CompletionPattern.Runtime
variable {Source : Type} {encoding : FiniteEncoding Source} {language : Source → Prop}
variable (source : ProgramSource encoding language)
variable (zero : ∀ symbols,FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

private def prefillCompiler [Inhabited encoding.Γ] (t : Tromino) :
    TM2ComputableInPolyTime id (Tromino.FiniteCoordinateColumns.completionEncoding t).encode
      (prefillOfSymbols source zero t) :=
  Tromino.FiniteCoordinateColumns.completionEncodingComputableInPolyTime (prefillOfSymbols source zero t)
    (FiniteDrawing.prefillSymmetryCompiler (drawing source zero) (FiniteProgramSparseTrominoRegion.assignments source)
      (widthCompiler source zero) (heightCompiler source zero)
      (xCompiler source zero) (yCompiler source zero) (kindCompiler source zero) (sparseModel source zero) t)
    (FiniteDrawing.prefillXCompiler (drawing source zero) (FiniteProgramSparseTrominoRegion.assignments source)
      (widthCompiler source zero) (heightCompiler source zero)
      (xCompiler source zero) (yCompiler source zero) (kindCompiler source zero) (sparseModel source zero) t)
    (FiniteDrawing.prefillYCompiler (drawing source zero) (FiniteProgramSparseTrominoRegion.assignments source)
      (widthCompiler source zero) (heightCompiler source zero)
      (xCompiler source zero) (yCompiler source zero) (kindCompiler source zero) (sparseModel source zero) t) t

/-- The reduction charges the full canonical box in the target encoding and
measures time against the original source word. -/
def prefillComputableInPolyTime (t : Tromino) :
    TM2ComputableInPolyTime encoding.encode (Tromino.FiniteCoordinateColumns.completionEncoding t).encode
      (prefill source zero t) := by
  classical
  have symbolsCompiler : TM2ComputableInPolyTime id (Tromino.FiniteCoordinateColumns.completionEncoding t).encode
      (prefillOfSymbols source zero t) := by
    by_cases nonempty : Nonempty encoding.Γ
    · letI : Inhabited encoding.Γ := ⟨Classical.choice nonempty⟩
      exact prefillCompiler source zero t
    · letI : Inhabited (Tromino.FiniteCoordinateColumns.completionEncoding t).Γ :=
        ⟨Tromino.FiniteCoordinateColumns.Token.bit false⟩
      letI : IsEmpty encoding.Γ := ⟨fun symbol => nonempty ⟨symbol⟩⟩
      exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
        (Tromino.FiniteCoordinateColumns.completionEncoding t).encode (prefillOfSymbols source zero t)
  exact TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode symbolsCompiler
    (fun _ => rfl) (fun _ => rfl)
end LeanTrominoes.FiniteProgramCompletion
