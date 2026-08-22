/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDecomposedVariableMarkerData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentAtomMarkerCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerAffineCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Polynomial-time decomposed retained variable markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedDecomposedMarkerCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The segment-terminal, source-atom, and crossing marker phases concatenate
to a polynomial-time compiler. -/
noncomputable def
    directRetainedPlanarMetadataDecomposedVariableMarkersComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token
      id id (directRetainedPlanarMetadataDecomposedVariableMarkers decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataSegmentAtomMarkers decider symbols ++
        directRetainedPlanarMetadataCrossingMarkers decider symbols)
  exact TM2ListAppend.nativeComputableInPolyTime
    (directRetainedPlanarMetadataSegmentAtomMarkersComputableInPolyTime decider)
    (directRetainedPlanarMetadataCrossingMarkersComputableInPolyTime decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
