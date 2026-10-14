/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDecomposedVariableMarkerCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDecomposedVariableMarkerCorrect
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Polynomial-time retained metadata variable markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The exact canonical retained metadata variable-marker suffix is
polynomial-time computable. -/
noncomputable def
    directRetainedPlanarMetadataVariableMarkersComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token
      id id (directRetainedPlanarMetadataVariableMarkers decider) :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataDecomposedVariableMarkers decider)
    (directRetainedPlanarMetadataVariableMarkers decider)
    (directRetainedPlanarMetadataDecomposedVariableMarkers_eq decider)
    (directRetainedPlanarMetadataDecomposedVariableMarkersComputableInPolyTime
      decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
