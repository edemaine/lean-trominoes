/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerAffineCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorData
import LeanTrominoes.ThirteenMarkerPairBlockCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling the fixed crossover descriptor postprocess -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossoverCompiledStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directRetainedPlanarMetadataCompiledCrossoverClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCompiledCrossoverClauseDescriptorCompiler
      decider := by
  let markers :=
    directRetainedPlanarMetadataCrossingMarkersComputableInPolyTime decider
  let descriptors :=
    ThirteenMarkerPairBlocks.computableInPolyTime
      (Marker := FormulaShapeDirectionOrdering.Token)
      FormulaShapeCrossoverDirection.descriptorPair
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      ThirteenMarkerPairBlocks.output
        FormulaShapeCrossoverDirection.descriptorPair
        (directRetainedPlanarMetadataCrossingMarkers decider symbols))
  exact TM2CompositionMachine.computableInPolyTime markers descriptors

end LeanTrominoes.PeriodicCNFStripReduction

end
