/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBaseBendScanCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling direct untranslated retained-bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile direct-source descriptor pairs and retain one normalized copy of
each bend block. -/
noncomputable def
    directRetainedPlanarMetadataBaseBendClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataBaseBendClauseDescriptorCompiler decider := by
  let fields :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let bends :=
    PeriodicOrthocrossing.RouteDescriptorPairAffine.affineBaseBendDescriptorStreamComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime fields bends
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      PeriodicOrthocrossing.RouteDescriptorPairAffine.affineBaseBendDescriptorStream
        (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
