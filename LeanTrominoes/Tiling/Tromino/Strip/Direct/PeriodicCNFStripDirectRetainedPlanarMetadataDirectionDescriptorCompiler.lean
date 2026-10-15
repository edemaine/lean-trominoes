/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorSemantics
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Direct retained planar metadata descriptor compiler boundary -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Exact machine boundary after eliminating the retained positioned formula
and route-normalization structures. -/
abbrev DirectRetainedPlanarMetadataDirectionDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token
    id id (directRetainedPlanarMetadataDirectionDescriptors decider)

/-- Any polynomial-time emitter for the explicit finite metadata stream
implements the canonical pre-split compiler expected by fixed-eight. -/
noncomputable def directRetainedPlanarDirectionDescriptorCompilerOfMetadata
    (metadataCompiler :
      DirectRetainedPlanarMetadataDirectionDescriptorCompiler decider) :
    DirectRetainedPlanarDirectionDescriptorCompiler decider := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    metadataCompiler fun symbols => by
      rw [directRetainedPlanarDirectionDescriptors_eq_metadata]

/-- Consequently a metadata emitter also supplies the exact fixed-eight
descriptor stream used downstream. -/
noncomputable def
    directRetainedFixedEightDirectionDescriptorsComputableInPolyTimeOfMetadata
    (metadataCompiler :
      DirectRetainedPlanarMetadataDirectionDescriptorCompiler decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
      encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token
      id id (directRetainedFixedEightDirectionDescriptors decider) :=
  directRetainedFixedEightDirectionDescriptorsComputableInPolyTime decider
    (directRetainedPlanarDirectionDescriptorCompilerOfMetadata
      decider metadataCompiler)

end PeriodicCNFStripReduction
end LeanTrominoes
