/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionGeneratedCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorData

/-! # Conditional direct retained planar direction compilation -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedPlanarDirectionCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Machine boundary for the pre-split retained planar direction stream. -/
abbrev DirectRetainedPlanarDirectionDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token
    id id (directRetainedPlanarDirectionDescriptors decider)

/-- Any polynomial-time pre-split descriptor emitter composes with the exact
two-pass fixed-eight expander. -/
noncomputable def
    directRetainedFixedEightDirectionDescriptorsComputableInPolyTime
    (sourceCompiler :
      DirectRetainedPlanarDirectionDescriptorCompiler decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
      encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token
      id id (directRetainedFixedEightDirectionDescriptors decider) := by
  exact PeriodicCNF.FormulaShapeFixedEightDirection.descriptorsComputableInPolyTimeOf
    id (directRetainedPlanarDirectionDescriptors decider) sourceCompiler

end PeriodicCNFStripReduction
end LeanTrominoes
