/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedDirectionDescriptorSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedFormulaShapeCompiler

/-! # Conditional direct retained shape compilation from finite descriptors -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedDirectionDescriptorCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The only remaining formula-shape obligation: emit one finite clause
profile/direction descriptor per retained source clause and the exact finite
variable-marker suffix. -/
abbrev DirectRetainedFigureNineDirectionDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedFigureNineDirectionDescriptors decider)

/-- A descriptor emitter composes with the fixed finite clockwise lookup to
compile the exact retained Figure 9 source shape. -/
noncomputable def directRetainedFigureNineSourceShapeComputableInPolyTimeOfDescriptors
    (descriptorCompiler :
      DirectRetainedFigureNineDirectionDescriptorCompiler decider) :
    DirectRetainedFigureNineSourceShapeCompiler decider := by
  let complete :=
    FormulaShapeDirectionOrdering.shapeComputableInPolyTimeOf
      (Source := List encoding.Γ) (InputSymbol := encoding.Γ)
      id
      (directRetainedFigureNineDirectionDescriptors decider)
      descriptorCompiler
  simpa only [id_eq, directRetainedFigureNineDirectionShape_eq] using complete

/-- The same finite descriptor obligation suffices for the complete final
exact-one logical shape. -/
noncomputable def directRetainedFinalExactOneShapeComputableInPolyTimeOfDescriptors
    (descriptorCompiler :
      DirectRetainedFigureNineDirectionDescriptorCompiler decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List FormulaShape.Token)
      encoding.Γ FormulaShape.Token id id
      (directRetainedFinalExactOneShape decider) :=
  directRetainedFinalExactOneShapeComputableInPolyTime decider
    (directRetainedFigureNineSourceShapeComputableInPolyTimeOfDescriptors
      decider descriptorCompiler)

end PeriodicCNFStripReduction
end LeanTrominoes
