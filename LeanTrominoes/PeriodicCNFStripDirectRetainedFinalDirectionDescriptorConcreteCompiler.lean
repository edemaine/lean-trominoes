/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCopiedClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceDirectionDescriptorBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceVariableMarkerCompiler

/-! # Concrete final Figure 9 direction-descriptor compilation -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDirectionConcreteCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The verified five-family copied-clause compiler and the concrete variable
marker pass compile the actual final normalized Figure 9 descriptor stream. -/
noncomputable def
    directRetainedFigureNineDirectionDescriptorsComputableInPolyTime :
    DirectRetainedFigureNineDirectionDescriptorCompiler decider :=
  directRetainedFigureNineDirectionDescriptorCompilerOfAppenders decider
    (directRetainedFigureNineCopiedClauseDescriptorAppender decider)
    (directRetainedFigureNineFiniteSourceVariableMarkerAppender decider)

/-- Consequently the complete final exact-one logical shape is polynomial-time
computable from the PSPACE-source symbol stream. -/
noncomputable def directRetainedFinalExactOneShapeConcreteComputableInPolyTime :=
  directRetainedFinalExactOneShapeComputableInPolyTimeOfDescriptors decider
    (directRetainedFigureNineDirectionDescriptorsComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
