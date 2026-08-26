/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedCopiedClauseQueryCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceDirectionDescriptorBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceVariableMarkerCompiler

/-! # Concrete final descriptor compilation from copied-clause queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFiniteSourceConcreteCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Any exact copied-clause query producer now supplies the actual final
normalized Figure 9 descriptor compiler: the clause evaluator, marker pass,
and fixed-eight expansion are all concrete. -/
noncomputable def directRetainedFigureNineDirectionDescriptorCompilerOfQueries
    (queries : DirectRetainedFigureNineCopiedClauseQueryCompiler decider) :
    DirectRetainedFigureNineDirectionDescriptorCompiler decider :=
  directRetainedFigureNineDirectionDescriptorCompilerOfAppenders decider
    (directRetainedFigureNineCopiedClauseDescriptorAppenderOfQueries
      decider queries)
    (directRetainedFigureNineFiniteSourceVariableMarkerAppender decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
