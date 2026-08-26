/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseDescriptorAssemblyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyCompiler
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling the evaluated five-family final descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDescriptorAssemblyCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compose the five-family query compiler with its fixed finite evaluator. -/
noncomputable def
    directRetainedFinalClauseDescriptorAssemblyComputableInPolyTime :
    DirectRetainedFinalClauseDescriptorAssemblyCompiler decider := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token id id
    (fun symbols => retainedFinalCopiedClauseDescriptors
      (directRetainedFinalClauseQueryAssembly decider symbols))
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFinalClauseQueryAssemblyComputableInPolyTime decider)
    retainedFinalCopiedClauseDescriptorsComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
