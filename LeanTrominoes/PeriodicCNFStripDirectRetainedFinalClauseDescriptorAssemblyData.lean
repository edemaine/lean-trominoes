/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyData

/-! # Evaluated five-family final clause-descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDescriptorAssemblyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Evaluate the compiled five-family query assembly to its exact finite
direction-aware descriptor stream. -/
def directRetainedFinalClauseDescriptorAssembly
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  retainedFinalCopiedClauseDescriptors
    (directRetainedFinalClauseQueryAssembly decider symbols)

abbrev DirectRetainedFinalClauseDescriptorAssemblyCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedFinalClauseDescriptorAssembly decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
