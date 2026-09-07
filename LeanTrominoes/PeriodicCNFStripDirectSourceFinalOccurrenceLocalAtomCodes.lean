/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSourceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceWitness
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceLocalAtomCodes

/-! # Actual parent-local code fields of direct source occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance occurrenceLocalCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance occurrenceLocalCodeVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every compiled local atom code uses the parent and finite header from
that same source occurrence; no separate alignment assumption is needed. -/
theorem directSourceFinalOccurrences_map_localAtomCode
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).map sourceOccurrenceLocalAtomCode =
      directSourceFinalLocalAtomCodes decider symbols := by
  unfold directSourceFinalOccurrences
    PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail.occurrences
  rw [sourceOccurrences_map_localAtomCode,
    directSourceFinalClauseDescriptors_eq_source_prefix, localAtomCodes_append_variables]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
