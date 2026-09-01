/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeBlockSemantics

/-! # Element-code interpretation of packed variable-incidence selectors -/

namespace LeanTrominoes.PeriodicCNFStripReduction

@[simp] theorem variableIncidenceElementCode_current
    (tag : Fin 32) (current next parent : Nat) :
    variableIncidenceElementCode
        (variableIncidenceElementSelector .currentOccurrence tag)
        current next parent =
      current * directSourceFinalElementCodeStride + tag.val := by
  unfold variableIncidenceElementCode variableIncidenceSelectedIdentity
    VariableIncidenceElementSelector.usesParent
    VariableIncidenceElementSelector.usesNext
    VariableIncidenceElementSelector.tag
  simp [variableIncidenceElementSelector,
    Nat.div_eq_of_lt tag.isLt, Nat.mod_eq_of_lt tag.isLt]

@[simp] theorem variableIncidenceElementCode_next
    (tag : Fin 32) (current next parent : Nat) :
    variableIncidenceElementCode
        (variableIncidenceElementSelector .nextOccurrence tag)
        current next parent =
      next * directSourceFinalElementCodeStride + tag.val := by
  unfold variableIncidenceElementCode variableIncidenceSelectedIdentity
    VariableIncidenceElementSelector.usesParent
    VariableIncidenceElementSelector.usesNext
    VariableIncidenceElementSelector.tag
  simp [variableIncidenceElementSelector,
    Nat.div_eq_of_lt tag.isLt, Nat.mod_eq_of_lt tag.isLt]

@[simp] theorem variableIncidenceElementCode_parent
    (tag : Fin 32) (current next parent : Nat) :
    variableIncidenceElementCode
        (variableIncidenceElementSelector .parentClause tag)
        current next parent =
      parent * directSourceFinalElementCodeStride + tag.val := by
  unfold variableIncidenceElementCode variableIncidenceSelectedIdentity
    VariableIncidenceElementSelector.usesParent
    VariableIncidenceElementSelector.usesNext
    VariableIncidenceElementSelector.tag
  have divEq : (64 + tag.val) / 32 = 2 := by omega
  have modEq : (64 + tag.val) % 32 = tag.val := by omega
  simp [variableIncidenceElementSelector, divEq, modEq]

end LeanTrominoes.PeriodicCNFStripReduction
