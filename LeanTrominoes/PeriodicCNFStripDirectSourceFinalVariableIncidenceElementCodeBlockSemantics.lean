/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceSelectedIdentitySemantics

/-! # Pointwise final variable-incidence element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Interpret one finite selector after supplying its three dynamic identity
bases. -/
def variableIncidenceElementCode
    (selector : VariableIncidenceElementSelector)
    (current next parent : Nat) : Nat :=
  variableIncidenceSelectedIdentity selector current next parent *
      directSourceFinalElementCodeStride +
    selector.tag

/-- Complete triple-major RGB element-code block of one grouped occurrence. -/
def groupedVariableIncidenceElementCodeBlock
    (pair : GroupedVariableFanSlot)
    (current next parent : Nat) : List Nat :=
  (groupedVariableIncidenceElementSelectorBlock pair).map fun selector =>
    variableIncidenceElementCode selector current next parent

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Scaling the selected identity and adding the compiled finite tag fuses
with the preceding four-column selection into direct element-code
interpretation. -/
  theorem directSourceFinalVariableIncidenceElementCodes_eq_zipWith4
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceElementCodes decider symbols =
      List.zipWith4 variableIncidenceElementCode
        (directSourceFinalVariableIncidenceElementSelectors decider symbols)
        (directSourceFinalVariableIncidenceCurrentKeys decider symbols)
        (directSourceFinalVariableIncidenceNextKeys decider symbols)
        (directSourceFinalVariableIncidenceParentIndices decider symbols) := by
  rw [directSourceFinalVariableIncidenceElementCodes_eq_zipWith]
  unfold directSourceFinalVariableIncidenceScaledIdentityBases
    UnaryFieldConstantScale.values
    directSourceFinalVariableIncidenceTagColumn
    directSourceFinalVariableIncidenceTags
    FiniteUnaryFieldMap.values
  rw [directSourceFinalVariableIncidenceSelectedIdentityBases_eq_zipWith4]
  exact List.zipWith_map_zipWith4_map_first
    variableIncidenceSelectedIdentity
    (fun identity => identity * directSourceFinalElementCodeStride)
    VariableIncidenceElementSelector.tag
    (fun base tag => base + tag)
    (directSourceFinalVariableIncidenceElementSelectors decider symbols)
    (directSourceFinalVariableIncidenceCurrentKeys decider symbols)
    (directSourceFinalVariableIncidenceNextKeys decider symbols)
    (directSourceFinalVariableIncidenceParentIndices decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
