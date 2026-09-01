/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFourSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeSemantics

/-! # Pointwise semantics of selected variable-incidence identities -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Interpret the dynamic identity component of one finite incidence
selector. -/
def variableIncidenceSelectedIdentity
    (selector : VariableIncidenceElementSelector)
    (current next parent : Nat) : Nat :=
  if selector.usesParent then parent
  else if selector.usesNext then next
  else current

@[simp] theorem variableIncidenceSelectedIdentity_default :
    variableIncidenceSelectedIdentity default 0 0 0 = 0 := by
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The two Boolean-choice stages are exactly one four-column pointwise
selection from selector, current key, successor key, and parent index. -/
theorem directSourceFinalVariableIncidenceSelectedIdentityBases_eq_zipWith4
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceSelectedIdentityBases decider symbols =
      List.zipWith4 variableIncidenceSelectedIdentity
        (directSourceFinalVariableIncidenceElementSelectors decider symbols)
        (directSourceFinalVariableIncidenceCurrentKeys decider symbols)
        (directSourceFinalVariableIncidenceNextKeys decider symbols)
        (directSourceFinalVariableIncidenceParentIndices decider symbols) := by
  let selectors :=
    directSourceFinalVariableIncidenceElementSelectors decider symbols
  let currents :=
    directSourceFinalVariableIncidenceCurrentKeys decider symbols
  let nexts := directSourceFinalVariableIncidenceNextKeys decider symbols
  let parents :=
    directSourceFinalVariableIncidenceParentIndices decider symbols
  have selectorsCurrents : selectors.length = currents.length := by
    simpa only [selectors, currents] using
      (directSourceFinalVariableIncidenceCurrentKeys_length
        decider symbols).symm
  have selectorsNexts : selectors.length = nexts.length := by
    simpa only [selectors, nexts] using
      (directSourceFinalVariableIncidenceNextKeys_length
        decider symbols).symm
  have selectorsParents : selectors.length = parents.length := by
    simpa only [selectors, parents] using
      (directSourceFinalVariableIncidenceParentIndices_length
        decider symbols).symm
  have compiledLength :
      (directSourceFinalVariableIncidenceSelectedIdentityBases
        decider symbols).length = selectors.length := by
    simpa only [selectors] using
      directSourceFinalVariableIncidenceSelectedIdentityBases_length
        decider symbols
  calc
    directSourceFinalVariableIncidenceSelectedIdentityBases decider symbols =
        (List.range
          (directSourceFinalVariableIncidenceSelectedIdentityBases
            decider symbols).length).map fun index =>
            (directSourceFinalVariableIncidenceSelectedIdentityBases
              decider symbols).getD index 0 :=
      (List.map_range_getD
        (directSourceFinalVariableIncidenceSelectedIdentityBases
          decider symbols) 0).symm
    _ = (List.range selectors.length).map fun index =>
          (directSourceFinalVariableIncidenceSelectedIdentityBases
            decider symbols).getD index 0 := by rw [compiledLength]
    _ = (List.range selectors.length).map fun index =>
          variableIncidenceSelectedIdentity
            (selectors.getD index default)
            (currents.getD index 0)
            (nexts.getD index 0)
            (parents.getD index 0) := by
      apply List.map_congr_left
      intro index indexMember
      rw [directSourceFinalVariableIncidenceSelectedIdentityBases_getD
        decider symbols index (by
          simpa only [selectors] using List.mem_range.mp indexMember)]
      rfl
    _ = List.zipWith4 variableIncidenceSelectedIdentity
        selectors currents nexts parents := by
      symm
      exact List.zipWith4_eq_map_range_getD
        variableIncidenceSelectedIdentity default 0 0 0
        selectors currents nexts parents selectorsCurrents
        selectorsNexts selectorsParents

end LeanTrominoes.PeriodicCNFStripReduction

end
