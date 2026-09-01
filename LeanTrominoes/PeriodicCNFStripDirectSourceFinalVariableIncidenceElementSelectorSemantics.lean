/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementSelectorCompiler

/-! # Semantics of final variable-incidence element selectors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Flattening pointwise singleton blocks is ordinary mapping. -/
private theorem flatMap_singletons_eq_map {Source Target : Type*}
    (value : Source → Target) (source : List Source) :
    source.flatMap (fun item => [value item]) = source.map value := by
  induction source with
  | nil => rfl
  | cons item source induction =>
      simp only [List.flatMap_cons, List.map_cons,
        List.singleton_append, induction]

/-- Packing preserves the finite base index and structural tag. -/
@[simp] theorem variableIncidenceElementSelector_val
    (base : VariableIncidenceElementBase) (tag : Fin 32) :
    (variableIncidenceElementSelector base tag).val =
      match base with
      | .currentOccurrence => tag.val
      | .nextOccurrence => 32 + tag.val
      | .parentClause => 64 + tag.val := by
  cases base <;> rfl

/-- The finite selector block is aligned one-for-one with the corresponding
finite direction-query block. -/
@[simp] theorem groupedVariableIncidenceElementSelectorBlock_length
    (pair : GroupedVariableFanSlot) :
    (groupedVariableIncidenceElementSelectorBlock pair).length =
      (groupedVariableIncidencePrefixQueryBlock pair).length := by
  simp [groupedVariableIncidenceElementSelectorBlock,
    groupedVariableIncidencePrefixQueryBlock]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete selector stream has exactly one item per grouped variable
incidence query. -/
@[simp] theorem directSourceFinalVariableIncidenceElementSelectors_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableIncidenceElementSelectors
      decider symbols).length =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  simp [directSourceFinalVariableIncidenceElementSelectors,
    directSourceFinalGroupedVariableIncidencePrefixQueries]

@[simp] theorem directSourceFinalVariableIncidenceNextControls_length
    (selectors : List VariableIncidenceElementSelector) :
    (directSourceFinalVariableIncidenceNextControls selectors).length =
      selectors.length := by
  simp [directSourceFinalVariableIncidenceNextControls]

/-- Singleton block expansion is the ordinary pointwise next-base map. -/
theorem directSourceFinalVariableIncidenceNextControls_eq_map
    (selectors : List VariableIncidenceElementSelector) :
    directSourceFinalVariableIncidenceNextControls selectors =
      selectors.map VariableIncidenceElementSelector.usesNext := by
  exact flatMap_singletons_eq_map
    VariableIncidenceElementSelector.usesNext selectors

@[simp] theorem directSourceFinalVariableIncidenceParentControls_length
    (selectors : List VariableIncidenceElementSelector) :
    (directSourceFinalVariableIncidenceParentControls selectors).length =
      selectors.length := by
  simp [directSourceFinalVariableIncidenceParentControls]

/-- Singleton block expansion is the ordinary pointwise parent-base map. -/
theorem directSourceFinalVariableIncidenceParentControls_eq_map
    (selectors : List VariableIncidenceElementSelector) :
    directSourceFinalVariableIncidenceParentControls selectors =
      selectors.map VariableIncidenceElementSelector.usesParent := by
  exact flatMap_singletons_eq_map
    VariableIncidenceElementSelector.usesParent selectors

@[simp] theorem directSourceFinalVariableIncidenceTags_length
    (selectors : List VariableIncidenceElementSelector) :
    (directSourceFinalVariableIncidenceTags selectors).length =
      selectors.length := by
  simp [directSourceFinalVariableIncidenceTags,
    FiniteUnaryFieldMap.values]

end LeanTrominoes.PeriodicCNFStripReduction

end
