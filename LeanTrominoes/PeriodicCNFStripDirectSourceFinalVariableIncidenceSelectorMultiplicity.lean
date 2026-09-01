/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeBlockSemantics

/-! # Finite multiplicity audit for variable-incidence selectors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- The part of a variable fan that can affect one local incidence block.
Endpoint directions are deliberately omitted. -/
structure VariableIncidenceLocalControl where
  countPred : Fin 3
  kind : VariableSiteSlot → VariableConnectorKind
  polarity : VariableSiteSlot → Bool
  genericSlot : FiniteRoleSlotUnaryDecoder.Slot
  deriving DecidableEq, Fintype

namespace VariableIncidenceLocalControl

def fan (control : VariableIncidenceLocalControl) : VariableRibbonFanData where
  countPred := control.countPred
  kind := control.kind
  polarity := control.polarity
  direction := fun _ => .north

def pair (control : VariableIncidenceLocalControl) : GroupedVariableFanSlot :=
  (control.fan, control.genericSlot)

def ofPair (pair : GroupedVariableFanSlot) :
    VariableIncidenceLocalControl where
  countPred := pair.1.countPred
  kind := pair.1.kind
  polarity := pair.1.polarity
  genericSlot := pair.2

def slot (control : VariableIncidenceLocalControl) : VariableSiteSlot :=
  groupedVariableFanSiteSlot control.genericSlot

def IsActive (control : VariableIncidenceLocalControl) : Prop :=
  control.slot.index < control.countPred.val + 1

instance (control : VariableIncidenceLocalControl) :
    Decidable control.IsActive := by
  unfold IsActive
  infer_instance

def current (tag : Fin 32) : VariableIncidenceElementSelector :=
  variableIncidenceElementSelector .currentOccurrence tag

def next (tag : Fin 32) : VariableIncidenceElementSelector :=
  variableIncidenceElementSelector .nextOccurrence tag

def parent (tag : Fin 32) : VariableIncidenceElementSelector :=
  variableIncidenceElementSelector .parentClause tag

/-- The two red cycle-link references.  A one-occurrence cycle refers twice
to its sole current key; longer active cycles use current and successor once
each. -/
def expectedCycleSelectors
    (control : VariableIncidenceLocalControl) :
    List VariableIncidenceElementSelector :=
  if control.countPred = 0 then [current 0, current 0]
  else [current 0, next 0]

/-- Every non-cycle variable-local element occurs twice in its finite
connector gadget. -/
def expectedPrivateSelectors
    (control : VariableIncidenceLocalControl) :
    List VariableIncidenceElementSelector :=
  match control.kind control.slot with
  | .fixedRed =>
      [current 1, current 1, current 2, current 2,
        current 4, current 4, current 5, current 5,
        current 6, current 6, current 8, current 8,
        current 9, current 9, current 10, current 10]
  | .fixedGreen | .fixedBlue =>
      [current 4, current 4, current 8, current 8]

/-- Each occurrence contributes exactly one red, green, and blue reference
to the terminal group selected by its connector kind. -/
def expectedParentSelectors
    (control : VariableIncidenceLocalControl) :
    List VariableIncidenceElementSelector :=
  let kind := control.kind control.slot
  [parent (variableIncidenceClauseTerminalTag kind .red),
    parent (variableIncidenceClauseTerminalTag kind .green),
    parent (variableIncidenceClauseTerminalTag kind .blue)]

def expectedSelectors (control : VariableIncidenceLocalControl) :
    List VariableIncidenceElementSelector :=
  control.expectedCycleSelectors ++ control.expectedPrivateSelectors ++
    control.expectedParentSelectors

/-- Reconstructing the direction-free local control preserves the complete
finite selector block definitionally. -/
theorem selectorBlock_ofPair (pair : GroupedVariableFanSlot) :
    groupedVariableIncidenceElementSelectorBlock pair =
      groupedVariableIncidenceElementSelectorBlock
        (VariableIncidenceLocalControl.ofPair pair).pair := by
  rcases pair with
    ⟨⟨countPred, kind, polarity, direction⟩, genericSlot⟩
  rfl

/-- Exhaustive audit of the 5,184 direction-free local controls.  Only 54
selected-slot behaviors are semantically distinct; the finite check also
covers harmless values in inactive function positions and generic fallback
slots. -/
theorem selectorBlock_perm_expected :
    ∀ control : VariableIncidenceLocalControl,
      control.IsActive →
      (groupedVariableIncidenceElementSelectorBlock control.pair).Perm
        control.expectedSelectors := by
  native_decide

end VariableIncidenceLocalControl

/-- Every active grouped occurrence has the audited selector multiplicities:
two cycle references, two references to each private variable element, and
one RGB parent-terminal reference. -/
theorem groupedVariableIncidenceElementSelectorBlock_perm_expected
    (pair : GroupedVariableFanSlot)
    (active : (VariableIncidenceLocalControl.ofPair pair).IsActive) :
    (groupedVariableIncidenceElementSelectorBlock pair).Perm
      (VariableIncidenceLocalControl.ofPair pair).expectedSelectors := by
  rw [VariableIncidenceLocalControl.selectorBlock_ofPair pair]
  exact VariableIncidenceLocalControl.selectorBlock_perm_expected
    (VariableIncidenceLocalControl.ofPair pair) active

/-- Mapping the audited finite selector permutation through dynamic identity
interpretation gives the corresponding exact element-code multiplicities. -/
theorem groupedVariableIncidenceElementCodeBlock_perm_expected
    (pair : GroupedVariableFanSlot)
    (current next parent : Nat)
    (active : (VariableIncidenceLocalControl.ofPair pair).IsActive) :
    (groupedVariableIncidenceElementCodeBlock
      pair current next parent).Perm
      ((VariableIncidenceLocalControl.ofPair pair).expectedSelectors.map
        fun selector =>
        variableIncidenceElementCode selector current next parent) := by
  exact (groupedVariableIncidenceElementSelectorBlock_perm_expected
    pair active).map fun selector =>
      variableIncidenceElementCode selector current next parent

end LeanTrominoes.PeriodicCNFStripReduction

end
