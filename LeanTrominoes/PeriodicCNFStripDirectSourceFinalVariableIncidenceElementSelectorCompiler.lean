/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler
import LeanTrominoes.PlanarThreeDMVariableSiteDrawing
import LeanTrominoes.TM2CompositionMachine

/-! # Finite element selectors for final variable incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open Gadget PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- The three input-dependent identity columns from which a variable
incidence can draw its referenced element. -/
inductive VariableIncidenceElementBase
  | currentOccurrence
  | nextOccurrence
  | parentClause
  deriving DecidableEq

/-- A finite description of one referenced element.  The base selects one
input-dependent identity; the tag selects one of its 32 reserved structural
positions. -/
abbrev VariableIncidenceElementSelector := Fin 96

/-- Pack one of the three dynamic bases and one structural tag into the finite
selector alphabet. -/
def variableIncidenceElementSelector :
    VariableIncidenceElementBase → Fin 32 →
      VariableIncidenceElementSelector
  | .currentOccurrence, tag => ⟨tag.val, by omega⟩
  | .nextOccurrence, tag => ⟨32 + tag.val, by omega⟩
  | .parentClause, tag => ⟨64 + tag.val, by omega⟩

/-- Structural tag of the clause terminal attached to one connector kind and
color. -/
def variableIncidenceClauseTerminalTag
    (kind : VariableConnectorKind) (color : WireColor) : Fin 32 :=
  let terminalOffset :=
    match kind with
    | .fixedRed => 1
    | .fixedBlue => 2
    | .fixedGreen => 3
  let colorBase :=
    match color with
    | .red => 16
    | .green => 20
    | .blue => 24
  ⟨colorBase + terminalOffset, by
    cases kind <;> cases color <;> decide⟩

/-- Interpret one assembled finite variable-site reference as a choice of
current occurrence, cyclic successor occurrence, or parent clause, together
with the canonical structural tag already used by the element column. -/
def groupedVariableIncidenceElementSelector
    (pair : GroupedVariableFanSlot)
    (triple : VariableSiteTriple) (color : WireColor) :
    VariableIncidenceElementSelector :=
  let slot := groupedVariableFanSiteSlot pair.2
  match variableSiteReferenceBase pair.1.count pair.1.polarity triple color with
  | .cycleLink referencedSlot =>
      if referencedSlot = slot then
        variableIncidenceElementSelector .currentOccurrence
          ⟨0, by decide⟩
      else
        variableIncidenceElementSelector .nextOccurrence
          ⟨0, by decide⟩
  | .ordinary _ _ .cycleShared =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨4, by decide⟩
  | .ordinary _ _ .auxiliaryShared =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨8, by decide⟩
  | .ordinary _ _ _ =>
      variableIncidenceElementSelector .parentClause
        (variableIncidenceClauseTerminalTag (pair.1.kind slot) color)
  | .fixedRed _ (.red .middleRung) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨1, by decide⟩
  | .fixedRed _ (.red .topAuxiliary) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨2, by decide⟩
  | .fixedRed _ (.green .leftRung) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨4, by decide⟩
  | .fixedRed _ (.green .topRightLink) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨5, by decide⟩
  | .fixedRed _ (.green .bottomRightLink) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨6, by decide⟩
  | .fixedRed _ (.blue .topLeftLink) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨8, by decide⟩
  | .fixedRed _ (.blue .bottomLeftLink) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨9, by decide⟩
  | .fixedRed _ (.blue .rightRung) =>
      variableIncidenceElementSelector .currentOccurrence
        ⟨10, by decide⟩
  | .fixedRed _ _ =>
      variableIncidenceElementSelector .parentClause
        (variableIncidenceClauseTerminalTag (pair.1.kind slot) color)

/-- One finite element selector per local triple and color, in the exact same
triple-major RGB order as the variable-incidence direction queries. -/
def groupedVariableIncidenceElementSelectorBlock
    (pair : GroupedVariableFanSlot) :
    List VariableIncidenceElementSelector :=
  (groupedVariableIncidenceTriples pair).flatMap fun triple =>
    [groupedVariableIncidenceElementSelector pair triple .red,
      groupedVariableIncidenceElementSelector pair triple .green,
      groupedVariableIncidenceElementSelector pair triple .blue]

/-- Flattened finite selector stream for every grouped variable incidence. -/
def directSourceFinalVariableIncidenceElementSelectors
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List VariableIncidenceElementSelector :=
  (directSourceFinalGroupedVariableFanSlots decider symbols).flatMap
    groupedVariableIncidenceElementSelectorBlock

/-- Whether one selector reads the cyclic-successor occurrence column. -/
def VariableIncidenceElementSelector.usesNext
    (selector : VariableIncidenceElementSelector) : Bool :=
  selector.val / 32 == 1

/-- Whether one selector reads the parent-clause column. -/
def VariableIncidenceElementSelector.usesParent
    (selector : VariableIncidenceElementSelector) : Bool :=
  selector.val / 32 == 2

/-- Recover the structural tag packed in a finite selector. -/
def VariableIncidenceElementSelector.tag
    (selector : VariableIncidenceElementSelector) : Nat :=
  selector.val % 32

def directSourceFinalVariableIncidenceNextControls
    (selectors : List VariableIncidenceElementSelector) : List Bool :=
  selectors.flatMap fun selector =>
    [VariableIncidenceElementSelector.usesNext selector]

def directSourceFinalVariableIncidenceParentControls
    (selectors : List VariableIncidenceElementSelector) : List Bool :=
  selectors.flatMap fun selector =>
    [VariableIncidenceElementSelector.usesParent selector]

def directSourceFinalVariableIncidenceTags
    (selectors : List VariableIncidenceElementSelector) : List Nat :=
  FiniteUnaryFieldMap.values VariableIncidenceElementSelector.tag selectors

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalVariableIncidenceSelectorStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The complete finite selector stream compiles in polynomial time. -/
noncomputable def
    directSourceFinalVariableIncidenceElementSelectorsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalVariableIncidenceElementSelectors decider) := by
  unfold directSourceFinalVariableIncidenceElementSelectors
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      groupedVariableIncidenceElementSelectorBlock)

noncomputable def
    directSourceFinalVariableIncidenceNextControlsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun symbols => directSourceFinalVariableIncidenceNextControls
        (directSourceFinalVariableIncidenceElementSelectors decider symbols)) := by
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalVariableIncidenceElementSelectorsComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      fun selector : VariableIncidenceElementSelector =>
      [VariableIncidenceElementSelector.usesNext selector])

noncomputable def
    directSourceFinalVariableIncidenceParentControlsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun symbols => directSourceFinalVariableIncidenceParentControls
        (directSourceFinalVariableIncidenceElementSelectors decider symbols)) := by
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalVariableIncidenceElementSelectorsComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      fun selector : VariableIncidenceElementSelector =>
      [VariableIncidenceElementSelector.usesParent selector])

noncomputable def
    directSourceFinalVariableIncidenceTagsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => directSourceFinalVariableIncidenceTags
        (directSourceFinalVariableIncidenceElementSelectors decider symbols)) := by
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalVariableIncidenceElementSelectorsComputableInPolyTime
      decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      VariableIncidenceElementSelector.tag)

end LeanTrominoes.PeriodicCNFStripReduction

end
