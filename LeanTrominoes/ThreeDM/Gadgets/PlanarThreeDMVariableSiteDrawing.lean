/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Core.LocalIncidenceDrawingCheck
import LeanTrominoes.ThreeDM.Gadgets.PlanarThreeDMConnectorDrawings
import LeanTrominoes.ThreeDM.Gadgets.PlanarThreeDMVariableConnectorBoundary

/-!
# Certified drawings of complete variable sites

This file assembles one, two, or three occurrence modules into a complete
variable-cycle drawing.  Every module is placed above the line containing
its two standardized red continuation ports.  Consecutive continuations are
joined below that line; the closing link uses one lower private lane.

The element type used by the finite geometric checker explicitly identifies
the two continuations incident to each shared cycle link.  Thus the
certificate checks the actual finite bipartite gadget, not just the
individual route shapes.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

open Gadget

/-- The three possible occurrence positions at a variable site. -/
inductive VariableSiteSlot
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

namespace VariableSiteSlot

/-- Zero-based horizontal position. -/
def index : VariableSiteSlot → Nat
  | .first => 0
  | .second => 1
  | .third => 2

/-- Stable enumeration of the three site positions. -/
def all : List VariableSiteSlot :=
  [.first, .second, .third]

end VariableSiteSlot

/-- A candidate triple from an occurrence module at a variable site. -/
inductive VariableSiteTriple
  | ordinary (slot : VariableSiteSlot)
      (variant : VariableOccurrenceVariant)
      (triple : VariableOccurrenceTriple)
  | fixedRed (slot : VariableSiteSlot)
      (triple : FixedRedConnectorTriple)
  deriving DecidableEq, Repr

/-- Stable enumeration of all candidate triples before selecting a connector
kind in each active slot. -/
def allVariableSiteTriples : List VariableSiteTriple :=
  VariableSiteSlot.all.flatMap fun slot =>
    ([VariableOccurrenceVariant.fixedGreen,
        VariableOccurrenceVariant.fixedBlue].flatMap fun variant =>
      [VariableOccurrenceTriple.first,
        VariableOccurrenceTriple.second,
        VariableOccurrenceTriple.auxiliary].map fun triple =>
          .ordinary slot variant triple) ++
      [FixedRedConnectorTriple.topLeft,
        FixedRedConnectorTriple.topMiddle,
        FixedRedConnectorTriple.topRight,
        FixedRedConnectorTriple.bottomLeft,
        FixedRedConnectorTriple.bottomMiddle,
        FixedRedConnectorTriple.bottomRight,
        FixedRedConnectorTriple.auxiliary].map fun triple =>
          .fixedRed slot triple

instance : Fintype VariableSiteTriple :=
  Fintype.ofList allVariableSiteTriples (by
    intro triple
    cases triple with
    | ordinary slot variant localTriple =>
        cases slot <;> cases variant <;> cases localTriple <;>
          simp [allVariableSiteTriples, VariableSiteSlot.all]
    | fixedRed slot localTriple =>
        cases slot <;> cases localTriple <;>
          simp [allVariableSiteTriples, VariableSiteSlot.all])

namespace VariableSiteTriple

/-- Occurrence-module slot containing a variable-site triple. -/
def slot : VariableSiteTriple → VariableSiteSlot
  | .ordinary slot _ _ => slot
  | .fixedRed slot _ => slot

/-- Whether a candidate triple belongs to the connector selected for its
slot. -/
def MatchesKind
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind) :
    VariableSiteTriple → Prop
  | .ordinary slot .fixedGreen _ =>
      slot.index < count ∧ kind slot = .fixedGreen
  | .ordinary slot .fixedBlue _ =>
      slot.index < count ∧ kind slot = .fixedBlue
  | .fixedRed slot _ =>
      slot.index < count ∧ kind slot = .fixedRed

instance (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (triple : VariableSiteTriple) :
    Decidable (triple.MatchesKind count kind) := by
  cases triple with
  | ordinary slot variant localTriple =>
      cases variant <;> unfold MatchesKind <;> infer_instance
  | fixedRed slot localTriple =>
      unfold MatchesKind
      infer_instance

end VariableSiteTriple

/-- Exactly the triples belonging to the chosen connector in every slot. -/
abbrev ActiveVariableSiteTriple
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind) :=
  {triple : VariableSiteTriple // triple.MatchesKind count kind}

/-- Candidate elements of a variable site.  Continuation elements are
represented only by their assembled cycle-link name. -/
inductive VariableSiteElement
  | cycleLink (slot : VariableSiteSlot)
  | ordinary (slot : VariableSiteSlot)
      (variant : VariableOccurrenceVariant)
      (element : VariableOccurrenceElement)
  | fixedRed (slot : VariableSiteSlot)
      (element : FixedRedConnectorElement)
  deriving DecidableEq, Repr

/-- Stable enumeration of all candidate variable-site elements. -/
def allVariableSiteElements : List VariableSiteElement :=
  VariableSiteSlot.all.flatMap fun slot =>
    [.cycleLink slot] ++
    ([VariableOccurrenceVariant.fixedGreen,
        VariableOccurrenceVariant.fixedBlue].flatMap fun variant =>
      [VariableOccurrenceElement.leftContinuation,
        VariableOccurrenceElement.rightContinuation,
        VariableOccurrenceElement.cycleShared,
        VariableOccurrenceElement.auxiliaryShared,
        VariableOccurrenceElement.connectorRed,
        VariableOccurrenceElement.connectorGreen,
        VariableOccurrenceElement.connectorBlue].map fun element =>
          .ordinary slot variant element) ++
    [FixedRedConnectorElement.red .leftTopPort,
      FixedRedConnectorElement.red .leftBottomPort,
      FixedRedConnectorElement.red .middleRung,
      FixedRedConnectorElement.red .topAuxiliary,
      FixedRedConnectorElement.red .connectorPort,
      FixedRedConnectorElement.green .leftRung,
      FixedRedConnectorElement.green .topRightLink,
      FixedRedConnectorElement.green .bottomRightLink,
      FixedRedConnectorElement.green .connectorPort,
      FixedRedConnectorElement.blue .topLeftLink,
      FixedRedConnectorElement.blue .bottomLeftLink,
      FixedRedConnectorElement.blue .rightRung,
      FixedRedConnectorElement.blue .connectorPort].map fun element =>
        .fixedRed slot element

instance : Fintype VariableSiteElement :=
  Fintype.ofList allVariableSiteElements (by
    intro element
    cases element with
    | cycleLink slot =>
        cases slot <;>
          simp [allVariableSiteElements, VariableSiteSlot.all]
    | ordinary slot variant localElement =>
        cases slot <;> cases variant <;> cases localElement <;>
          simp [allVariableSiteElements, VariableSiteSlot.all]
    | fixedRed slot localElement =>
        cases slot <;> cases localElement with
        | red red =>
            cases red <;>
              simp [allVariableSiteElements, VariableSiteSlot.all]
        | green green =>
            cases green <;>
              simp [allVariableSiteElements, VariableSiteSlot.all]
        | blue blue =>
            cases blue <;>
              simp [allVariableSiteElements, VariableSiteSlot.all])

namespace VariableSiteElement

/-- Whether an element belongs to the selected connectors and active prefix.
Local continuation names are omitted because their assembled names are the
cycle links. -/
def MatchesKind
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind) :
    VariableSiteElement → Prop
  | .cycleLink slot =>
      slot.index < count
  | .ordinary slot .fixedGreen element =>
      slot.index < count ∧
        kind slot = .fixedGreen ∧
        element ≠ .leftContinuation ∧
        element ≠ .rightContinuation
  | .ordinary slot .fixedBlue element =>
      slot.index < count ∧
        kind slot = .fixedBlue ∧
        element ≠ .leftContinuation ∧
        element ≠ .rightContinuation
  | .fixedRed slot element =>
      slot.index < count ∧
        kind slot = .fixedRed ∧
        element ≠ .red .leftTopPort ∧
        element ≠ .red .leftBottomPort

instance (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (element : VariableSiteElement) :
    Decidable (element.MatchesKind count kind) := by
  cases element with
  | cycleLink slot =>
      unfold MatchesKind
      infer_instance
  | ordinary slot variant localElement =>
      cases variant <;> unfold MatchesKind <;> infer_instance
  | fixedRed slot localElement =>
      unfold MatchesKind
      infer_instance

end VariableSiteElement

/-- Exactly the elements present in the selected active modules, with shared
continuations identified as cycle links. -/
abbrev ActiveVariableSiteElement
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind) :=
  {element : VariableSiteElement // element.MatchesKind count kind}

/-- Cyclic successor among the active prefix of site slots. -/
def nextVariableSiteSlot
    (count : Nat) : VariableSiteSlot → VariableSiteSlot
  | .first => if 1 < count then .second else .first
  | .second => if 2 < count then .third else .first
  | .third => .first

/-- The successor of an active slot is active. -/
theorem nextVariableSiteSlot_active
    (count : Nat) (slot : VariableSiteSlot)
    (active : slot.index < count) :
    (nextVariableSiteSlot count slot).index < count := by
  cases slot with
  | first =>
      simp only [nextVariableSiteSlot]
      split
      · assumption
      · simpa [VariableSiteSlot.index] using active
  | second =>
      simp only [nextVariableSiteSlot]
      split
      · assumption
      · simp only [VariableSiteSlot.index]
        have : 1 < count := by
          simpa [VariableSiteSlot.index] using active
        omega
  | third =>
      simp only [nextVariableSiteSlot, VariableSiteSlot.index]
      have : 2 < count := by
        simpa [VariableSiteSlot.index] using active
      omega

/-- Horizontal origin of one occurrence module. -/
def variableModuleOrigin (slot : VariableSiteSlot) : Cell :=
  (32 * slot.index, 0)

/-- Translate a local point into its occurrence module. -/
def placeVariableModulePoint
    (slot : VariableSiteSlot) (point : Cell) : Cell :=
  (point.1 + (variableModuleOrigin slot).1,
    point.2 + (variableModuleOrigin slot).2)

/-- Position of the cycle-link element indexed by the current slot. -/
def variableCycleLinkPosition (slot : VariableSiteSlot) : Cell :=
  ((variableModuleOrigin slot).1 + 4, -8)

/-- Position of the link indexed by the cyclic successor of this slot. -/
def nextVariableCycleLinkPosition
    (count : Nat) (slot : VariableSiteSlot) : Cell :=
  if slot.index + 1 < count then
    (32 * (slot.index + 1) + 4, -8)
  else
    (4, -8)

/-- Identify an ordinary module's local element with its assembled
variable-site element. -/
def ordinaryVariableSiteElement
    (count : Nat) (polarity : Bool)
    (slot : VariableSiteSlot)
    (variant : VariableOccurrenceVariant) :
    VariableOccurrenceElement → VariableSiteElement
  | .leftContinuation =>
      .cycleLink
        (if polarity then slot else nextVariableSiteSlot count slot)
  | .rightContinuation =>
      .cycleLink
        (if polarity then nextVariableSiteSlot count slot else slot)
  | element =>
      .ordinary slot variant element

/-- Identify a fixed-red module's local element with its assembled
variable-site element. -/
def fixedRedVariableSiteElement
    (count : Nat) (polarity : Bool)
    (slot : VariableSiteSlot) :
    FixedRedConnectorElement → VariableSiteElement
  | .red .leftTopPort =>
      .cycleLink
        (if polarity then nextVariableSiteSlot count slot else slot)
  | .red .leftBottomPort =>
      .cycleLink
        (if polarity then slot else nextVariableSiteSlot count slot)
  | element =>
      .fixedRed slot element

/-- Assembled element referenced by one colored variable-site incidence. -/
def variableSiteReferenceBase
    (count : Nat)
    (polarity : VariableSiteSlot → Bool)
    (triple : VariableSiteTriple)
    (color : WireColor) : VariableSiteElement :=
  match triple with
  | .ordinary slot variant localTriple =>
      ordinaryVariableSiteElement count (polarity slot) slot variant
        (VariableOccurrence.reference variant localTriple color)
  | .fixedRed slot localTriple =>
      fixedRedVariableSiteElement count (polarity slot) slot
        (FixedRedConnector.reference localTriple color)

@[simp]
theorem ordinary_slotContinuation_reference
    (count : Nat) (polarity : Bool)
    (slot : VariableSiteSlot)
    (variant : VariableOccurrenceVariant) :
    variableSiteReferenceBase count (fun _ => polarity)
        (.ordinary slot variant
          (VariableOccurrence.slotContinuationTriple polarity)) .red =
      .cycleLink slot := by
  cases polarity <;> cases variant <;>
    simp [variableSiteReferenceBase, ordinaryVariableSiteElement,
      VariableOccurrence.slotContinuationTriple,
      VariableOccurrence.reference,
      VariableOccurrenceTriple.references]

@[simp]
theorem ordinary_nextContinuation_reference
    (count : Nat) (polarity : Bool)
    (slot : VariableSiteSlot)
    (variant : VariableOccurrenceVariant) :
    variableSiteReferenceBase count (fun _ => polarity)
        (.ordinary slot variant
          (VariableOccurrence.nextContinuationTriple polarity)) .red =
      .cycleLink (nextVariableSiteSlot count slot) := by
  cases polarity <;> cases variant <;>
    simp [variableSiteReferenceBase, ordinaryVariableSiteElement,
      VariableOccurrence.nextContinuationTriple,
      VariableOccurrence.reference,
      VariableOccurrenceTriple.references]

@[simp]
theorem fixedRed_slotContinuation_reference
    (count : Nat) (polarity : Bool)
    (slot : VariableSiteSlot) :
    variableSiteReferenceBase count (fun _ => polarity)
        (.fixedRed slot
          (FixedRedConnector.slotContinuationTriple polarity)) .red =
      .cycleLink slot := by
  cases polarity <;>
    simp [variableSiteReferenceBase, fixedRedVariableSiteElement,
      FixedRedConnector.slotContinuationTriple,
      FixedRedConnector.reference,
      FixedRedConnectorTriple.references]

@[simp]
theorem fixedRed_nextContinuation_reference
    (count : Nat) (polarity : Bool)
    (slot : VariableSiteSlot) :
    variableSiteReferenceBase count (fun _ => polarity)
        (.fixedRed slot
          (FixedRedConnector.nextContinuationTriple polarity)) .red =
      .cycleLink (nextVariableSiteSlot count slot) := by
  cases polarity <;>
    simp [variableSiteReferenceBase, fixedRedVariableSiteElement,
      FixedRedConnector.nextContinuationTriple,
      FixedRedConnector.reference,
      FixedRedConnectorTriple.references]

/-- Every reference of an active triple is an active assembled element. -/
theorem variableSiteReferenceBase_matches
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (polarity : VariableSiteSlot → Bool)
    (triple : VariableSiteTriple)
    (active : triple.MatchesKind count kind)
    (color : WireColor) :
    (variableSiteReferenceBase count polarity triple color).MatchesKind
      count kind := by
  cases triple with
  | ordinary slot variant localTriple =>
      cases variant <;>
        simp only [VariableSiteTriple.MatchesKind] at active
      all_goals
        rcases active with ⟨slotActive, kindEq⟩
        have nextActive :=
          nextVariableSiteSlot_active count slot slotActive
        cases localTriple <;> cases color <;>
          cases polarityEq : polarity slot <;>
          simp [variableSiteReferenceBase, ordinaryVariableSiteElement,
            VariableOccurrence.reference,
            VariableOccurrenceTriple.references,
            VariableSiteElement.MatchesKind,
            polarityEq, slotActive, nextActive, kindEq]
  | fixedRed slot localTriple =>
      simp only [VariableSiteTriple.MatchesKind] at active
      rcases active with ⟨slotActive, kindEq⟩
      have nextActive :=
        nextVariableSiteSlot_active count slot slotActive
      cases localTriple <;> cases color <;>
        cases polarityEq : polarity slot <;>
        simp [variableSiteReferenceBase, fixedRedVariableSiteElement,
          FixedRedConnector.reference,
          FixedRedConnectorTriple.references,
          VariableSiteElement.MatchesKind,
          polarityEq, slotActive, nextActive, kindEq]

/-- Typed assembled reference of one active colored incidence. -/
def variableSiteReference
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (polarity : VariableSiteSlot → Bool)
    (triple : ActiveVariableSiteTriple count kind)
    (color : WireColor) :
    ActiveVariableSiteElement count kind :=
  ⟨variableSiteReferenceBase count polarity triple.1 color,
    variableSiteReferenceBase_matches
      count kind polarity triple.1 triple.2 color⟩

/-- Position of a triple in the selected, polarity-oriented module. -/
def variableSiteTriplePosition
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (polarity : VariableSiteSlot → Bool)
    (triple : ActiveVariableSiteTriple count kind) : Cell :=
  match triple.1 with
  | .ordinary slot variant localTriple =>
      placeVariableModulePoint slot
        ((VariableOccurrence.orientedBoundaryDrawing
          variant (polarity slot)).triplePosition localTriple)
  | .fixedRed slot localTriple =>
      placeVariableModulePoint slot
        ((FixedRedConnector.boundaryDrawing
          (polarity slot)).triplePosition localTriple)

/-- Position of an actual assembled element in the variable-site drawing. -/
def variableSiteElementPosition
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (polarity : VariableSiteSlot → Bool)
    (element : ActiveVariableSiteElement count kind) : Cell :=
  match element.1 with
  | .cycleLink slot =>
      variableCycleLinkPosition slot
  | .ordinary slot variant localElement =>
      placeVariableModulePoint slot
        ((VariableOccurrence.orientedBoundaryDrawing
          variant (polarity slot)).elementPosition localElement)
  | .fixedRed slot localElement =>
      placeVariableModulePoint slot
        ((FixedRedConnector.boundaryDrawing
          (polarity slot)).elementPosition localElement)

/-- The route inside one selected occurrence module, translated to its
variable-site position. -/
def variableSiteLocalRoute
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (polarity : VariableSiteSlot → Bool)
    (triple : ActiveVariableSiteTriple count kind)
    (color : WireColor) : List Cell :=
  match triple.1 with
  | .ordinary slot variant localTriple =>
      ((VariableOccurrence.orientedBoundaryDrawing
        variant (polarity slot)).route localTriple color).map
          (placeVariableModulePoint slot)
  | .fixedRed slot localTriple =>
      ((FixedRedConnector.boundaryDrawing
        (polarity slot)).route localTriple color).map
          (placeVariableModulePoint slot)

/-- Extend a current-slot continuation vertically to its cycle-link
element. -/
def currentCycleExtension (slot : VariableSiteSlot) : List Cell :=
  [variableCycleLinkPosition slot]

/-- Extend a successor continuation to the next link.  The closing
continuation runs on the private line `y = -16`. -/
def nextCycleExtension
    (count : Nat) (slot : VariableSiteSlot) : List Cell :=
  let startX := (variableModuleOrigin slot).1 + 12
  let target := nextVariableCycleLinkPosition count slot
  if slot.index + 1 < count then
    [(startX, -8), target]
  else
    [(startX, -16), (target.1, -16), target]

/-- Route of one colored incidence in the complete variable site. -/
def variableSiteRoute
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (polarity : VariableSiteSlot → Bool)
    (triple : ActiveVariableSiteTriple count kind)
    (color : WireColor) : List Cell :=
  let localRoute :=
    variableSiteLocalRoute count kind polarity triple color
  match triple.1 with
  | .ordinary slot _ localTriple =>
      if color = .red ∧
          localTriple =
            VariableOccurrence.slotContinuationTriple (polarity slot) then
        localRoute ++ currentCycleExtension slot
      else if color = .red ∧
          localTriple =
            VariableOccurrence.nextContinuationTriple (polarity slot) then
        localRoute ++ nextCycleExtension count slot
      else
        localRoute
  | .fixedRed slot localTriple =>
      if color = .red ∧
          localTriple =
            FixedRedConnector.slotContinuationTriple (polarity slot) then
        localRoute ++ currentCycleExtension slot
      else if color = .red ∧
          localTriple =
            FixedRedConnector.nextContinuationTriple (polarity slot) then
        localRoute ++ nextCycleExtension count slot
      else
        localRoute

/-- Complete finite drawing of a variable site with shared cycle-link and
internal elements. -/
def variableSiteDrawing
    (count : Nat)
    (kind : VariableSiteSlot → VariableConnectorKind)
    (polarity : VariableSiteSlot → Bool) :
    LocalIncidenceDrawing
      (ActiveVariableSiteTriple count kind)
      (ActiveVariableSiteElement count kind) where
  triplePosition := variableSiteTriplePosition count kind polarity
  elementPosition := variableSiteElementPosition count kind polarity
  reference := variableSiteReference count kind polarity
  route := variableSiteRoute count kind polarity

/-- One-occurrence specialization of the variable-site drawing. -/
def oneVariableSiteDrawing
    (kind : VariableConnectorKind) (polarity : Bool) :=
  variableSiteDrawing
    1
    (fun _ => kind)
    (fun _ => polarity)

set_option maxHeartbeats 2000000 in
/-- Every connector kind and polarity gives a valid one-occurrence site. -/
theorem all_oneVariableSiteDrawing_isValid :
    ∀ kind polarity,
      (oneVariableSiteDrawing kind polarity).IsValid := by
  intro kind polarity
  cases kind <;> cases polarity <;>
    (apply LocalIncidenceDrawing.isValid_of_check; decide +kernel)

/-- Two-occurrence specialization of the variable-site drawing. -/
def twoVariableSiteDrawing
    (firstKind secondKind : VariableConnectorKind)
    (firstPolarity secondPolarity : Bool) :=
  variableSiteDrawing
    2
    (fun slot =>
      if slot = .first then firstKind else secondKind)
    (fun slot =>
      if slot = .first then firstPolarity else secondPolarity)

set_option maxHeartbeats 2000000 in
/-- Every connector-kind and polarity pattern gives a valid
two-occurrence site. -/
theorem all_twoVariableSiteDrawing_isValid :
    ∀ firstKind secondKind firstPolarity secondPolarity,
      (twoVariableSiteDrawing
        firstKind secondKind firstPolarity secondPolarity).IsValid := by
  intro firstKind secondKind firstPolarity secondPolarity
  cases firstKind <;> cases secondKind <;> cases firstPolarity <;> cases secondPolarity <;>
    (apply LocalIncidenceDrawing.isValid_of_check; decide +kernel)

/-- Three-occurrence specialization of the variable-site drawing. -/
def threeVariableSiteDrawing
    (firstKind secondKind thirdKind : VariableConnectorKind)
    (firstPolarity secondPolarity thirdPolarity : Bool) :=
  variableSiteDrawing
    3
    (fun slot =>
      if slot = .first then firstKind
      else if slot = .second then secondKind
      else thirdKind)
    (fun slot =>
      if slot = .first then firstPolarity
      else if slot = .second then secondPolarity
      else thirdPolarity)

private theorem threeVariableSiteDrawing_case0 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case1 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case2 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case3 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case4 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case5 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case6 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case7 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case8 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case9 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case10 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case11 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case12 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case13 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case14 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case15 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case16 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case17 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case18 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case19 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case20 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case21 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case22 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case23 :
    (threeVariableSiteDrawing .fixedRed .fixedRed .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case24 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case25 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case26 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case27 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case28 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case29 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case30 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case31 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case32 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case33 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case34 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case35 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case36 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case37 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case38 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case39 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case40 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case41 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case42 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case43 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case44 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case45 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case46 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case47 :
    (threeVariableSiteDrawing .fixedRed .fixedGreen .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case48 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case49 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case50 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case51 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case52 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case53 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case54 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case55 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case56 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case57 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case58 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case59 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case60 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case61 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case62 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case63 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case64 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case65 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case66 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case67 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case68 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case69 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case70 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case71 :
    (threeVariableSiteDrawing .fixedRed .fixedBlue .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case72 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case73 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case74 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case75 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case76 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case77 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case78 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case79 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case80 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case81 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case82 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case83 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case84 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case85 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case86 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case87 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case88 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case89 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case90 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case91 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case92 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case93 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case94 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case95 :
    (threeVariableSiteDrawing .fixedGreen .fixedRed .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case96 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case97 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case98 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case99 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case100 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case101 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case102 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case103 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case104 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case105 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case106 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case107 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case108 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case109 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case110 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case111 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case112 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case113 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case114 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case115 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case116 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case117 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case118 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case119 :
    (threeVariableSiteDrawing .fixedGreen .fixedGreen .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case120 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case121 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case122 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case123 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case124 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case125 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case126 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case127 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case128 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case129 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case130 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case131 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case132 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case133 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case134 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case135 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case136 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case137 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case138 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case139 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case140 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case141 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case142 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case143 :
    (threeVariableSiteDrawing .fixedGreen .fixedBlue .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case144 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case145 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case146 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case147 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case148 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case149 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case150 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case151 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case152 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case153 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case154 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case155 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case156 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case157 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case158 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case159 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case160 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case161 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case162 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case163 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case164 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case165 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case166 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case167 :
    (threeVariableSiteDrawing .fixedBlue .fixedRed .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case168 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case169 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case170 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case171 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case172 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case173 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case174 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case175 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case176 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case177 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case178 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case179 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case180 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case181 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case182 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case183 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case184 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case185 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case186 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case187 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case188 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case189 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case190 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case191 :
    (threeVariableSiteDrawing .fixedBlue .fixedGreen .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case192 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case193 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case194 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case195 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case196 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case197 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case198 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case199 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedRed true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case200 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case201 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case202 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case203 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case204 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case205 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case206 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case207 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedGreen true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case208 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue false false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case209 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue false false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case210 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue false true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case211 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue false true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case212 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue true false false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case213 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue true false true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case214 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue true true false).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

private theorem threeVariableSiteDrawing_case215 :
    (threeVariableSiteDrawing .fixedBlue .fixedBlue .fixedBlue true true true).IsValid := by
  apply LocalIncidenceDrawing.isValid_of_check
  decide +kernel

set_option maxHeartbeats 2000000 in
/-- Every connector-kind and polarity pattern gives a valid
three-occurrence site. -/
theorem all_threeVariableSiteDrawing_isValid :
    ∀ firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity,
      (threeVariableSiteDrawing
        firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity).IsValid := by
  intro firstKind secondKind thirdKind firstPolarity secondPolarity thirdPolarity
  match firstKind, secondKind, thirdKind, firstPolarity, secondPolarity, thirdPolarity with
  | .fixedRed, .fixedRed, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case0
  | .fixedRed, .fixedRed, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case1
  | .fixedRed, .fixedRed, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case2
  | .fixedRed, .fixedRed, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case3
  | .fixedRed, .fixedRed, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case4
  | .fixedRed, .fixedRed, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case5
  | .fixedRed, .fixedRed, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case6
  | .fixedRed, .fixedRed, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case7
  | .fixedRed, .fixedRed, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case8
  | .fixedRed, .fixedRed, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case9
  | .fixedRed, .fixedRed, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case10
  | .fixedRed, .fixedRed, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case11
  | .fixedRed, .fixedRed, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case12
  | .fixedRed, .fixedRed, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case13
  | .fixedRed, .fixedRed, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case14
  | .fixedRed, .fixedRed, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case15
  | .fixedRed, .fixedRed, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case16
  | .fixedRed, .fixedRed, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case17
  | .fixedRed, .fixedRed, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case18
  | .fixedRed, .fixedRed, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case19
  | .fixedRed, .fixedRed, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case20
  | .fixedRed, .fixedRed, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case21
  | .fixedRed, .fixedRed, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case22
  | .fixedRed, .fixedRed, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case23
  | .fixedRed, .fixedGreen, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case24
  | .fixedRed, .fixedGreen, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case25
  | .fixedRed, .fixedGreen, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case26
  | .fixedRed, .fixedGreen, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case27
  | .fixedRed, .fixedGreen, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case28
  | .fixedRed, .fixedGreen, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case29
  | .fixedRed, .fixedGreen, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case30
  | .fixedRed, .fixedGreen, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case31
  | .fixedRed, .fixedGreen, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case32
  | .fixedRed, .fixedGreen, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case33
  | .fixedRed, .fixedGreen, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case34
  | .fixedRed, .fixedGreen, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case35
  | .fixedRed, .fixedGreen, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case36
  | .fixedRed, .fixedGreen, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case37
  | .fixedRed, .fixedGreen, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case38
  | .fixedRed, .fixedGreen, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case39
  | .fixedRed, .fixedGreen, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case40
  | .fixedRed, .fixedGreen, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case41
  | .fixedRed, .fixedGreen, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case42
  | .fixedRed, .fixedGreen, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case43
  | .fixedRed, .fixedGreen, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case44
  | .fixedRed, .fixedGreen, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case45
  | .fixedRed, .fixedGreen, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case46
  | .fixedRed, .fixedGreen, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case47
  | .fixedRed, .fixedBlue, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case48
  | .fixedRed, .fixedBlue, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case49
  | .fixedRed, .fixedBlue, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case50
  | .fixedRed, .fixedBlue, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case51
  | .fixedRed, .fixedBlue, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case52
  | .fixedRed, .fixedBlue, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case53
  | .fixedRed, .fixedBlue, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case54
  | .fixedRed, .fixedBlue, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case55
  | .fixedRed, .fixedBlue, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case56
  | .fixedRed, .fixedBlue, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case57
  | .fixedRed, .fixedBlue, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case58
  | .fixedRed, .fixedBlue, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case59
  | .fixedRed, .fixedBlue, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case60
  | .fixedRed, .fixedBlue, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case61
  | .fixedRed, .fixedBlue, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case62
  | .fixedRed, .fixedBlue, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case63
  | .fixedRed, .fixedBlue, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case64
  | .fixedRed, .fixedBlue, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case65
  | .fixedRed, .fixedBlue, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case66
  | .fixedRed, .fixedBlue, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case67
  | .fixedRed, .fixedBlue, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case68
  | .fixedRed, .fixedBlue, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case69
  | .fixedRed, .fixedBlue, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case70
  | .fixedRed, .fixedBlue, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case71
  | .fixedGreen, .fixedRed, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case72
  | .fixedGreen, .fixedRed, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case73
  | .fixedGreen, .fixedRed, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case74
  | .fixedGreen, .fixedRed, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case75
  | .fixedGreen, .fixedRed, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case76
  | .fixedGreen, .fixedRed, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case77
  | .fixedGreen, .fixedRed, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case78
  | .fixedGreen, .fixedRed, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case79
  | .fixedGreen, .fixedRed, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case80
  | .fixedGreen, .fixedRed, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case81
  | .fixedGreen, .fixedRed, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case82
  | .fixedGreen, .fixedRed, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case83
  | .fixedGreen, .fixedRed, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case84
  | .fixedGreen, .fixedRed, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case85
  | .fixedGreen, .fixedRed, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case86
  | .fixedGreen, .fixedRed, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case87
  | .fixedGreen, .fixedRed, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case88
  | .fixedGreen, .fixedRed, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case89
  | .fixedGreen, .fixedRed, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case90
  | .fixedGreen, .fixedRed, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case91
  | .fixedGreen, .fixedRed, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case92
  | .fixedGreen, .fixedRed, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case93
  | .fixedGreen, .fixedRed, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case94
  | .fixedGreen, .fixedRed, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case95
  | .fixedGreen, .fixedGreen, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case96
  | .fixedGreen, .fixedGreen, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case97
  | .fixedGreen, .fixedGreen, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case98
  | .fixedGreen, .fixedGreen, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case99
  | .fixedGreen, .fixedGreen, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case100
  | .fixedGreen, .fixedGreen, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case101
  | .fixedGreen, .fixedGreen, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case102
  | .fixedGreen, .fixedGreen, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case103
  | .fixedGreen, .fixedGreen, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case104
  | .fixedGreen, .fixedGreen, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case105
  | .fixedGreen, .fixedGreen, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case106
  | .fixedGreen, .fixedGreen, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case107
  | .fixedGreen, .fixedGreen, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case108
  | .fixedGreen, .fixedGreen, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case109
  | .fixedGreen, .fixedGreen, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case110
  | .fixedGreen, .fixedGreen, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case111
  | .fixedGreen, .fixedGreen, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case112
  | .fixedGreen, .fixedGreen, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case113
  | .fixedGreen, .fixedGreen, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case114
  | .fixedGreen, .fixedGreen, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case115
  | .fixedGreen, .fixedGreen, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case116
  | .fixedGreen, .fixedGreen, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case117
  | .fixedGreen, .fixedGreen, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case118
  | .fixedGreen, .fixedGreen, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case119
  | .fixedGreen, .fixedBlue, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case120
  | .fixedGreen, .fixedBlue, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case121
  | .fixedGreen, .fixedBlue, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case122
  | .fixedGreen, .fixedBlue, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case123
  | .fixedGreen, .fixedBlue, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case124
  | .fixedGreen, .fixedBlue, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case125
  | .fixedGreen, .fixedBlue, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case126
  | .fixedGreen, .fixedBlue, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case127
  | .fixedGreen, .fixedBlue, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case128
  | .fixedGreen, .fixedBlue, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case129
  | .fixedGreen, .fixedBlue, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case130
  | .fixedGreen, .fixedBlue, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case131
  | .fixedGreen, .fixedBlue, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case132
  | .fixedGreen, .fixedBlue, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case133
  | .fixedGreen, .fixedBlue, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case134
  | .fixedGreen, .fixedBlue, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case135
  | .fixedGreen, .fixedBlue, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case136
  | .fixedGreen, .fixedBlue, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case137
  | .fixedGreen, .fixedBlue, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case138
  | .fixedGreen, .fixedBlue, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case139
  | .fixedGreen, .fixedBlue, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case140
  | .fixedGreen, .fixedBlue, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case141
  | .fixedGreen, .fixedBlue, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case142
  | .fixedGreen, .fixedBlue, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case143
  | .fixedBlue, .fixedRed, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case144
  | .fixedBlue, .fixedRed, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case145
  | .fixedBlue, .fixedRed, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case146
  | .fixedBlue, .fixedRed, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case147
  | .fixedBlue, .fixedRed, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case148
  | .fixedBlue, .fixedRed, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case149
  | .fixedBlue, .fixedRed, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case150
  | .fixedBlue, .fixedRed, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case151
  | .fixedBlue, .fixedRed, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case152
  | .fixedBlue, .fixedRed, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case153
  | .fixedBlue, .fixedRed, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case154
  | .fixedBlue, .fixedRed, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case155
  | .fixedBlue, .fixedRed, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case156
  | .fixedBlue, .fixedRed, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case157
  | .fixedBlue, .fixedRed, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case158
  | .fixedBlue, .fixedRed, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case159
  | .fixedBlue, .fixedRed, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case160
  | .fixedBlue, .fixedRed, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case161
  | .fixedBlue, .fixedRed, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case162
  | .fixedBlue, .fixedRed, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case163
  | .fixedBlue, .fixedRed, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case164
  | .fixedBlue, .fixedRed, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case165
  | .fixedBlue, .fixedRed, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case166
  | .fixedBlue, .fixedRed, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case167
  | .fixedBlue, .fixedGreen, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case168
  | .fixedBlue, .fixedGreen, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case169
  | .fixedBlue, .fixedGreen, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case170
  | .fixedBlue, .fixedGreen, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case171
  | .fixedBlue, .fixedGreen, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case172
  | .fixedBlue, .fixedGreen, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case173
  | .fixedBlue, .fixedGreen, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case174
  | .fixedBlue, .fixedGreen, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case175
  | .fixedBlue, .fixedGreen, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case176
  | .fixedBlue, .fixedGreen, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case177
  | .fixedBlue, .fixedGreen, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case178
  | .fixedBlue, .fixedGreen, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case179
  | .fixedBlue, .fixedGreen, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case180
  | .fixedBlue, .fixedGreen, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case181
  | .fixedBlue, .fixedGreen, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case182
  | .fixedBlue, .fixedGreen, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case183
  | .fixedBlue, .fixedGreen, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case184
  | .fixedBlue, .fixedGreen, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case185
  | .fixedBlue, .fixedGreen, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case186
  | .fixedBlue, .fixedGreen, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case187
  | .fixedBlue, .fixedGreen, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case188
  | .fixedBlue, .fixedGreen, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case189
  | .fixedBlue, .fixedGreen, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case190
  | .fixedBlue, .fixedGreen, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case191
  | .fixedBlue, .fixedBlue, .fixedRed, false, false, false => exact threeVariableSiteDrawing_case192
  | .fixedBlue, .fixedBlue, .fixedRed, false, false, true => exact threeVariableSiteDrawing_case193
  | .fixedBlue, .fixedBlue, .fixedRed, false, true, false => exact threeVariableSiteDrawing_case194
  | .fixedBlue, .fixedBlue, .fixedRed, false, true, true => exact threeVariableSiteDrawing_case195
  | .fixedBlue, .fixedBlue, .fixedRed, true, false, false => exact threeVariableSiteDrawing_case196
  | .fixedBlue, .fixedBlue, .fixedRed, true, false, true => exact threeVariableSiteDrawing_case197
  | .fixedBlue, .fixedBlue, .fixedRed, true, true, false => exact threeVariableSiteDrawing_case198
  | .fixedBlue, .fixedBlue, .fixedRed, true, true, true => exact threeVariableSiteDrawing_case199
  | .fixedBlue, .fixedBlue, .fixedGreen, false, false, false => exact threeVariableSiteDrawing_case200
  | .fixedBlue, .fixedBlue, .fixedGreen, false, false, true => exact threeVariableSiteDrawing_case201
  | .fixedBlue, .fixedBlue, .fixedGreen, false, true, false => exact threeVariableSiteDrawing_case202
  | .fixedBlue, .fixedBlue, .fixedGreen, false, true, true => exact threeVariableSiteDrawing_case203
  | .fixedBlue, .fixedBlue, .fixedGreen, true, false, false => exact threeVariableSiteDrawing_case204
  | .fixedBlue, .fixedBlue, .fixedGreen, true, false, true => exact threeVariableSiteDrawing_case205
  | .fixedBlue, .fixedBlue, .fixedGreen, true, true, false => exact threeVariableSiteDrawing_case206
  | .fixedBlue, .fixedBlue, .fixedGreen, true, true, true => exact threeVariableSiteDrawing_case207
  | .fixedBlue, .fixedBlue, .fixedBlue, false, false, false => exact threeVariableSiteDrawing_case208
  | .fixedBlue, .fixedBlue, .fixedBlue, false, false, true => exact threeVariableSiteDrawing_case209
  | .fixedBlue, .fixedBlue, .fixedBlue, false, true, false => exact threeVariableSiteDrawing_case210
  | .fixedBlue, .fixedBlue, .fixedBlue, false, true, true => exact threeVariableSiteDrawing_case211
  | .fixedBlue, .fixedBlue, .fixedBlue, true, false, false => exact threeVariableSiteDrawing_case212
  | .fixedBlue, .fixedBlue, .fixedBlue, true, false, true => exact threeVariableSiteDrawing_case213
  | .fixedBlue, .fixedBlue, .fixedBlue, true, true, false => exact threeVariableSiteDrawing_case214
  | .fixedBlue, .fixedBlue, .fixedBlue, true, true, true => exact threeVariableSiteDrawing_case215

/-- The explicit one-, two-, and three-site successor coordinates agree with
the named cyclic successor slots. -/
theorem variableCycleLink_successor_positions :
    (∀ slot,
      nextVariableCycleLinkPosition 1 slot =
        variableCycleLinkPosition (nextVariableSiteSlot 1 slot)) ∧
    (∀ slot,
      nextVariableCycleLinkPosition 2 slot =
        variableCycleLinkPosition (nextVariableSiteSlot 2 slot)) ∧
    ∀ slot,
      nextVariableCycleLinkPosition 3 slot =
        variableCycleLinkPosition (nextVariableSiteSlot 3 slot) := by
  decide +kernel

end PlanarThreeDM
end LeanTrominoes
