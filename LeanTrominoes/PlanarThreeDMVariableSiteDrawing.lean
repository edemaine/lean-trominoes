import LeanTrominoes.PlanarThreeDMConnectorDrawings
import LeanTrominoes.PlanarThreeDMVariableConnectorBoundary

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

/-- Every connector kind and polarity gives a valid one-occurrence site. -/
theorem all_oneVariableSiteDrawing_isValid :
    ∀ kind polarity,
      (oneVariableSiteDrawing kind polarity).IsValid := by
  native_decide

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

/-- Every connector-kind and polarity pattern gives a valid
two-occurrence site. -/
theorem all_twoVariableSiteDrawing_isValid :
    ∀ firstKind secondKind firstPolarity secondPolarity,
      (twoVariableSiteDrawing
        firstKind secondKind firstPolarity secondPolarity).IsValid := by
  native_decide

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

/-- Every connector-kind and polarity pattern gives a valid
three-occurrence site. -/
theorem all_threeVariableSiteDrawing_isValid :
    ∀ firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity,
      (threeVariableSiteDrawing
        firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity).IsValid := by
  native_decide

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
  native_decide

end PlanarThreeDM
end LeanTrominoes
