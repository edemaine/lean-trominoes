/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeDMGadgetSemantics
import LeanTrominoes.PeriodicOneInThreeToThreeDMTyped

/-!
# Typed periodic assembly of the planar exact-one to 3DM reduction

This file assembles the verified Dyer--Frieze gadgets over a periodic
exact-one formula, while retaining meaningful finite element and triple
types.  Natural-number encoding and the geometric drawing are deliberately
deferred.

Every syntactic occurrence occupies one of the source variable's first three
slots.  Its connector kind is determined by its literal position in the
clause: top/fixed-red, left/fixed-blue, or right/fixed-green.  Red continuation
elements close the used occurrence slots into a variable cycle.  The three
RGB connector ports are identified with the matching colored terminal of the
clause core, using the reversed literal offset to refer from the variable
translate back to the clause translate.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

abbrev OccurrenceSlot :=
  PeriodicOneInThreeToThreeDM.OccurrenceSlot

abbrev TaggedOccurrence (Variable : Type*) :=
  PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable

/-- Stable list of the three available occurrence slots. -/
def allOccurrenceSlots : List OccurrenceSlot :=
  PeriodicOneInThreeToThreeDM.OccurrenceSlot.all

/-- Stable list of the ordinary three-triple module. -/
def allOrdinaryTriples : List VariableOccurrenceTriple :=
  [.first, .second, .auxiliary]

/-- Stable list of the seven triples in the fixed-red detour. -/
def allFixedRedTriples : List FixedRedConnectorTriple :=
  [.topLeft, .topMiddle, .topRight,
    .bottomLeft, .bottomMiddle, .bottomRight, .auxiliary]

/-- Stable list of the nine clause-core triples. -/
def allClauseSets : List X3CClauseSet :=
  [.topLeftOuter, .topLeftInner, .topRightInner, .topRightOuter,
    .leftMiddle, .rightMiddle, .bottomLeft, .bottomRight, .bottom]

/-- Stable list of the three clause terminals. -/
def allTerminalGroups : List X3CClauseTerminalGroup :=
  [.top, .left, .right]

/-- All syntactic occurrences of one protovariable. -/
def occurrencesOf {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    List (TaggedOccurrence Variable) :=
  PeriodicOneInThreeToThreeDM.occurrencesOf source atom

/-- The source occurrence assigned to one of three slots. -/
def occurrenceAt {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : Option (TaggedOccurrence Variable) :=
  PeriodicOneInThreeToThreeDM.occurrenceAt source atom slot

/-- Prototypical source variables that actually occur. -/
def occurringVariables {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Variable :=
  PeriodicOneInThreeToThreeDM.occurringVariables source

/-- The used prefix of the three occurrence slots. -/
def usedSlots {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    List OccurrenceSlot :=
  allOccurrenceSlots.filter fun slot =>
    (occurrenceAt source atom slot).isSome

/-- Cyclic successor among the actually used occurrence slots.  The fallback
is observed only outside the listed construction. -/
def nextUsedSlot {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : OccurrenceSlot :=
  let slots := usedSlots source atom
  if slots.isEmpty then
    slot
  else
    slots.getD ((slots.idxOf slot + 1) % slots.length) slot

/-- Match literal positions zero, one, and two with the top, left, and right
clause terminals. -/
def terminalGroupOfLiteralIndex : Nat → X3CClauseTerminalGroup
  | 0 => .top
  | 1 => .left
  | _ => .right

/-- Connector kind required by one literal position. -/
def connectorKindOfLiteralIndex
    (literalIndex : Nat) : VariableConnectorKind :=
  variableConnectorKindForTerminal
    (terminalGroupOfLiteralIndex literalIndex)

/-- Total clause index of one used occurrence slot. -/
def occurrenceClauseIndex {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : Nat :=
  match occurrenceAt source atom slot with
  | none => 0
  | some tagged => tagged.2.1

/-- Total literal index of one used occurrence slot. -/
def occurrenceLiteralIndex {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : Nat :=
  match occurrenceAt source atom slot with
  | none => 0
  | some tagged => tagged.2.2

/-- Polarity of one used occurrence slot. -/
def occurrencePolarity {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : Bool :=
  match occurrenceAt source atom slot with
  | none => false
  | some tagged => tagged.1.value

/-- Negated source-literal offset, pointing from its variable translate back
to its clause translate. -/
def occurrenceReverseOffset {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : Cell :=
  match occurrenceAt source atom slot with
  | none => (0, 0)
  | some tagged =>
      PeriodicOneInThreeToThreeDM.reverseOffset tagged.1.offset

/-- Connector kind occupying one used occurrence slot. -/
def occurrenceConnectorKind {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : VariableConnectorKind :=
  connectorKindOfLiteralIndex
    (occurrenceLiteralIndex source atom slot)

/-!
The variable-cycle links give a canonical orientation to each connector
boundary: the first continuation meets the link indexed by the occurrence,
and the second continuation meets the link indexed by the next used
occurrence.  A negative literal swaps the physical continuation ports,
exactly as in `VariableConnectorBoundary.RealizableFor`.
-/

def firstCycleLinkSlot {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : OccurrenceSlot :=
  if occurrencePolarity source atom slot then
    slot
  else
    nextUsedSlot source atom slot

def secondCycleLinkSlot {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : OccurrenceSlot :=
  if occurrencePolarity source atom slot then
    nextUsedSlot source atom slot
  else
    slot

/-- The two internal elements of an ordinary occurrence module. -/
inductive OrdinaryInternal
  | cycleShared
  | auxiliaryShared
  deriving DecidableEq, Repr, Fintype

/-- Internal red elements of the fixed-red detour. -/
inductive FixedRedInternalRed
  | middleRung
  | topAuxiliary
  deriving DecidableEq, Repr, Fintype

/-- Internal green elements of the fixed-red detour. -/
inductive FixedRedInternalGreen
  | leftRung
  | topRightLink
  | bottomRightLink
  deriving DecidableEq, Repr, Fintype

/-- Internal blue elements of the fixed-red detour. -/
inductive FixedRedInternalBlue
  | topLeftLink
  | bottomLeftLink
  | rightRung
  deriving DecidableEq, Repr, Fintype

/-- Red elements in the assembled planar reduction. -/
inductive RedElement (Variable : Type*)
  | cycleLink (atom : Variable) (slot : OccurrenceSlot)
  | fixedRedInternal (atom : Variable) (slot : OccurrenceSlot)
      (element : FixedRedInternalRed)
  | clauseInternal (clauseIndex : Nat)
  | clauseTerminal (clauseIndex : Nat)
      (group : X3CClauseTerminalGroup)
  deriving DecidableEq, Repr

/-- Green elements in the assembled planar reduction. -/
inductive GreenElement (Variable : Type*)
  | ordinaryInternal (atom : Variable) (slot : OccurrenceSlot)
      (element : OrdinaryInternal)
  | fixedRedInternal (atom : Variable) (slot : OccurrenceSlot)
      (element : FixedRedInternalGreen)
  | clauseInternal (clauseIndex : Nat)
  | clauseTerminal (clauseIndex : Nat)
      (group : X3CClauseTerminalGroup)
  deriving DecidableEq, Repr

/-- Blue elements in the assembled planar reduction. -/
inductive BlueElement (Variable : Type*)
  | ordinaryInternal (atom : Variable) (slot : OccurrenceSlot)
      (element : OrdinaryInternal)
  | fixedRedInternal (atom : Variable) (slot : OccurrenceSlot)
      (element : FixedRedInternalBlue)
  | clauseInternal (clauseIndex : Nat)
  | clauseTerminal (clauseIndex : Nat)
      (group : X3CClauseTerminalGroup)
  deriving DecidableEq, Repr

/-- Triples in variable modules or clause cores. -/
inductive Triple (Variable : Type*)
  | ordinary (atom : Variable) (slot : OccurrenceSlot)
      (variant : VariableOccurrenceVariant)
      (triple : VariableOccurrenceTriple)
  | fixedRed (atom : Variable) (slot : OccurrenceSlot)
      (triple : FixedRedConnectorTriple)
  | clause (clauseIndex : Nat) (set : X3CClauseSet)
  deriving DecidableEq, Repr

/-- One typed periodic element reference. -/
structure Reference (Element : Type*) where
  atom : Element
  offset : Cell
  deriving DecidableEq, Repr

/-- One typed triple with a reference of each color. -/
structure TripleReferences (Variable : Type*) where
  red : Reference (RedElement Variable)
  green : Reference (GreenElement Variable)
  blue : Reference (BlueElement Variable)
  deriving DecidableEq, Repr

/-- The terminal element shared by one variable occurrence and clause core. -/
def redClauseTerminal {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : RedElement Variable :=
  .clauseTerminal
    (occurrenceClauseIndex source atom slot)
    (terminalGroupOfLiteralIndex
      (occurrenceLiteralIndex source atom slot))

/-- Green terminal shared by one occurrence and clause core. -/
def greenClauseTerminal {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : GreenElement Variable :=
  .clauseTerminal
    (occurrenceClauseIndex source atom slot)
    (terminalGroupOfLiteralIndex
      (occurrenceLiteralIndex source atom slot))

/-- Blue terminal shared by one occurrence and clause core. -/
def blueClauseTerminal {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : BlueElement Variable :=
  .clauseTerminal
    (occurrenceClauseIndex source atom slot)
    (terminalGroupOfLiteralIndex
      (occurrenceLiteralIndex source atom slot))

/-- Map the red field of an ordinary module to an assembled red element. -/
def ordinaryRedElement {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) :
    VariableOccurrenceElement → RedElement Variable
  | .leftContinuation =>
      .cycleLink atom (firstCycleLinkSlot source atom slot)
  | .rightContinuation =>
      .cycleLink atom (secondCycleLinkSlot source atom slot)
  | _ => redClauseTerminal source atom slot

/-- Map the green field of an ordinary module to an assembled green
element. -/
def ordinaryGreenElement {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) :
    VariableOccurrenceElement → GreenElement Variable
  | .cycleShared =>
      .ordinaryInternal atom slot .cycleShared
  | .auxiliaryShared =>
      .ordinaryInternal atom slot .auxiliaryShared
  | _ => greenClauseTerminal source atom slot

/-- Map the blue field of an ordinary module to an assembled blue element. -/
def ordinaryBlueElement {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) :
    VariableOccurrenceElement → BlueElement Variable
  | .cycleShared =>
      .ordinaryInternal atom slot .cycleShared
  | .auxiliaryShared =>
      .ordinaryInternal atom slot .auxiliaryShared
  | _ => blueClauseTerminal source atom slot

/-- References of one ordinary fixed-green or fixed-blue occurrence triple. -/
def ordinaryTripleReferences {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple) :
    TripleReferences Variable :=
  let references := triple.references variant
  let terminalOffset := occurrenceReverseOffset source atom slot
  ⟨⟨ordinaryRedElement source atom slot references.red,
      if references.red = .connectorRed then terminalOffset else (0, 0)⟩,
    ⟨ordinaryGreenElement source atom slot references.green,
      if references.green = .connectorGreen then
        terminalOffset else (0, 0)⟩,
    ⟨ordinaryBlueElement source atom slot references.blue,
      if references.blue = .connectorBlue then
        terminalOffset else (0, 0)⟩⟩

/-- Map a fixed-red red reference into the assembled presentation. -/
def fixedRedRedElement {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) :
    FixedRedConnectorRed → RedElement Variable
  | .leftTopPort =>
      .cycleLink atom (secondCycleLinkSlot source atom slot)
  | .leftBottomPort =>
      .cycleLink atom (firstCycleLinkSlot source atom slot)
  | .middleRung =>
      .fixedRedInternal atom slot .middleRung
  | .topAuxiliary =>
      .fixedRedInternal atom slot .topAuxiliary
  | .connectorPort => redClauseTerminal source atom slot

/-- Map a fixed-red green reference into the assembled presentation. -/
def fixedRedGreenElement {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) :
    FixedRedConnectorGreen → GreenElement Variable
  | .leftRung =>
      .fixedRedInternal atom slot .leftRung
  | .topRightLink =>
      .fixedRedInternal atom slot .topRightLink
  | .bottomRightLink =>
      .fixedRedInternal atom slot .bottomRightLink
  | .connectorPort => greenClauseTerminal source atom slot

/-- Map a fixed-red blue reference into the assembled presentation. -/
def fixedRedBlueElement {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) :
    FixedRedConnectorBlue → BlueElement Variable
  | .topLeftLink =>
      .fixedRedInternal atom slot .topLeftLink
  | .bottomLeftLink =>
      .fixedRedInternal atom slot .bottomLeftLink
  | .rightRung =>
      .fixedRedInternal atom slot .rightRung
  | .connectorPort => blueClauseTerminal source atom slot

/-- References of one fixed-red Figure 6 triple. -/
def fixedRedTripleReferences {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (triple : FixedRedConnectorTriple) :
    TripleReferences Variable :=
  let references := triple.references
  let terminalOffset := occurrenceReverseOffset source atom slot
  ⟨⟨fixedRedRedElement source atom slot references.red,
      if references.red = .connectorPort then
        terminalOffset else (0, 0)⟩,
    ⟨fixedRedGreenElement source atom slot references.green,
      if references.green = .connectorPort then
        terminalOffset else (0, 0)⟩,
    ⟨fixedRedBlueElement source atom slot references.blue,
      if references.blue = .connectorPort then
        terminalOffset else (0, 0)⟩⟩

/-- Red clause-core reference at one clause prototype. -/
def clauseRedElement {Variable : Type*} (clauseIndex : Nat) :
    X3CClauseElement → RedElement Variable
  | .internal _ => .clauseInternal clauseIndex
  | .terminal terminal =>
      .clauseTerminal clauseIndex terminal.group

/-- Green clause-core reference at one clause prototype. -/
def clauseGreenElement {Variable : Type*} (clauseIndex : Nat) :
    X3CClauseElement → GreenElement Variable
  | .internal _ => .clauseInternal clauseIndex
  | .terminal terminal =>
      .clauseTerminal clauseIndex terminal.group

/-- Blue clause-core reference at one clause prototype. -/
def clauseBlueElement {Variable : Type*} (clauseIndex : Nat) :
    X3CClauseElement → BlueElement Variable
  | .internal _ => .clauseInternal clauseIndex
  | .terminal terminal =>
      .clauseTerminal clauseIndex terminal.group

/-- References of one colored clause-core triple. -/
def clauseTripleReferences {Variable : Type*}
    (clauseIndex : Nat) (set : X3CClauseSet) :
    TripleReferences Variable :=
  let references := set.coloredReferences
  ⟨⟨clauseRedElement clauseIndex references.red, (0, 0)⟩,
    ⟨clauseGreenElement clauseIndex references.green, (0, 0)⟩,
    ⟨clauseBlueElement clauseIndex references.blue, (0, 0)⟩⟩

/-- References of every assembled prototype triple. -/
def tripleReferences {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Triple Variable → TripleReferences Variable
  | .ordinary atom slot variant triple =>
      ordinaryTripleReferences source atom slot variant triple
  | .fixedRed atom slot triple =>
      fixedRedTripleReferences source atom slot triple
  | .clause clauseIndex set =>
      clauseTripleReferences clauseIndex set

/-- Ordinary or fixed-red triples occupying one used variable slot. -/
def occurrenceTriples {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : List (Triple Variable) :=
  match occurrenceConnectorKind source atom slot with
  | .fixedRed =>
      allFixedRedTriples.map (Triple.fixedRed atom slot)
  | .fixedGreen =>
      allOrdinaryTriples.map
        (Triple.ordinary atom slot .fixedGreen)
  | .fixedBlue =>
      allOrdinaryTriples.map
        (Triple.ordinary atom slot .fixedBlue)

/-- All variable-module triples. -/
def variableTriples {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (Triple Variable) :=
  (occurringVariables source).flatMap fun atom =>
    (usedSlots source atom).flatMap fun slot =>
      occurrenceTriples source atom slot

/-- Nine clause-core triples for every prototype clause. -/
def clauseTriples {Variable : Type*}
    (source : PeriodicCNF Variable) : List (Triple Variable) :=
  (List.range source.clauses.length).flatMap fun clauseIndex =>
    allClauseSets.map (Triple.clause clauseIndex)

/-- Complete prototype-triple list. -/
def triples {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (Triple Variable) :=
  variableTriples source ++ clauseTriples source

/-- Red elements contributed by one used occurrence slot. -/
def occurrenceRedElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : List (RedElement Variable) :=
  [.cycleLink atom slot] ++
    match occurrenceConnectorKind source atom slot with
    | .fixedRed =>
        [.fixedRedInternal atom slot .middleRung,
          .fixedRedInternal atom slot .topAuxiliary]
    | .fixedGreen | .fixedBlue => []

/-- Green elements contributed by one used occurrence slot. -/
def occurrenceGreenElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : List (GreenElement Variable) :=
  match occurrenceConnectorKind source atom slot with
  | .fixedRed =>
      [.fixedRedInternal atom slot .leftRung,
        .fixedRedInternal atom slot .topRightLink,
        .fixedRedInternal atom slot .bottomRightLink]
  | .fixedGreen =>
      [.ordinaryInternal atom slot .cycleShared]
  | .fixedBlue =>
      [.ordinaryInternal atom slot .cycleShared]

/-- Blue elements contributed by one used occurrence slot. -/
def occurrenceBlueElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : List (BlueElement Variable) :=
  match occurrenceConnectorKind source atom slot with
  | .fixedRed =>
      [.fixedRedInternal atom slot .topLeftLink,
        .fixedRedInternal atom slot .bottomLeftLink,
        .fixedRedInternal atom slot .rightRung]
  | .fixedGreen =>
      [.ordinaryInternal atom slot .auxiliaryShared]
  | .fixedBlue =>
      [.ordinaryInternal atom slot .auxiliaryShared]

/-- Complete finite red-element presentation. -/
def redElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (RedElement Variable) :=
  ((occurringVariables source).flatMap fun atom =>
      (usedSlots source atom).flatMap fun slot =>
        occurrenceRedElements source atom slot) ++
    ((List.range source.clauses.length).flatMap fun clauseIndex =>
      [.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal clauseIndex))

/-- Complete finite green-element presentation. -/
def greenElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (GreenElement Variable) :=
  ((occurringVariables source).flatMap fun atom =>
      (usedSlots source atom).flatMap fun slot =>
        occurrenceGreenElements source atom slot) ++
    ((List.range source.clauses.length).flatMap fun clauseIndex =>
      [.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (GreenElement.clauseTerminal clauseIndex))

/-- Complete finite blue-element presentation. -/
def blueElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (BlueElement Variable) :=
  ((occurringVariables source).flatMap fun atom =>
      (usedSlots source atom).flatMap fun slot =>
        occurrenceBlueElements source atom slot) ++
    ((List.range source.clauses.length).flatMap fun clauseIndex =>
      [.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (BlueElement.clauseTerminal clauseIndex))

/-- Inspectable typed finite presentation of the periodic planar 3DM
instance. -/
structure TypedProblem (Variable : Type*) where
  redElements : List (RedElement Variable)
  greenElements : List (GreenElement Variable)
  blueElements : List (BlueElement Variable)
  triples : List (Triple Variable)
  references : Triple Variable → TripleReferences Variable

/-- Assemble the full typed periodic instance. -/
def problem {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : TypedProblem Variable where
  redElements := redElements source
  greenElements := greenElements source
  blueElements := blueElements source
  triples := triples source
  references := tripleReferences source

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
