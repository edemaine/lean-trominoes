/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsOccurrences
import LeanTrominoes.PlanarThreeDMClauseGadget

/-!
# Typed periodic 3DM presentation for exact-one SAT

This file assembles the variable and paired-port clause gadgets before their
finite element types are encoded by natural numbers.  Keeping meaningful
types at this boundary makes the incidence construction inspectable.

Each occurring protovariable gets the six triples of Figure 10(a).  Its first,
second, and third pairs serve the first three syntactic occurrences.  Within
one pair, the triple whose phase agrees with the literal sign is the literal
port and the other is its complementary port.  Unused pairs share one private
blue element, which is covered exactly once because their selections are
complementary.

For every protoclause there is one common red, green, and main blue element.
Every literal occurrence adds a clause-local auxiliary triple and a
degree-two complementary blue element.  A variable triple at the literal
cell references its clause elements at the negated literal offset, so it meets
the auxiliary triples living at the clause translate.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- The three occurrence slots exposed by one six-triple variable cycle. -/
inductive OccurrenceSlot
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

namespace OccurrenceSlot

def index : OccurrenceSlot → Nat
  | .first => 0
  | .second => 1
  | .third => 2

def all : List OccurrenceSlot := [.first, .second, .third]

end OccurrenceSlot

/-- Stable clockwise enumeration of the variable triples. -/
def allVariableTriples : List PlanarThreeDM.VariableTriple :=
  [.topLeft, .topRight, .rightMiddle, .bottomRight,
    .bottomLeft, .leftMiddle]

/-- Stable enumeration of the internal red variable elements. -/
def allVariableReds : List PlanarThreeDM.VariableRed :=
  [.right, .bottom, .left]

/-- Stable enumeration of the internal green variable elements. -/
def allVariableGreens : List PlanarThreeDM.VariableGreen :=
  [.top, .right, .left]

/-- The occurrence pair containing one variable triple. -/
def variableTripleSlot :
    PlanarThreeDM.VariableTriple → OccurrenceSlot
  | .topLeft | .topRight => .first
  | .rightMiddle | .bottomRight => .second
  | .bottomLeft | .leftMiddle => .third

/-- The variable value carried by a selected triple: the first triple in each
occurrence pair carries `true`, and the second carries `false`. -/
def variableTripleValue :
    PlanarThreeDM.VariableTriple → Bool
  | .topLeft | .rightMiddle | .bottomLeft => true
  | .topRight | .bottomRight | .leftMiddle => false

/-- The Figure 10(a) selection is equality with the phase carried by the
triple. -/
theorem variableSelection_eq_beq (value : Bool)
    (triple : PlanarThreeDM.VariableTriple) :
    PlanarThreeDM.variableSelection value triple =
      (value == variableTripleValue triple) := by
  cases value <;> cases triple <;> rfl

/-- The two triples in each occurrence pair carry opposite phases. -/
theorem occurrencePair_values :
    variableTripleValue .topRight =
        !variableTripleValue .topLeft ∧
      variableTripleValue .bottomRight =
        !variableTripleValue .rightMiddle ∧
      variableTripleValue .leftMiddle =
        !variableTripleValue .bottomLeft := by
  decide

/-- A syntactic literal occurrence with its clause and literal indices. -/
abbrev TaggedOccurrence (Variable : Type*) :=
  PeriodicLiteral Variable × Nat × Nat

/-- All syntactic occurrences of one protovariable, in presentation order. -/
def occurrencesOf {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    List (TaggedOccurrence Variable) :=
  (PeriodicThreeSATThree.taggedLiterals source).filter fun tagged =>
    tagged.1.atom = atom

/-- The occurrence assigned to one of the three available variable slots. -/
def occurrenceAt {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) : Option (TaggedOccurrence Variable) :=
  (occurrencesOf source atom)[slot.index]?

/-- Red elements are internal variable-cycle elements or clause cores. -/
inductive RedElement (Variable : Type*)
  | variable (atom : Variable) (element : PlanarThreeDM.VariableRed)
  | clause (clauseIndex : Nat)
  deriving DecidableEq, Repr

/-- Green elements are internal variable-cycle elements or clause cores. -/
inductive GreenElement (Variable : Type*)
  | variable (atom : Variable) (element : PlanarThreeDM.VariableGreen)
  | clause (clauseIndex : Nat)
  deriving DecidableEq, Repr

/-- Blue elements join literal ports, complementary ports, or an unused
variable occurrence pair. -/
inductive BlueElement (Variable : Type*)
  | clause (clauseIndex : Nat)
  | complement (clauseIndex literalIndex : Nat)
  | unused (atom : Variable) (slot : OccurrenceSlot)
  deriving DecidableEq, Repr

/-- Triples belong either to a variable cycle or to one clause occurrence. -/
inductive Triple (Variable : Type*)
  | variable (atom : Variable)
      (triple : PlanarThreeDM.VariableTriple)
  | clauseAuxiliary (clauseIndex literalIndex : Nat)
  deriving DecidableEq, Repr

/-- A typed periodic element reference. -/
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

/-- Negate the cell offset of a source literal. -/
def reverseOffset (offset : Cell) : Cell :=
  (-offset.1, -offset.2)

@[simp]
theorem add_reverseOffset (translate offset : Cell) :
    Cell.add (Cell.add translate offset) (reverseOffset offset) =
      translate := by
  rcases translate with ⟨x, y⟩
  rcases offset with ⟨dx, dy⟩
  simp [Cell.add, reverseOffset]

/-- The blue element named by one variable port. -/
def variableBlueElement {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (triple : PlanarThreeDM.VariableTriple) :
    BlueElement Variable :=
  let slot := variableTripleSlot triple
  match occurrenceAt source atom slot with
  | none => .unused atom slot
  | some tagged =>
      if variableTripleValue triple = tagged.1.value then
        .clause tagged.2.1
      else
        .complement tagged.2.1 tagged.2.2

/-- Both ports of a used occurrence point back from its variable cell to the
translate of the containing clause. -/
def variableBlueOffset {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (triple : PlanarThreeDM.VariableTriple) : Cell :=
  match occurrenceAt source atom (variableTripleSlot triple) with
  | none => (0, 0)
  | some tagged => reverseOffset tagged.1.offset

/-- References of a variable-cycle triple. -/
def variableTripleReferences {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (triple : PlanarThreeDM.VariableTriple) :
    TripleReferences Variable :=
  let references := triple.references
  ⟨⟨.variable atom references.red, (0, 0)⟩,
    ⟨.variable atom references.green, (0, 0)⟩,
    ⟨variableBlueElement source atom triple,
      variableBlueOffset source atom triple⟩⟩

/-- References of the auxiliary triple for one literal occurrence. -/
def clauseAuxiliaryReferences {Variable : Type*}
    (clauseIndex literalIndex : Nat) :
    TripleReferences Variable :=
  ⟨⟨.clause clauseIndex, (0, 0)⟩,
    ⟨.clause clauseIndex, (0, 0)⟩,
    ⟨.complement clauseIndex literalIndex, (0, 0)⟩⟩

/-- References of every actual prototype triple. -/
def tripleReferences {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : Triple Variable →
      TripleReferences Variable
  | .variable atom triple =>
      variableTripleReferences source atom triple
  | .clauseAuxiliary clauseIndex literalIndex =>
      clauseAuxiliaryReferences clauseIndex literalIndex

/-- Prototypical variables that actually occur in the source presentation. -/
def occurringVariables {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Variable :=
  (PeriodicCNF.variableOccurrences source).dedup

/-- All six variable-cycle triples for every occurring protovariable. -/
def variableTriples {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (Triple Variable) :=
  (occurringVariables source).flatMap fun atom =>
    allVariableTriples.map (Triple.variable atom)

/-- One auxiliary triple for each literal occurrence. -/
def clauseAuxiliaryTriples {Variable : Type*}
    (source : PeriodicCNF Variable) : List (Triple Variable) :=
  (PeriodicThreeSATThree.taggedLiterals source).map fun tagged =>
    .clauseAuxiliary tagged.2.1 tagged.2.2

/-- Complete finite list of prototype triples. -/
def triples {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (Triple Variable) :=
  variableTriples source ++ clauseAuxiliaryTriples source

/-- Finite red-element presentation. -/
def redElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (RedElement Variable) :=
  ((occurringVariables source).flatMap fun atom =>
      allVariableReds.map (RedElement.variable atom)) ++
    (List.range source.clauses.length).map RedElement.clause

/-- Finite green-element presentation. -/
def greenElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (GreenElement Variable) :=
  ((occurringVariables source).flatMap fun atom =>
      allVariableGreens.map (GreenElement.variable atom)) ++
    (List.range source.clauses.length).map GreenElement.clause

/-- The unused variable slots that need a private degree-two blue element. -/
def unusedSlots {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (Variable × OccurrenceSlot) :=
  (occurringVariables source).flatMap fun atom =>
    OccurrenceSlot.all.filterMap fun slot =>
      if (occurrenceAt source atom slot).isNone then
        some (atom, slot)
      else
        none

/-- Finite blue-element presentation. -/
def blueElements {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (BlueElement Variable) :=
  (List.range source.clauses.length).map BlueElement.clause ++
    ((PeriodicThreeSATThree.taggedLiterals source).map fun tagged =>
      BlueElement.complement tagged.2.1 tagged.2.2) ++
    ((unusedSlots source).map fun tagged =>
      BlueElement.unused tagged.1 tagged.2)

/-- A typed finite presentation of the periodic 3DM instance. -/
structure TypedPeriodicThreeDM (Variable : Type*) where
  redElements : List (RedElement Variable)
  greenElements : List (GreenElement Variable)
  blueElements : List (BlueElement Variable)
  triples : List (Triple Variable)
  references : Triple Variable → TripleReferences Variable

/-- Assemble the complete typed periodic 3DM presentation. -/
def problem {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    TypedPeriodicThreeDM Variable where
  redElements := redElements source
  greenElements := greenElements source
  blueElements := blueElements source
  triples := triples source
  references := tripleReferences source

/-- A used port whose phase agrees with the literal sign names the main
clause blue element. -/
theorem variableBlueElement_eq_clause_of_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (triple : PlanarThreeDM.VariableTriple)
    (tagged : TaggedOccurrence Variable)
    (occurrence :
      occurrenceAt source atom (variableTripleSlot triple) = some tagged)
    (agrees : variableTripleValue triple = tagged.1.value) :
    variableBlueElement source atom triple =
      .clause tagged.2.1 := by
  simp [variableBlueElement, occurrence, agrees]

/-- The opposite port of a used pair names its occurrence-specific
complementary blue element. -/
theorem variableBlueElement_eq_complement_of_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (triple : PlanarThreeDM.VariableTriple)
    (tagged : TaggedOccurrence Variable)
    (occurrence :
      occurrenceAt source atom (variableTripleSlot triple) = some tagged)
    (opposes : variableTripleValue triple ≠ tagged.1.value) :
    variableBlueElement source atom triple =
      .complement tagged.2.1 tagged.2.2 := by
  simp [variableBlueElement, occurrence, opposes]

/-- An unused pair names its private blue cap. -/
theorem variableBlueElement_eq_unused
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (triple : PlanarThreeDM.VariableTriple)
    (unused :
      occurrenceAt source atom (variableTripleSlot triple) = none) :
    variableBlueElement source atom triple =
      .unused atom (variableTripleSlot triple) := by
  simp [variableBlueElement, unused]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
