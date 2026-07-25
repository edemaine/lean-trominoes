import LeanTrominoes.PeriodicOneInThreeToThreeDMAssignmentEncoding

/-!
# Recovering Boolean values from variable-gadget matchings

An arbitrary matching of a six-triple variable cycle determines its Boolean
value at the top-left port.  The verified gadget classification then forces
every literal-side port to equal comparison with the literal sign, and every
complementary port to carry the opposite bit.  These are the local soundness
facts used to recover an exact-one assignment from a 3DM matching.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Read the represented Boolean value from a typed matching's top-left
variable port. -/
def assignmentOfMatching {Variable : Type*}
    (matching : Triple Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell =>
    matching (.variable atom .topLeft) cell

/-- Any valid variable-gadget selection is the alternating selection indexed
by its top-left port. -/
theorem variableSelection_eq_of_gadgetHolds
    (selected : PlanarThreeDM.VariableTriple → Bool)
    (holds : PlanarThreeDM.VariableGadgetHolds selected) :
    selected =
      PlanarThreeDM.variableSelection (selected .topLeft) := by
  rcases
      (PlanarThreeDM.variableGadgetHolds_iff selected).mp holds with
    selectedTrue | selectedFalse
  · rw [selectedTrue]
    rfl
  · rw [selectedFalse]
    rfl

/-- A literal-side port of any valid variable cycle is selected exactly when
the represented value agrees with the literal sign. -/
theorem literalTriple_eq_beq_of_gadgetHolds
    (selected : PlanarThreeDM.VariableTriple → Bool)
    (holds : PlanarThreeDM.VariableGadgetHolds selected)
    (slot : OccurrenceSlot) (value : Bool) :
    selected (slot.literalTriple value) =
      (selected .topLeft == value) := by
  rw [variableSelection_eq_of_gadgetHolds selected holds,
    variableSelection_eq_beq]
  simp [PlanarThreeDM.variableSelection]

/-- The paired port carries the Boolean complement of the literal-side
selection. -/
theorem complementTriple_eq_not_beq_of_gadgetHolds
    (selected : PlanarThreeDM.VariableTriple → Bool)
    (holds : PlanarThreeDM.VariableGadgetHolds selected)
    (slot : OccurrenceSlot) (value : Bool) :
    selected (slot.complementTriple value) =
      !(selected .topLeft == value) := by
  rw [variableSelection_eq_of_gadgetHolds selected holds,
    variableSelection_eq_beq]
  cases slot <;> cases state : selected .topLeft <;> cases value <;>
    simp [PlanarThreeDM.variableSelection,
      OccurrenceSlot.complementTriple, OccurrenceSlot.trueTriple,
      OccurrenceSlot.falseTriple, variableTripleValue]

/-- The literal-side port of a valid typed variable cycle reads the recovered
Boolean assignment at that variable cell. -/
theorem matching_literalPort_of_variableGadgetHolds
    {Variable : Type*}
    (matching : Triple Variable → Cell → Bool)
    (atom : Variable) (cell : Cell)
    (holds : PlanarThreeDM.VariableGadgetHolds fun triple =>
      matching (.variable atom triple) cell)
    (slot : OccurrenceSlot) (value : Bool) :
    matching (.variable atom (slot.literalTriple value)) cell =
      (assignmentOfMatching matching atom cell == value) := by
  exact literalTriple_eq_beq_of_gadgetHolds
    (fun triple => matching (.variable atom triple) cell)
    holds slot value

/-- The complementary port of a valid typed variable cycle carries the
opposite recovered literal value. -/
theorem matching_complementPort_of_variableGadgetHolds
    {Variable : Type*}
    (matching : Triple Variable → Cell → Bool)
    (atom : Variable) (cell : Cell)
    (holds : PlanarThreeDM.VariableGadgetHolds fun triple =>
      matching (.variable atom triple) cell)
    (slot : OccurrenceSlot) (value : Bool) :
    matching (.variable atom (slot.complementTriple value)) cell =
      !(assignmentOfMatching matching atom cell == value) := by
  exact complementTriple_eq_not_beq_of_gadgetHolds
    (fun triple => matching (.variable atom triple) cell)
    holds slot value

/-- At the literal's translated variable cell, a valid variable gadget's
literal port equals the recovered source literal truth value. -/
theorem matching_literalPort_eq_literalTruth
    {Variable : Type*}
    (matching : Triple Variable → Cell → Bool)
    (translate : Cell) (literal : PeriodicLiteral Variable)
    (slot : OccurrenceSlot)
    (holds : PlanarThreeDM.VariableGadgetHolds fun triple =>
      matching (.variable literal.atom triple)
        (Cell.add translate literal.offset)) :
    matching
        (.variable literal.atom (slot.literalTriple literal.value))
        (Cell.add translate literal.offset) =
      PeriodicOneInThree.literalTruth
        (assignmentOfMatching matching) translate literal := by
  exact matching_literalPort_of_variableGadgetHolds
    matching literal.atom (Cell.add translate literal.offset)
    holds slot literal.value

/-- The complementary port similarly equals the negation of recovered literal
truth. -/
theorem matching_complementPort_eq_not_literalTruth
    {Variable : Type*}
    (matching : Triple Variable → Cell → Bool)
    (translate : Cell) (literal : PeriodicLiteral Variable)
    (slot : OccurrenceSlot)
    (holds : PlanarThreeDM.VariableGadgetHolds fun triple =>
      matching (.variable literal.atom triple)
        (Cell.add translate literal.offset)) :
    matching
        (.variable literal.atom (slot.complementTriple literal.value))
        (Cell.add translate literal.offset) =
      !PeriodicOneInThree.literalTruth
        (assignmentOfMatching matching) translate literal := by
  exact matching_complementPort_of_variableGadgetHolds
    matching literal.atom (Cell.add translate literal.offset)
    holds slot literal.value

/-- The main blue constraint of any paired-port clause gadget immediately
recovers its exact-one literal relation. -/
theorem clauseHolds_of_clauseGadgetHolds
    (literals complements auxiliaries : List Bool)
    (holds :
      PlanarThreeDM.ClauseGadgetHolds
        literals complements auxiliaries) :
    PeriodicOneInThree.ExactlyOne literals :=
  holds.1

/-- When literal values come from a recovered assignment, the clause
gadget's main blue constraint is precisely source clause satisfaction. -/
theorem recoveredClauseHolds_of_clauseGadgetHolds
    {Variable : Type*}
    (matching : Triple Variable → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Variable)
    (complements auxiliaries : List Bool)
    (holds :
      PlanarThreeDM.ClauseGadgetHolds
        (PeriodicOneInThree.clauseValues
          (assignmentOfMatching matching) translate clause)
        complements auxiliaries) :
    PeriodicOneInThree.ClauseHolds
      (assignmentOfMatching matching) translate clause :=
  holds.1

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
