import LeanTrominoes.PeriodicCNF

/-!
# One-dimensional periodic CNF semantics

The hardness half of the 1.5D result starts from a Boolean constraint system
repeated along one integer coordinate.  The existing `PeriodicCNF` syntax uses
two-dimensional offsets because it is shared with the plane reductions.  This
file identifies the one-dimensional fragment (all vertical offsets are zero),
defines its direct line semantics, and proves that this semantics agrees with
the existing plane semantics.
-/

namespace LeanTrominoes

namespace PeriodicLiteral

/-- Whether a periodic literal holds at one integer translate on the line. -/
def HoldsOnLine {Variable : Type*}
    (assignment : Variable → Int → Bool) (translate : Int)
    (literal : PeriodicLiteral Variable) : Prop :=
  assignment literal.atom (translate + literal.offset.1) = literal.value

end PeriodicLiteral

namespace PeriodicClause

/-- Distance between two literal offsets in the unbounded coordinate. -/
def offsetDistanceOnLine {Variable : Type*}
    (first second : PeriodicLiteral Variable) : Nat :=
  (first.offset.1 - second.offset.1).natAbs

/-- A one-dimensional protoclauses is local when every two offsets are at
distance at most one. -/
def IsLocalOnLine {Variable : Type*}
    (clause : PeriodicClause Variable) : Prop :=
  ∀ first ∈ clause, ∀ second ∈ clause,
    offsetDistanceOnLine first second ≤ 1

/-- Whether some literal in a clause holds at one translate on the line. -/
def HoldsOnLine {Variable : Type*}
    (assignment : Variable → Int → Bool) (translate : Int)
    (clause : PeriodicClause Variable) : Prop :=
  ∃ literal ∈ clause, literal.HoldsOnLine assignment translate

end PeriodicClause

namespace PeriodicCNF

/-- A formula belongs to the one-dimensional fragment when every literal has
zero vertical offset. -/
def IsOneDimensional {Variable : Type*}
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ clause ∈ formula.clauses, ∀ literal ∈ clause,
    literal.offset.2 = 0

/-- Executable recognition of the one-dimensional fragment. -/
def isOneDimensional {Variable : Type*}
    (formula : PeriodicCNF Variable) : Bool :=
  formula.clauses.all fun clause =>
    clause.all fun literal => literal.offset.2 == 0

@[simp]
theorem isOneDimensional_eq_true_iff {Variable : Type*}
    (formula : PeriodicCNF Variable) :
    formula.isOneDimensional = true ↔ formula.IsOneDimensional := by
  simp [isOneDimensional, IsOneDimensional]

instance {Variable : Type*} (formula : PeriodicCNF Variable) :
    Decidable formula.IsOneDimensional :=
  decidable_of_iff (formula.isOneDimensional = true)
    formula.isOneDimensional_eq_true_iff

/-- Every clause is local when measured in the unbounded coordinate. -/
def IsLocalOnLine {Variable : Type*}
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ clause ∈ formula.clauses, clause.IsLocalOnLine

/-- Whether a line assignment satisfies every clause at every integer
translate. -/
def SatisfiesOnLine {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Int → Bool) : Prop :=
  ∀ translate clause, clause ∈ formula.clauses →
    clause.HoldsOnLine assignment translate

/-- Whether a periodic CNF formula has a satisfying assignment on the line. -/
def SatisfiableOnLine {Variable : Type*}
    (formula : PeriodicCNF Variable) : Prop :=
  ∃ assignment : Variable → Int → Bool,
    formula.SatisfiesOnLine assignment

/-- Lift a line assignment uniformly through all horizontal rows. -/
def liftLineAssignment {Variable : Type*}
    (assignment : Variable → Int → Bool) : Variable → Cell → Bool :=
  fun atom cell => assignment atom cell.1

/-- Restrict a plane assignment to its row at vertical coordinate zero. -/
def restrictPlaneAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) : Variable → Int → Bool :=
  fun atom horizontal => assignment atom (horizontal, 0)

/-- Locality in the plane agrees with locality on the line for a horizontal
clause. -/
theorem clause_isLocal_iff_isLocalOnLine {Variable : Type*}
    {clause : PeriodicClause Variable}
    (horizontal : ∀ literal ∈ clause, literal.offset.2 = 0) :
    clause.IsLocal ↔ clause.IsLocalOnLine := by
  constructor
  · intro locality first firstMem second secondMem
    have bound := locality first firstMem second secondMem
    simp [PeriodicClause.offsetDistance,
      horizontal first firstMem, horizontal second secondMem] at bound
    exact bound
  · intro locality first firstMem second secondMem
    have bound := locality first firstMem second secondMem
    simpa [PeriodicClause.offsetDistance,
      PeriodicClause.offsetDistanceOnLine,
      horizontal first firstMem, horizontal second secondMem] using bound

/-- Plane locality and line locality agree for a one-dimensional formula. -/
theorem isLocal_iff_isLocalOnLine {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (oneDimensional : formula.IsOneDimensional) :
    formula.IsLocal ↔ formula.IsLocalOnLine := by
  constructor <;> intro locality clause clauseMem
  · exact (clause_isLocal_iff_isLocalOnLine
      (oneDimensional clause clauseMem)).mp (locality clause clauseMem)
  · exact (clause_isLocal_iff_isLocalOnLine
      (oneDimensional clause clauseMem)).mpr (locality clause clauseMem)

/-- A satisfying line assignment lifts to a satisfying plane assignment. -/
theorem satisfiable_of_satisfiableOnLine {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (satisfiable : formula.SatisfiableOnLine) :
    formula.Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := satisfiable
  refine ⟨liftLineAssignment assignment, ?_⟩
  intro translate clause clauseMem
  obtain ⟨literal, literalMem, holds⟩ :=
    satisfies translate.1 clause clauseMem
  exact ⟨literal, literalMem, by
    simpa [PeriodicLiteral.Holds, PeriodicLiteral.HoldsOnLine,
      liftLineAssignment, Cell.add] using holds⟩

/-- A satisfying plane assignment restricts to a satisfying line assignment
for every one-dimensional formula. -/
theorem satisfiableOnLine_of_satisfiable {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (oneDimensional : formula.IsOneDimensional)
    (satisfiable : formula.Satisfiable) :
    formula.SatisfiableOnLine := by
  obtain ⟨assignment, satisfies⟩ := satisfiable
  refine ⟨restrictPlaneAssignment assignment, ?_⟩
  intro translate clause clauseMem
  obtain ⟨literal, literalMem, holds⟩ :=
    satisfies (translate, 0) clause clauseMem
  have vertical := oneDimensional clause clauseMem literal literalMem
  exact ⟨literal, literalMem, by
    simpa [PeriodicLiteral.Holds, PeriodicLiteral.HoldsOnLine,
      restrictPlaneAssignment, Cell.add, vertical] using holds⟩

/-- For a one-dimensional formula, the direct line semantics is equivalent to
the existing plane semantics. -/
theorem satisfiable_iff_satisfiableOnLine {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (oneDimensional : formula.IsOneDimensional) :
    formula.Satisfiable ↔ formula.SatisfiableOnLine :=
  ⟨satisfiableOnLine_of_satisfiable oneDimensional,
    satisfiable_of_satisfiableOnLine⟩

/-- The concrete source language used by the 1.5D hardness chain.  Formulas
outside the horizontal local fragment are rejected. -/
def LocalPeriodicCNF1DSAT (formula : PeriodicCNF Nat) : Prop :=
  formula.IsOneDimensional ∧
    formula.IsLocalOnLine ∧
    formula.SatisfiableOnLine

end PeriodicCNF

end LeanTrominoes
