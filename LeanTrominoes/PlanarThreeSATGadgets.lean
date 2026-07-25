import LeanTrominoes.PeriodicCNF

/-!
# Finite planar 3SAT gadgets

This file records the variable and clause vertices of the crossover in
Figure 8(b).  The coordinates use the integer grid shown in the figure.  A
literal's Boolean component is the value that makes that incidence true; the
two edge colors in the paper therefore become `true` and `false`.

The complete finite truth table is checked in Lean: a boundary assignment
extends through the gadget exactly when the left and right `a` ports agree
and the top and bottom `b` ports agree.  Thus the two logical wires cross
without interacting.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- A clause vertex together with its grid position. -/
structure EmbeddedClause (Variable : Type*) where
  position : Cell
  literals : List (Variable × Bool)
  deriving DecidableEq, Repr

/-- A finite clause is true when one incident literal has its designated
satisfying value. -/
def ClauseHolds {Variable : Type*} (assignment : Variable → Bool)
    (clause : EmbeddedClause Variable) : Prop :=
  ∃ literal ∈ clause.literals,
    assignment literal.1 = literal.2

instance {Variable : Type*} [DecidableEq Variable]
    (assignment : Variable → Bool) (clause : EmbeddedClause Variable) :
    Decidable (ClauseHolds assignment clause) := by
  unfold ClauseHolds
  infer_instance

/-- Every clause in a finite embedded formula is true. -/
def FormulaHolds {Variable : Type*} (assignment : Variable → Bool)
    (formula : List (EmbeddedClause Variable)) : Prop :=
  ∀ clause ∈ formula, ClauseHolds assignment clause

instance {Variable : Type*} [DecidableEq Variable]
    (assignment : Variable → Bool)
    (formula : List (EmbeddedClause Variable)) :
    Decidable (FormulaHolds assignment formula) := by
  unfold FormulaHolds
  infer_instance

/-- The thirteen variable vertices in Figure 8(b), named by their logical
role and geometric order. -/
inductive CrossoverVariable
  | aLeft
  | aInnerLeft
  | upperLeft
  | lowerLeft
  | bTop
  | bInnerTop
  | center
  | bInnerBottom
  | bBottom
  | upperRight
  | lowerRight
  | aInnerRight
  | aRight
  deriving DecidableEq, Repr, Fintype

/-- Grid position of each variable vertex in Figure 8(b). -/
def CrossoverVariable.position : CrossoverVariable → Cell
  | .aLeft => (1, 6)
  | .aInnerLeft => (3, 6)
  | .upperLeft => (5, 5)
  | .lowerLeft => (5, 7)
  | .bTop => (6, 1)
  | .bInnerTop => (6, 3)
  | .center => (6, 6)
  | .bInnerBottom => (6, 9)
  | .bBottom => (6, 11)
  | .upperRight => (7, 5)
  | .lowerRight => (7, 7)
  | .aInnerRight => (9, 6)
  | .aRight => (11, 6)

/-- One positioned clause of the crossover. -/
def crossoverClause (x y : Int)
    (literals : List (CrossoverVariable × Bool)) :
    EmbeddedClause CrossoverVariable :=
  ⟨(x, y), literals⟩

/-- The 26 clauses drawn in Figure 8(b), in lexicographic grid order. -/
def crossoverFormula : List (EmbeddedClause CrossoverVariable) :=
  [crossoverClause 2 6
      [(.aLeft, true), (.aInnerLeft, false)],
    crossoverClause 2 7
      [(.aLeft, false), (.aInnerLeft, true)],
    crossoverClause 3 3
      [(.aInnerLeft, false), (.upperLeft, false),
        (.bInnerTop, true)],
    crossoverClause 3 9
      [(.aInnerLeft, false), (.lowerLeft, false),
        (.bInnerBottom, false)],
    crossoverClause 4 5
      [(.aInnerLeft, true), (.upperLeft, true)],
    crossoverClause 4 6
      [(.upperLeft, true), (.lowerLeft, true)],
    crossoverClause 4 7
      [(.aInnerLeft, true), (.lowerLeft, true)],
    crossoverClause 5 2
      [(.bTop, false), (.bInnerTop, true)],
    crossoverClause 5 4
      [(.upperLeft, true), (.bInnerTop, false)],
    crossoverClause 5 6
      [(.upperLeft, false), (.lowerLeft, false), (.center, false)],
    crossoverClause 5 8
      [(.lowerLeft, true), (.bInnerBottom, true)],
    crossoverClause 6 2
      [(.bTop, true), (.bInnerTop, false)],
    crossoverClause 6 5
      [(.upperLeft, true), (.upperRight, true)],
    crossoverClause 6 7
      [(.lowerLeft, true), (.lowerRight, true)],
    crossoverClause 6 10
      [(.bInnerBottom, false), (.bBottom, true)],
    crossoverClause 7 4
      [(.bInnerTop, false), (.upperRight, true)],
    crossoverClause 7 6
      [(.center, true), (.upperRight, false), (.lowerRight, false)],
    crossoverClause 7 8
      [(.bInnerBottom, true), (.lowerRight, true)],
    crossoverClause 7 10
      [(.bInnerBottom, true), (.bBottom, false)],
    crossoverClause 8 5
      [(.upperRight, true), (.aInnerRight, false)],
    crossoverClause 8 6
      [(.upperRight, true), (.lowerRight, true)],
    crossoverClause 8 7
      [(.lowerRight, true), (.aInnerRight, false)],
    crossoverClause 9 3
      [(.bInnerTop, true), (.upperRight, false),
        (.aInnerRight, true)],
    crossoverClause 9 9
      [(.bInnerBottom, false), (.lowerRight, false),
        (.aInnerRight, true)],
    crossoverClause 10 5
      [(.aInnerRight, true), (.aRight, false)],
    crossoverClause 10 6
      [(.aInnerRight, false), (.aRight, true)]]

/-- A complete assignment satisfies the finite crossover. -/
def CrossoverHolds (assignment : CrossoverVariable → Bool) : Prop :=
  FormulaHolds assignment crossoverFormula

instance (assignment : CrossoverVariable → Bool) :
    Decidable (CrossoverHolds assignment) := by
  unfold CrossoverHolds
  infer_instance

/-- Assemble boundary and internal values into a complete crossover
assignment. -/
def crossoverAssignment
    (aLeft aRight bTop bBottom
      aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
      upperRight lowerRight aInnerRight : Bool) :
    CrossoverVariable → Bool
  | .aLeft => aLeft
  | .aInnerLeft => aInnerLeft
  | .upperLeft => upperLeft
  | .lowerLeft => lowerLeft
  | .bTop => bTop
  | .bInnerTop => bInnerTop
  | .center => center
  | .bInnerBottom => bInnerBottom
  | .bBottom => bBottom
  | .upperRight => upperRight
  | .lowerRight => lowerRight
  | .aInnerRight => aInnerRight
  | .aRight => aRight

/-- A boundary assignment extends to all nine internal crossover variables. -/
def CrossoverExtends (aLeft aRight bTop bBottom : Bool) : Prop :=
  ∃ aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
      upperRight lowerRight aInnerRight : Bool,
    CrossoverHolds
      (crossoverAssignment aLeft aRight bTop bBottom
        aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
        upperRight lowerRight aInnerRight)

instance (aLeft aRight bTop bBottom : Bool) :
    Decidable (CrossoverExtends aLeft aRight bTop bBottom) := by
  unfold CrossoverExtends
  exact Fintype.decidableExistsFintype

/-- Exhaustive certificate for the Lichtenstein crossover: the horizontal
and vertical values propagate independently. -/
theorem crossoverExtends_iff (aLeft aRight bTop bBottom : Bool) :
    CrossoverExtends aLeft aRight bTop bBottom ↔
      aLeft = aRight ∧ bTop = bBottom := by
  cases aLeft <;> cases aRight <;> cases bTop <;> cases bBottom <;>
    native_decide

/-- Every satisfying assignment to the crossover propagates each boundary
value to the opposite port.  This is the soundness direction needed when a
crossover embedded in a larger formula is projected back to its two original
wires. -/
theorem crossover_boundary_eq_of_holds
    {assignment : CrossoverVariable → Bool}
    (holds : CrossoverHolds assignment) :
    assignment .aLeft = assignment .aRight ∧
      assignment .bTop = assignment .bBottom := by
  apply (crossoverExtends_iff
    (assignment .aLeft) (assignment .aRight)
    (assignment .bTop) (assignment .bBottom)).mp
  refine ⟨assignment .aInnerLeft, assignment .upperLeft,
    assignment .lowerLeft, assignment .bInnerTop, assignment .center,
    assignment .bInnerBottom, assignment .upperRight,
    assignment .lowerRight, assignment .aInnerRight, ?_⟩
  have assignment_eq :
      crossoverAssignment
        (assignment .aLeft) (assignment .aRight)
        (assignment .bTop) (assignment .bBottom)
        (assignment .aInnerLeft) (assignment .upperLeft)
        (assignment .lowerLeft) (assignment .bInnerTop)
        (assignment .center) (assignment .bInnerBottom)
        (assignment .upperRight) (assignment .lowerRight)
        (assignment .aInnerRight) = assignment := by
    funext x
    cases x <;> rfl
  rw [assignment_eq]
  exact holds

/-- Conversely, two independently propagated boundary values can always be
extended to a satisfying assignment of the whole crossover. -/
theorem exists_crossover_holds_of_boundary_eq
    {aLeft aRight bTop bBottom : Bool}
    (horizontal : aLeft = aRight) (vertical : bTop = bBottom) :
    ∃ assignment : CrossoverVariable → Bool,
      CrossoverHolds assignment ∧
        assignment .aLeft = aLeft ∧
        assignment .aRight = aRight ∧
        assignment .bTop = bTop ∧
        assignment .bBottom = bBottom := by
  have hExtends :
      CrossoverExtends aLeft aRight bTop bBottom :=
    (crossoverExtends_iff aLeft aRight bTop bBottom).mpr
      ⟨horizontal, vertical⟩
  rcases hExtends with
    ⟨aInnerLeft, upperLeft, lowerLeft, bInnerTop, center, bInnerBottom,
      upperRight, lowerRight, aInnerRight, holds⟩
  refine ⟨crossoverAssignment aLeft aRight bTop bBottom
    aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
    upperRight lowerRight aInnerRight, holds, ?_⟩
  simp [crossoverAssignment]

/-! ## Variable duplicator -/

/-- The center and three ports of Figure 8(a). -/
inductive DuplicatorVariable
  | center
  | left
  | top
  | right
  deriving DecidableEq, Repr, Fintype

/-- Grid position of each variable in Figure 8(a). -/
def DuplicatorVariable.position : DuplicatorVariable → Cell
  | .center => (4, 4)
  | .left => (2, 4)
  | .top => (4, 2)
  | .right => (6, 4)

/-- One positioned clause of the duplicator. -/
def duplicatorClause (x y : Int)
    (literals : List (DuplicatorVariable × Bool)) :
    EmbeddedClause DuplicatorVariable :=
  ⟨(x, y), literals⟩

/-- The six binary implication clauses drawn in Figure 8(a). -/
def duplicatorFormula : List (EmbeddedClause DuplicatorVariable) :=
  [duplicatorClause 3 4 [(.left, true), (.center, false)],
    duplicatorClause 3 3 [(.left, false), (.center, true)],
    duplicatorClause 4 3 [(.top, true), (.center, false)],
    duplicatorClause 5 3 [(.top, false), (.center, true)],
    duplicatorClause 5 4 [(.right, true), (.center, false)],
    duplicatorClause 5 5 [(.right, false), (.center, true)]]

/-- Assemble values into a complete duplicator assignment. -/
def duplicatorAssignment (center left top right : Bool) :
    DuplicatorVariable → Bool
  | .center => center
  | .left => left
  | .top => top
  | .right => right

/-- The duplicator is satisfied exactly when every port carries the center
value. -/
theorem duplicatorHolds_iff (center left top right : Bool) :
    FormulaHolds (duplicatorAssignment center left top right)
        duplicatorFormula ↔
      left = center ∧ top = center ∧ right = center := by
  cases center <;> cases left <;> cases top <;> cases right <;>
    native_decide

/-- Assignment-independent form of `duplicatorHolds_iff`, convenient when
the four vertices are supplied by a larger embedded formula. -/
theorem duplicator_holds_iff (assignment : DuplicatorVariable → Bool) :
    FormulaHolds assignment duplicatorFormula ↔
      assignment .left = assignment .center ∧
      assignment .top = assignment .center ∧
      assignment .right = assignment .center := by
  have assignment_eq :
      duplicatorAssignment
        (assignment .center) (assignment .left)
        (assignment .top) (assignment .right) = assignment := by
    funext x
    cases x <;> rfl
  rw [← assignment_eq]
  exact duplicatorHolds_iff
    (assignment .center) (assignment .left)
    (assignment .top) (assignment .right)

end PlanarThreeSAT
end LeanTrominoes
