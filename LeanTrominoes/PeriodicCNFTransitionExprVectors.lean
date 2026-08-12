import LeanTrominoes.PeriodicCNFTransitionExprCompleteness

/-!
# Boolean-vector transition expressions

This file builds the reusable expression layer needed to encode bounded
machine configurations.  It provides conjunctions, equality of current and
next bit vectors, exact-one constraints, and a no-overflow binary successor
relation.  The semantic theorems are stated before CNF compilation, so the
soundness and completeness results for `compileTransitionExpr` can later be
applied uniformly to a complete machine transition.
-/

namespace LeanTrominoes

namespace PeriodicCNF

namespace TransitionExpr

/-- Read one atom from the current transition endpoint. -/
def current (atom : Nat) : TransitionExpr :=
  .wire ⟨.current, atom⟩

/-- Read one atom from the next transition endpoint. -/
def next (atom : Nat) : TransitionExpr :=
  .wire ⟨.next, atom⟩

@[simp]
theorem current_eval (atom : Nat) (currentValues nextValues : Nat → Bool) :
    (current atom).eval currentValues nextValues = currentValues atom :=
  rfl

@[simp]
theorem next_eval (atom : Nat) (currentValues nextValues : Nat → Bool) :
    (next atom).eval currentValues nextValues = nextValues atom :=
  rfl

/-- Conjoin a finite list of expressions, with the empty conjunction true. -/
def all : List TransitionExpr → TransitionExpr
  | [] => .constant true
  | expression :: expressions => .and expression (all expressions)

@[simp]
theorem all_eval (expressions : List TransitionExpr)
    (currentValues nextValues : Nat → Bool) :
    (all expressions).eval currentValues nextValues =
      expressions.all fun expression =>
        expression.eval currentValues nextValues := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp [all, TransitionExpr.eval, ih]

/-- Disjoin a finite list of expressions, with the empty disjunction false. -/
def any : List TransitionExpr → TransitionExpr
  | [] => .constant false
  | expression :: expressions => .or expression (any expressions)

@[simp]
theorem any_eval (expressions : List TransitionExpr)
    (currentValues nextValues : Nat → Bool) :
    (any expressions).eval currentValues nextValues =
      expressions.any fun expression =>
        expression.eval currentValues nextValues := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp [any, TransitionExpr.eval, ih]

/-- Boolean equality expressed using only the primitive transition gates. -/
def equal (first second : TransitionExpr) : TransitionExpr :=
  .or (.and first second) (.and (.not first) (.not second))

@[simp]
theorem equal_eval (first second : TransitionExpr)
    (currentValues nextValues : Nat → Bool) :
    (equal first second).eval currentValues nextValues =
      decide (first.eval currentValues nextValues =
        second.eval currentValues nextValues) := by
  cases firstValue : first.eval currentValues nextValues <;>
    cases secondValue : second.eval currentValues nextValues <;>
      simp [equal, TransitionExpr.eval, firstValue, secondValue]

/-- Equality between a current-slice vector and a next-slice vector.  A length
mismatch is rejected. -/
def vectorsEqual : List Nat → List Nat → TransitionExpr
  | [], [] => .constant true
  | first :: firsts, second :: seconds =>
      .and (equal (current first) (next second))
        (vectorsEqual firsts seconds)
  | _, _ => .constant false

@[simp]
theorem vectorsEqual_eval_iff (first second : List Nat)
    (currentValues nextValues : Nat → Bool) :
    (vectorsEqual first second).eval currentValues nextValues = true ↔
      first.map currentValues = second.map nextValues := by
  induction first generalizing second with
  | nil =>
      cases second <;> simp [vectorsEqual, TransitionExpr.eval]
  | cons first firsts ih =>
      cases second with
      | nil => simp [vectorsEqual, TransitionExpr.eval]
      | cons second seconds =>
          simp [vectorsEqual, TransitionExpr.eval, ih]

/-- A list of Boolean values contains exactly one true entry. -/
def ExactlyOneTrue : List Bool → Prop
  | [] => False
  | value :: values =>
      (value = true ∧ ∀ other ∈ values, other = false) ∨
        (value = false ∧ ExactlyOneTrue values)

/-- Express that exactly one expression in a list is true. -/
def exactlyOne : List TransitionExpr → TransitionExpr
  | [] => .constant false
  | expression :: expressions =>
      .or
        (.and expression (all (expressions.map TransitionExpr.not)))
        (.and (.not expression) (exactlyOne expressions))

@[simp]
theorem exactlyOne_eval_iff (expressions : List TransitionExpr)
    (currentValues nextValues : Nat → Bool) :
    (exactlyOne expressions).eval currentValues nextValues = true ↔
      ExactlyOneTrue (expressions.map fun expression =>
        expression.eval currentValues nextValues) := by
  induction expressions with
  | nil => simp [exactlyOne, ExactlyOneTrue, TransitionExpr.eval]
  | cons expression expressions ih =>
      cases value : expression.eval currentValues nextValues <;>
        simp [exactlyOne, ExactlyOneTrue, TransitionExpr.eval, ih,
          all_eval, value]

/-- Exact-one constraint for a family of current-slice atoms. -/
def currentExactlyOne (atoms : List Nat) : TransitionExpr :=
  exactlyOne (atoms.map current)

@[simp]
theorem currentExactlyOne_eval_iff (atoms : List Nat)
    (currentValues nextValues : Nat → Bool) :
    (currentExactlyOne atoms).eval currentValues nextValues = true ↔
      ExactlyOneTrue (atoms.map currentValues) := by
  simpa [currentExactlyOne, Function.comp_def] using
    exactlyOne_eval_iff (atoms.map current) currentValues nextValues

/-- Little-endian fixed-width successor without overflow. -/
def BinarySuccessor : List Bool → List Bool → Prop
  | [], [] => False
  | false :: currentValues, true :: nextValues =>
      currentValues = nextValues
  | true :: currentValues, false :: nextValues =>
      BinarySuccessor currentValues nextValues
  | _, _ => False

/-- Express that the next-slice bit vector is the no-overflow successor of the
current-slice bit vector.  Both atom lists are little endian. -/
def binarySuccessor : List Nat → List Nat → TransitionExpr
  | [], [] => .constant false
  | currentAtom :: currentAtoms, nextAtom :: nextAtoms =>
      .or
        (.and
          (.and (.not (current currentAtom)) (next nextAtom))
          (vectorsEqual currentAtoms nextAtoms))
        (.and
          (.and (current currentAtom) (.not (next nextAtom)))
          (binarySuccessor currentAtoms nextAtoms))
  | _, _ => .constant false

@[simp]
theorem binarySuccessor_eval_iff (currentAtoms nextAtoms : List Nat)
    (currentValues nextValues : Nat → Bool) :
    (binarySuccessor currentAtoms nextAtoms).eval
        currentValues nextValues = true ↔
      BinarySuccessor (currentAtoms.map currentValues)
        (nextAtoms.map nextValues) := by
  induction currentAtoms generalizing nextAtoms with
  | nil =>
      cases nextAtoms <;>
        simp [binarySuccessor, BinarySuccessor, TransitionExpr.eval]
  | cons currentAtom currentAtoms ih =>
      cases nextAtoms with
      | nil =>
          simp [binarySuccessor, BinarySuccessor, TransitionExpr.eval]
      | cons nextAtom nextAtoms =>
          cases currentValue : currentValues currentAtom <;>
            cases nextValue : nextValues nextAtom <;>
              simp [binarySuccessor, BinarySuccessor, TransitionExpr.eval,
                ih, currentValue, nextValue]

/-- Every atom in a finite atom vector lies below a boundary. -/
def AtomListBelow (atoms : List Nat) (bound : Nat) : Prop :=
  ∀ atom ∈ atoms, atom < bound

theorem all_atomsBelow {expressions : List TransitionExpr} {bound : Nat}
    (bounded : ∀ expression ∈ expressions,
      expression.AtomsBelow bound) :
    (all expressions).AtomsBelow bound := by
  induction expressions with
  | nil => trivial
  | cons expression expressions ih =>
      exact ⟨bounded expression (by simp),
        ih (fun member memberMem => bounded member (by simp [memberMem]))⟩

theorem exactlyOne_atomsBelow {expressions : List TransitionExpr} {bound : Nat}
    (bounded : ∀ expression ∈ expressions,
      expression.AtomsBelow bound) :
    (exactlyOne expressions).AtomsBelow bound := by
  induction expressions with
  | nil => trivial
  | cons expression expressions ih =>
      have headBound := bounded expression (by simp)
      have tailBound : ∀ member ∈ expressions,
          member.AtomsBelow bound := by
        intro member memberMem
        exact bounded member (by simp [memberMem])
      have negatedTail : ∀ member ∈ expressions.map TransitionExpr.not,
          member.AtomsBelow bound := by
        intro member memberMem
        obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp memberMem
        exact tailBound source sourceMem
      exact ⟨⟨headBound, all_atomsBelow negatedTail⟩,
        ⟨headBound, ih tailBound⟩⟩

theorem equal_atomsBelow {first second : TransitionExpr} {bound : Nat}
    (firstBound : first.AtomsBelow bound)
    (secondBound : second.AtomsBelow bound) :
    (equal first second).AtomsBelow bound :=
  ⟨⟨firstBound, secondBound⟩, ⟨firstBound, secondBound⟩⟩

theorem vectorsEqual_atomsBelow {first second : List Nat} {bound : Nat}
    (firstBound : AtomListBelow first bound)
    (secondBound : AtomListBelow second bound) :
    (vectorsEqual first second).AtomsBelow bound := by
  induction first generalizing second with
  | nil =>
      cases second <;> trivial
  | cons first firsts ih =>
      cases second with
      | nil => trivial
      | cons second seconds =>
          apply And.intro
          · apply equal_atomsBelow
            · exact firstBound first (by simp)
            · exact secondBound second (by simp)
          · apply ih
            · intro atom atomMem
              exact firstBound atom (by simp [atomMem])
            · intro atom atomMem
              exact secondBound atom (by simp [atomMem])

theorem currentExactlyOne_atomsBelow {atoms : List Nat} {bound : Nat}
    (bounded : AtomListBelow atoms bound) :
    (currentExactlyOne atoms).AtomsBelow bound := by
  apply exactlyOne_atomsBelow
  intro expression expressionMem
  obtain ⟨atom, atomMem, rfl⟩ := List.mem_map.mp expressionMem
  exact bounded atom atomMem

theorem binarySuccessor_atomsBelow {currentAtoms nextAtoms : List Nat}
    {bound : Nat} (currentBound : AtomListBelow currentAtoms bound)
    (nextBound : AtomListBelow nextAtoms bound) :
    (binarySuccessor currentAtoms nextAtoms).AtomsBelow bound := by
  induction currentAtoms generalizing nextAtoms with
  | nil =>
      cases nextAtoms <;> trivial
  | cons currentAtom currentAtoms ih =>
      cases nextAtoms with
      | nil => trivial
      | cons nextAtom nextAtoms =>
          have currentHead : currentAtom < bound :=
            currentBound currentAtom (by simp)
          have nextHead : nextAtom < bound :=
            nextBound nextAtom (by simp)
          have currentTail : AtomListBelow currentAtoms bound := by
            intro atom atomMem
            exact currentBound atom (by simp [atomMem])
          have nextTail : AtomListBelow nextAtoms bound := by
            intro atom atomMem
            exact nextBound atom (by simp [atomMem])
          exact ⟨
            ⟨⟨currentHead, nextHead⟩,
              vectorsEqual_atomsBelow currentTail nextTail⟩,
            ⟨⟨currentHead, nextHead⟩,
              ih currentTail nextTail⟩⟩

@[simp]
theorem all_gateCount (expressions : List TransitionExpr) :
    (all expressions).gateCount =
      (expressions.map TransitionExpr.gateCount).sum +
        expressions.length + 1 := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp [all, TransitionExpr.gateCount, ih]
      omega

@[simp]
theorem any_gateCount (expressions : List TransitionExpr) :
    (any expressions).gateCount =
      (expressions.map TransitionExpr.gateCount).sum +
        expressions.length + 1 := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp [any, TransitionExpr.gateCount, ih]
      omega

end TransitionExpr

end PeriodicCNF

end LeanTrominoes
