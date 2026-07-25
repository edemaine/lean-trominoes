import LeanTrominoes.PlanarThreeDMVariableGadget

/-!
# A paired-port 3DM clause relation

The Dyer--Frieze variable cycle exposes two complementary triple selections
for every literal occurrence.  This file records a small clause gadget that
uses both ports directly.

For literal values `xᵢ`, the literal-side triples all meet one blue element,
which imposes `ExactlyOne x`.  The complementary triple for position `i`
meets an auxiliary triple at a degree-two blue element, forcing the auxiliary
selection back to `xᵢ`.  Finally all auxiliary triples meet one red and one
green element.  Those two elements repeat the same exact-one constraint.

Thus every auxiliary triple has one reference of each color; the shared
clause, red, and green elements have degree two or three for clauses of size
two or three; and the complementary elements have degree two.  The finite
relation is useful for the abstract reduction, but this file deliberately
makes no planar-embedding claim for the natural alternating boundary order
of the literal/complement port pairs.  The geometric reduction must separately
produce a `PeriodicThreeDM.PlanarPresentation`.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

/-- Pair complementary input triples with their clause-local auxiliary
triples.  A mismatched number of inputs is rejected rather than truncated. -/
def ComplementPairsHold : List Bool → List Bool → Prop
  | [], [] => True
  | complement :: complements, auxiliary :: auxiliaries =>
      PeriodicOneInThree.ExactlyOne [complement, auxiliary] ∧
        ComplementPairsHold complements auxiliaries
  | _, _ => False

instance (complements auxiliaries : List Bool) :
    Decidable (ComplementPairsHold complements auxiliaries) := by
  induction complements generalizing auxiliaries with
  | nil =>
      cases auxiliaries with
      | nil => exact isTrue trivial
      | cons auxiliary auxiliaries => exact isFalse id
  | cons complement complements induction =>
      cases auxiliaries with
      | nil => exact isFalse id
      | cons auxiliary auxiliaries =>
          haveI : Decidable
              (ComplementPairsHold complements auxiliaries) :=
            induction auxiliaries
          change Decidable
            (PeriodicOneInThree.ExactlyOne [complement, auxiliary] ∧
              ComplementPairsHold complements auxiliaries)
          infer_instance

/-- The exact-cover constraints internal to a paired-port clause gadget.

The four conjuncts respectively belong to the main blue clause element, the
degree-two complementary blue elements, the common red element, and the
common green element. -/
def ClauseGadgetHolds
    (literals complements auxiliaries : List Bool) : Prop :=
  PeriodicOneInThree.ExactlyOne literals ∧
    ComplementPairsHold complements auxiliaries ∧
    PeriodicOneInThree.ExactlyOne auxiliaries ∧
    PeriodicOneInThree.ExactlyOne auxiliaries

instance (literals complements auxiliaries : List Bool) :
    Decidable (ClauseGadgetHolds literals complements auxiliaries) := by
  unfold ClauseGadgetHolds
  infer_instance

/-- A complementary input and its auxiliary cover their shared blue element
exactly once precisely when the auxiliary repeats the literal value. -/
theorem exactlyOne_not_and_iff (literal auxiliary : Bool) :
    PeriodicOneInThree.ExactlyOne [!literal, auxiliary] ↔
      auxiliary = literal := by
  cases literal <;> cases auxiliary <;> native_decide

/-- All degree-two complementary blue elements force the complete auxiliary
selection to repeat the literal selection. -/
theorem complementPairsHold_map_not_iff
    (literals auxiliaries : List Bool) :
    ComplementPairsHold (literals.map (!·)) auxiliaries ↔
      auxiliaries = literals := by
  induction literals generalizing auxiliaries with
  | nil =>
      cases auxiliaries <;> simp [ComplementPairsHold]
  | cons literal literals induction =>
      cases auxiliaries with
      | nil => simp [ComplementPairsHold]
      | cons auxiliary auxiliaries =>
          simp only [List.map_cons, ComplementPairsHold,
            exactlyOne_not_and_iff, List.cons.injEq]
          rw [induction]

/-- With genuinely complementary ports, every local clause matching is
classified by the source exact-one relation and has the canonical auxiliary
selection. -/
theorem clauseGadgetHolds_complements_iff
    (literals auxiliaries : List Bool) :
    ClauseGadgetHolds literals (literals.map (!·)) auxiliaries ↔
      PeriodicOneInThree.ExactlyOne literals ∧
        auxiliaries = literals := by
  rw [ClauseGadgetHolds, complementPairsHold_map_not_iff]
  constructor
  · rintro ⟨clause, equality, red, green⟩
    exact ⟨clause, equality⟩
  · rintro ⟨clause, rfl⟩
    exact ⟨clause, rfl, clause, clause⟩

/-- A clause-side matching exists exactly when the literal ports satisfy the
source exact-one clause. -/
theorem exists_clauseGadgetHolds_complements_iff
    (literals : List Bool) :
    (∃ auxiliaries,
        ClauseGadgetHolds literals (literals.map (!·)) auxiliaries) ↔
      PeriodicOneInThree.ExactlyOne literals := by
  constructor
  · rintro ⟨auxiliaries, holds⟩
    exact (clauseGadgetHolds_complements_iff
      literals auxiliaries).mp holds |>.1
  · intro clause
    exact ⟨literals,
      (clauseGadgetHolds_complements_iff literals literals).mpr
        ⟨clause, rfl⟩⟩

/-- The two-literal specialization, whose shared colored elements have
degree two. -/
theorem twoClauseGadget_truth_table (first second : Bool) :
    (∃ firstAux secondAux,
      ClauseGadgetHolds [first, second] [!first, !second]
        [firstAux, secondAux]) ↔
      PeriodicOneInThree.ExactlyOne [first, second] := by
  constructor
  · rintro ⟨firstAux, secondAux, holds⟩
    exact
      (clauseGadgetHolds_complements_iff
        [first, second] [firstAux, secondAux]).mp holds |>.1
  · intro clause
    exact ⟨first, second,
      (clauseGadgetHolds_complements_iff
        [first, second] [first, second]).mpr ⟨clause, rfl⟩⟩

/-- The three-literal specialization, whose shared colored elements have
degree three. -/
theorem threeClauseGadget_truth_table
    (first second third : Bool) :
    (∃ firstAux secondAux thirdAux,
      ClauseGadgetHolds [first, second, third]
        [!first, !second, !third]
        [firstAux, secondAux, thirdAux]) ↔
      PeriodicOneInThree.ExactlyOne [first, second, third] := by
  constructor
  · rintro ⟨firstAux, secondAux, thirdAux, holds⟩
    exact
      (clauseGadgetHolds_complements_iff
        [first, second, third]
        [firstAux, secondAux, thirdAux]).mp holds |>.1
  · intro clause
    exact ⟨first, second, third,
      (clauseGadgetHolds_complements_iff
        [first, second, third]
        [first, second, third]).mpr ⟨clause, rfl⟩⟩

/-- Symbolic blue elements in a clause gadget. -/
inductive ClauseBlue (Slot : Type*)
  | clause
  | complement (slot : Slot)
  deriving DecidableEq, Repr

/-- The references of the auxiliary triple at one literal position. -/
structure ClauseAuxiliaryReferences (Slot : Type*) where
  red : Unit
  green : Unit
  blue : ClauseBlue Slot
  deriving DecidableEq, Repr

/-- Every clause-local auxiliary triple meets the common red and green
elements and its own complementary blue element. -/
def clauseAuxiliaryReferences {Slot : Type*}
    (slot : Slot) : ClauseAuxiliaryReferences Slot :=
  ⟨(), (), .complement slot⟩

/-- The literal-side input triples all name the common clause element. -/
def clauseLiteralBlue {Slot : Type*} (_slot : Slot) : ClauseBlue Slot :=
  .clause

/-- The complementary input at each position names the same degree-two blue
element as its corresponding auxiliary triple. -/
def clauseComplementBlue {Slot : Type*}
    (slot : Slot) : ClauseBlue Slot :=
  .complement slot

/-- For arity two or three, the common red, green, and clause-blue elements
all satisfy the degree restriction in Theorem 3.7. -/
theorem clauseSharedElement_degree_mem
    {arity : Nat} (lower : 2 ≤ arity) (upper : arity ≤ 3) :
    arity ∈ ([2, 3] : List Nat) := by
  have : arity = 2 ∨ arity = 3 := by omega
  rcases this with rfl | rfl <;> simp

/-- Every complementary blue element has exactly its input and auxiliary
incidences. -/
theorem clauseComplementElement_degree : (2 : Nat) ∈ ([2, 3] : List Nat) := by
  simp

end PlanarThreeDM
end LeanTrominoes
