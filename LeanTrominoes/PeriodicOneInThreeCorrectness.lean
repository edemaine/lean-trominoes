/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThree

/-!
# Correctness of the periodic 1-in-3SAT reduction

The auxiliary values choose the first true literal of each source clause.
Padding variables are always false.  This gives a canonical extension of any
source assignment; conversely, the finite gadget truth table recovers a true
source literal from any exact-one solution.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

/-- The Boolean truth value of one source literal at one translate. -/
def literalTruth {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (literal : PeriodicLiteral Variable) : Bool :=
  assignment literal.atom (Cell.add translate literal.offset) ==
    literal.value

@[simp]
theorem literalTruth_eq_true_iff {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (literal : PeriodicLiteral Variable) :
    literalTruth assignment translate literal = true ↔
      literal.Holds assignment translate := by
  simp [literalTruth, PeriodicLiteral.Holds]

/-- The three truth values supplied to a padded clause gadget. -/
structure ClauseBits where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

/-- At least one of the three padded source positions is true. -/
def ClauseBits.AnyTrue (bits : ClauseBits) : Prop :=
  bits.first = true ∨ bits.second = true ∨ bits.third = true

instance (bits : ClauseBits) : Decidable bits.AnyTrue := by
  unfold ClauseBits.AnyTrue
  infer_instance

/-- Read the first three source-literal truth values, padding by false. -/
def clauseBits {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell) :
    PeriodicClause Variable → ClauseBits
  | [] => ⟨false, false, false⟩
  | [first] =>
      ⟨literalTruth assignment translate first, false, false⟩
  | [first, second] =>
      ⟨literalTruth assignment translate first,
        literalTruth assignment translate second, false⟩
  | first :: second :: third :: _ =>
      ⟨literalTruth assignment translate first,
        literalTruth assignment translate second,
        literalTruth assignment translate third⟩

/-- The first selectable literal is chosen whenever the first source literal
is false and the second is true. -/
def canonicalFirstChoice (bits : ClauseBits) : Bool :=
  !bits.first && bits.second

/-- The second selectable literal is chosen exactly when the first two source
literals are false and the third is true. -/
def canonicalSecondChoice (bits : ClauseBits) : Bool :=
  !bits.first && !bits.second && bits.third

/-- Slack completes the second exact-one clause. -/
def canonicalFirstSlack (bits : ClauseBits) : Bool :=
  bits.second && !canonicalFirstChoice bits

/-- Slack completes the third exact-one clause. -/
def canonicalSecondSlack (bits : ClauseBits) : Bool :=
  bits.third && !canonicalSecondChoice bits

/-- Canonical value of every auxiliary variable. -/
def auxiliaryValue (kind : OneInThreeAux) (bits : ClauseBits) : Bool :=
  match kind with
  | .firstChoice => canonicalFirstChoice bits
  | .secondChoice => canonicalSecondChoice bits
  | .firstSlack => canonicalFirstSlack bits
  | .secondSlack => canonicalSecondSlack bits
  | .firstPadding | .secondPadding | .thirdPadding => false

/-- Whenever the source disjunction is true, the canonical auxiliary values
satisfy all three exact-one clauses. -/
theorem canonical_disjunctionGadgetHolds {bits : ClauseBits}
    (anyTrue : bits.AnyTrue) :
    DisjunctionGadgetHolds bits.first bits.second bits.third
      (auxiliaryValue .firstChoice bits)
      (auxiliaryValue .secondChoice bits)
      (auxiliaryValue .firstSlack bits)
      (auxiliaryValue .secondSlack bits) := by
  rcases bits with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third <;>
    simp_all [ClauseBits.AnyTrue, auxiliaryValue,
      canonicalFirstChoice, canonicalSecondChoice,
      canonicalFirstSlack, canonicalSecondSlack,
      DisjunctionGadgetHolds, ExactlyOne]

/-- Width-at-most-three source-clause truth is exactly truth of one padded
position. -/
theorem sourceClause_holds_iff_clauseBits_anyTrue {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (source : PeriodicClause Variable) (width : source.WidthAtMost 3) :
    source.Holds assignment translate ↔
      (clauseBits assignment translate source).AnyTrue := by
  rcases source with _ | ⟨first, rest⟩
  · simp [PeriodicClause.Holds, clauseBits, ClauseBits.AnyTrue]
  · rcases rest with _ | ⟨second, rest⟩
    · simp [PeriodicClause.Holds, clauseBits, ClauseBits.AnyTrue,
        literalTruth_eq_true_iff]
    · rcases rest with _ | ⟨third, rest⟩
      · simp [PeriodicClause.Holds, clauseBits, ClauseBits.AnyTrue,
          literalTruth_eq_true_iff]
      · rcases rest with _ | ⟨fourth, rest⟩
        · simp [PeriodicClause.Holds, clauseBits, ClauseBits.AnyTrue,
            literalTruth_eq_true_iff]
        · simp [PeriodicClause.WidthAtMost] at width

/-- Coordinate subtraction cancels the anchor added by an auxiliary literal. -/
@[simp]
theorem sub_add_right (translate offset : Cell) :
    Cell.sub (Cell.add translate offset) offset = translate := by
  rcases translate with ⟨translateX, translateY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [Cell.sub, Cell.add]

/-- Extend a source assignment by evaluating each clause gadget independently
at the translate named by the auxiliary variable's cell. -/
def extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    OneInThreeVariable Variable → Cell → Bool
  | Sum.inl atom, cell => assignment atom cell
  | Sum.inr ((_, source), kind), cell =>
      auxiliaryValue kind
        (clauseBits assignment (Cell.sub cell (anchor source)) source)

@[simp]
theorem extendAssignment_original {Variable : Type*}
    (assignment : Variable → Cell → Bool) (atom : Variable) (cell : Cell) :
    extendAssignment assignment (Sum.inl atom) cell =
      assignment atom cell := rfl

@[simp]
theorem extendAssignment_auxiliary {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    extendAssignment assignment
        (Sum.inr ((clauseIndex, source), kind))
        (Cell.add translate (anchor source)) =
      auxiliaryValue kind (clauseBits assignment translate source) := by
  simp [extendAssignment]

/-- Restrict an exact-one assignment to the embedded source variables. -/
def restrictAssignment {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell => assignment (Sum.inl atom) cell

@[simp]
theorem literalTruth_liftLiteral_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (literal : PeriodicLiteral Variable) :
    literalTruth (extendAssignment assignment) translate
        (liftLiteral literal) =
      literalTruth assignment translate literal := by
  rfl

@[simp]
theorem literalTruth_negate {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (literal : PeriodicLiteral Variable) :
    literalTruth assignment translate (negate literal) =
      !literalTruth assignment translate literal := by
  unfold literalTruth negate
  cases assignment literal.atom (Cell.add translate literal.offset) <;>
    cases literal.value <;> rfl

@[simp]
theorem literalTruth_auxiliary_true_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    literalTruth (extendAssignment assignment) translate
        (auxiliary clauseIndex source kind true) =
      auxiliaryValue kind (clauseBits assignment translate source) := by
  simp [literalTruth, auxiliary]

@[simp]
theorem literalTruth_auxiliary_false_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    literalTruth (extendAssignment assignment) translate
        (auxiliary clauseIndex source kind false) =
      !auxiliaryValue kind (clauseBits assignment translate source) := by
  simp [literalTruth, auxiliary]

theorem clauseHolds_iff_exactlyOne_literalTruth {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clause : PeriodicClause Variable) :
    ClauseHolds assignment translate clause ↔
      ExactlyOne (clause.map (literalTruth assignment translate)) := by
  rfl

/-- The canonical extension satisfies the three core exact-one clauses,
provided the supplied literals realize the padded source truth values. -/
theorem disjunctionGadget_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (first second third :
      PeriodicLiteral (OneInThreeVariable Variable))
    (firstTruth :
      literalTruth (extendAssignment assignment) translate first =
        (clauseBits assignment translate source).first)
    (secondTruth :
      literalTruth (extendAssignment assignment) translate second =
        (clauseBits assignment translate source).second)
    (thirdTruth :
      literalTruth (extendAssignment assignment) translate third =
        (clauseBits assignment translate source).third)
    (anyTrue : (clauseBits assignment translate source).AnyTrue) :
    ∀ clause ∈ disjunctionGadget clauseIndex source first second third,
      ClauseHolds (extendAssignment assignment) translate clause := by
  have gadget :=
    canonical_disjunctionGadgetHolds anyTrue
  intro clause clauseMem
  simp only [disjunctionGadget, List.mem_cons, List.not_mem_nil,
    or_false] at clauseMem
  rcases clauseMem with rfl | rfl | rfl
  · rw [clauseHolds_iff_exactlyOne_literalTruth]
    simp only [List.map_cons, List.map_nil, firstTruth,
      literalTruth_auxiliary_true_extend]
    exact gadget.1
  · rw [clauseHolds_iff_exactlyOne_literalTruth]
    simp only [List.map_cons, List.map_nil, literalTruth_negate,
      secondTruth, literalTruth_auxiliary_true_extend]
    exact gadget.2.1
  · rw [clauseHolds_iff_exactlyOne_literalTruth]
    simp only [List.map_cons, List.map_nil, literalTruth_negate,
      thirdTruth, literalTruth_auxiliary_true_extend]
    exact gadget.2.2

/-- The canonical extension satisfies every exact-one clause generated from
one satisfied width-at-most-three source clause. -/
theorem clauseClauses_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (width : source.WidthAtMost 3)
    (sourceHolds : source.Holds assignment translate) :
    ∀ clause ∈ clauseClauses clauseIndex source,
      ClauseHolds (extendAssignment assignment) translate clause := by
  have anyTrue :=
    (sourceClause_holds_iff_clauseBits_anyTrue
      assignment translate source width).1 sourceHolds
  rcases source with _ | ⟨first, rest⟩
  · intro clause clauseMem
    simp only [clauseClauses, List.mem_append] at clauseMem
    rcases clauseMem with gadgetMem | paddingMem
    · exact disjunctionGadget_complete assignment translate
        clauseIndex []
        (padding clauseIndex [] .firstPadding)
        (padding clauseIndex [] .secondPadding)
        (padding clauseIndex [] .thirdPadding)
        (by simp [padding, clauseBits, auxiliaryValue])
        (by simp [padding, clauseBits, auxiliaryValue])
        (by simp [padding, clauseBits, auxiliaryValue])
        anyTrue clause gadgetMem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at paddingMem
      rcases paddingMem with rfl | rfl | rfl <;>
        rw [clauseHolds_iff_exactlyOne_literalTruth] <;>
        simp [forcePaddingFalse, auxiliaryValue, ExactlyOne]
  · rcases rest with _ | ⟨second, rest⟩
    · intro clause clauseMem
      simp only [clauseClauses, List.mem_append] at clauseMem
      rcases clauseMem with gadgetMem | paddingMem
      · exact disjunctionGadget_complete assignment translate
          clauseIndex [first]
          (liftLiteral first)
          (padding clauseIndex [first] .secondPadding)
          (padding clauseIndex [first] .thirdPadding)
          (by simp [clauseBits])
          (by simp [padding, clauseBits, auxiliaryValue])
          (by simp [padding, clauseBits, auxiliaryValue])
          anyTrue clause gadgetMem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at paddingMem
        rcases paddingMem with rfl | rfl <;>
          rw [clauseHolds_iff_exactlyOne_literalTruth] <;>
          simp [forcePaddingFalse, auxiliaryValue, ExactlyOne]
    · rcases rest with _ | ⟨third, rest⟩
      · intro clause clauseMem
        simp only [clauseClauses, List.mem_append] at clauseMem
        rcases clauseMem with gadgetMem | paddingMem
        · exact disjunctionGadget_complete assignment translate
            clauseIndex [first, second]
            (liftLiteral first) (liftLiteral second)
            (padding clauseIndex [first, second] .thirdPadding)
            (by simp [clauseBits])
            (by simp [clauseBits])
            (by simp [padding, clauseBits, auxiliaryValue])
            anyTrue clause gadgetMem
        · simp only [List.mem_singleton] at paddingMem
          subst clause
          rw [clauseHolds_iff_exactlyOne_literalTruth]
          simp [forcePaddingFalse, auxiliaryValue, ExactlyOne]
      · rcases rest with _ | ⟨fourth, rest⟩
        · exact disjunctionGadget_complete assignment translate
            clauseIndex [first, second, third]
            (liftLiteral first) (liftLiteral second) (liftLiteral third)
            (by simp [clauseBits]) (by simp [clauseBits])
            (by simp [clauseBits]) anyTrue
        · simp [PeriodicClause.WidthAtMost] at width

@[simp]
theorem literalTruth_liftLiteral_restrict {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Cell → Bool)
    (translate : Cell) (literal : PeriodicLiteral Variable) :
    literalTruth assignment translate (liftLiteral literal) =
      literalTruth (restrictAssignment assignment) translate literal := by
  rfl

/-- Satisfaction of the three generated clauses exposes a true supplied
literal, independently of how the auxiliary variables were assigned. -/
theorem disjunctionGadget_sound {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (first second third :
      PeriodicLiteral (OneInThreeVariable Variable))
    (satisfies :
      ∀ clause ∈ disjunctionGadget clauseIndex source first second third,
        ClauseHolds assignment translate clause) :
    literalTruth assignment translate first = true ∨
      literalTruth assignment translate second = true ∨
      literalTruth assignment translate third = true := by
  let firstChoice :=
    literalTruth assignment translate
      (auxiliary clauseIndex source .firstChoice true)
  let secondChoice :=
    literalTruth assignment translate
      (auxiliary clauseIndex source .secondChoice true)
  let firstSlack :=
    literalTruth assignment translate
      (auxiliary clauseIndex source .firstSlack true)
  let secondSlack :=
    literalTruth assignment translate
      (auxiliary clauseIndex source .secondSlack true)
  have firstClause := satisfies
    [first,
      auxiliary clauseIndex source .firstChoice true,
      auxiliary clauseIndex source .secondChoice true] (by
        simp [disjunctionGadget])
  have secondClause := satisfies
    [negate second,
      auxiliary clauseIndex source .firstChoice true,
      auxiliary clauseIndex source .firstSlack true] (by
        simp [disjunctionGadget])
  have thirdClause := satisfies
    [negate third,
      auxiliary clauseIndex source .secondChoice true,
      auxiliary clauseIndex source .secondSlack true] (by
        simp [disjunctionGadget])
  have gadget :
      DisjunctionGadgetHolds
        (literalTruth assignment translate first)
        (literalTruth assignment translate second)
        (literalTruth assignment translate third)
        firstChoice secondChoice firstSlack secondSlack := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [clauseHolds_iff_exactlyOne_literalTruth,
        firstChoice, secondChoice] using firstClause
    · simpa [clauseHolds_iff_exactlyOne_literalTruth,
        firstChoice, firstSlack] using secondClause
    · simpa [clauseHolds_iff_exactlyOne_literalTruth,
        secondChoice, secondSlack] using thirdClause
  exact (exists_disjunctionGadgetHolds_iff
    (literalTruth assignment translate first)
    (literalTruth assignment translate second)
    (literalTruth assignment translate third)).1
      ⟨firstChoice, secondChoice, firstSlack, secondSlack, gadget⟩

/-- A satisfied negative unit padding clause forces its corresponding positive
padding literal to be false. -/
theorem forcePaddingFalse_sound {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (source : PeriodicClause Variable) (kind : OneInThreeAux)
    (holds :
      ClauseHolds assignment translate
        (forcePaddingFalse clauseIndex source kind)) :
    literalTruth assignment translate
      (padding clauseIndex source kind) = false := by
  rw [clauseHolds_iff_exactlyOne_literalTruth] at holds
  simp only [forcePaddingFalse, List.map_cons, List.map_nil] at holds
  unfold ExactlyOne at holds
  have negativeTrue :
      literalTruth assignment translate
        (auxiliary clauseIndex source kind false) = true := by
    cases truthEq :
        literalTruth assignment translate
          (auxiliary clauseIndex source kind false) with
    | false => simp [truthEq] at holds
    | true => rfl
  simpa [literalTruth, padding, auxiliary] using negativeTrue

/-- Any exact-one assignment satisfying the generated clauses restricts to a
satisfying assignment of the source clause. -/
theorem clauseClauses_sound {Variable : Type*}
    (assignment : OneInThreeVariable Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (source : PeriodicClause Variable) (width : source.WidthAtMost 3)
    (satisfies :
      ∀ clause ∈ clauseClauses clauseIndex source,
        ClauseHolds assignment translate clause) :
    source.Holds (restrictAssignment assignment) translate := by
  apply (sourceClause_holds_iff_clauseBits_anyTrue
    (restrictAssignment assignment) translate source width).2
  rcases source with _ | ⟨first, rest⟩
  · have gadgetAny := disjunctionGadget_sound assignment translate
      clauseIndex []
      (padding clauseIndex [] .firstPadding)
      (padding clauseIndex [] .secondPadding)
      (padding clauseIndex [] .thirdPadding)
      (fun clause clauseMem =>
        satisfies clause (by
          simp only [clauseClauses, List.mem_append]
          exact Or.inl clauseMem))
    have firstFalse := forcePaddingFalse_sound assignment translate
      clauseIndex [] .firstPadding
      (satisfies
        (forcePaddingFalse clauseIndex [] .firstPadding) (by
          simp [clauseClauses]))
    have secondFalse := forcePaddingFalse_sound assignment translate
      clauseIndex [] .secondPadding
      (satisfies
        (forcePaddingFalse clauseIndex [] .secondPadding) (by
          simp [clauseClauses]))
    have thirdFalse := forcePaddingFalse_sound assignment translate
      clauseIndex [] .thirdPadding
      (satisfies
        (forcePaddingFalse clauseIndex [] .thirdPadding) (by
          simp [clauseClauses]))
    rcases gadgetAny with firstTrue | secondTrue | thirdTrue
    · rw [firstFalse] at firstTrue
      contradiction
    · rw [secondFalse] at secondTrue
      contradiction
    · rw [thirdFalse] at thirdTrue
      contradiction
  · rcases rest with _ | ⟨second, rest⟩
    · have gadgetAny := disjunctionGadget_sound assignment translate
        clauseIndex [first]
        (liftLiteral first)
        (padding clauseIndex [first] .secondPadding)
        (padding clauseIndex [first] .thirdPadding)
        (fun clause clauseMem =>
          satisfies clause (by
            simp only [clauseClauses, List.mem_append]
            exact Or.inl clauseMem))
      have secondFalse := forcePaddingFalse_sound assignment translate
        clauseIndex [first] .secondPadding
        (satisfies
          (forcePaddingFalse clauseIndex [first] .secondPadding) (by
            simp [clauseClauses]))
      have thirdFalse := forcePaddingFalse_sound assignment translate
        clauseIndex [first] .thirdPadding
        (satisfies
          (forcePaddingFalse clauseIndex [first] .thirdPadding) (by
            simp [clauseClauses]))
      simp only [clauseBits, ClauseBits.AnyTrue, Bool.false_eq_true,
        or_false]
      rcases gadgetAny with firstTrue | secondTrue | thirdTrue
      · simpa using firstTrue
      · rw [secondFalse] at secondTrue
        contradiction
      · rw [thirdFalse] at thirdTrue
        contradiction
    · rcases rest with _ | ⟨third, rest⟩
      · have gadgetAny := disjunctionGadget_sound assignment translate
          clauseIndex [first, second]
          (liftLiteral first) (liftLiteral second)
          (padding clauseIndex [first, second] .thirdPadding)
          (fun clause clauseMem =>
            satisfies clause (by
              simp only [clauseClauses, List.mem_append]
              exact Or.inl clauseMem))
        have thirdFalse := forcePaddingFalse_sound assignment translate
          clauseIndex [first, second] .thirdPadding
          (satisfies
            (forcePaddingFalse clauseIndex [first, second]
              .thirdPadding) (by
                simp [clauseClauses]))
        simp only [clauseBits, ClauseBits.AnyTrue, Bool.false_eq_true,
          or_false]
        rcases gadgetAny with firstTrue | secondTrue | thirdTrue
        · exact Or.inl (by simpa using firstTrue)
        · exact Or.inr (by simpa using secondTrue)
        · rw [thirdFalse] at thirdTrue
          contradiction
      · rcases rest with _ | ⟨fourth, rest⟩
        · have gadgetAny := disjunctionGadget_sound assignment translate
            clauseIndex [first, second, third]
            (liftLiteral first) (liftLiteral second) (liftLiteral third)
            (fun clause clauseMem =>
              satisfies clause (by
                simpa [clauseClauses] using clauseMem))
          simpa only [clauseBits, ClauseBits.AnyTrue,
            literalTruth_liftLiteral_restrict] using gadgetAny
        · simp [PeriodicClause.WidthAtMost] at width

/-- A satisfying source assignment extends to a satisfying exact-one
assignment for the complete periodic formula. -/
theorem formula_satisfies_of_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable) (width : source.WidthAtMost 3)
    (assignment : Variable → Cell → Bool)
    (satisfies : source.Satisfies assignment) :
    Satisfies (formula source) (extendAssignment assignment) := by
  intro translate clause clauseMem
  simp only [formula, List.mem_flatMap] at clauseMem
  rcases clauseMem with ⟨tagged, taggedMem, clauseMem⟩
  exact clauseClauses_complete assignment translate tagged.2 tagged.1
    (width tagged.1 (List.fst_mem_of_mem_zipIdx taggedMem))
    (satisfies translate tagged.1
      (List.fst_mem_of_mem_zipIdx taggedMem))
    clause clauseMem

/-- Any satisfying exact-one assignment restricts to a satisfying assignment
for the complete source formula. -/
theorem satisfies_of_formula_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable) (width : source.WidthAtMost 3)
    (assignment : OneInThreeVariable Variable → Cell → Bool)
    (satisfies : Satisfies (formula source) assignment) :
    source.Satisfies (restrictAssignment assignment) := by
  intro translate clause clauseMem
  have mappedMem :
      clause ∈ source.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clauseMem
  rcases List.mem_map.mp mappedMem with
    ⟨⟨taggedClause, clauseIndex⟩, taggedMem, taggedEq⟩
  simp only at taggedEq
  subst taggedClause
  apply clauseClauses_sound assignment translate clauseIndex clause
    (width clause clauseMem)
  intro generated generatedMem
  apply satisfies translate generated
  simp only [formula, List.mem_flatMap]
  exact ⟨(clause, clauseIndex), taggedMem, generatedMem⟩

/-- The periodic reduction from width-three SAT to exact-one SAT preserves
satisfiability exactly. -/
theorem satisfiable_iff {Variable : Type*}
    (source : PeriodicCNF Variable) (width : source.WidthAtMost 3) :
    source.Satisfiable ↔ Satisfiable (formula source) := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨extendAssignment assignment,
      formula_satisfies_of_satisfies source width assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨restrictAssignment assignment,
      satisfies_of_formula_satisfies source width assignment satisfies⟩

end PeriodicOneInThree
end LeanTrominoes
