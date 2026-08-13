/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThree
import Mathlib.Data.List.Count

/-!
# Reduction from periodic 3SAT to periodic 1-in-3SAT

This file formalizes the clause gadget in Figure 7 of the paper.  A clause
`x ∨ y ∨ z` is replaced by three exact-one clauses

* `x + y' + z' = 1`,
* `¬y + y' + a = 1`, and
* `¬z + z' + b = 1`.

Existential choices of `y'`, `z'`, `a`, and `b` exist exactly when the
original disjunction is true.  Short source clauses are padded by fresh
variables that are forced false by unit exact-one clauses.
-/

namespace LeanTrominoes

/-- Auxiliary variables used by one clause gadget. -/
inductive OneInThreeAux
  | firstChoice
  | secondChoice
  | firstSlack
  | secondSlack
  | firstPadding
  | secondPadding
  | thirdPadding
  deriving DecidableEq, Repr, Fintype

/-- Original variables or clause-positioned auxiliaries. -/
abbrev OneInThreeVariable (Variable : Type*) :=
  Sum Variable
    ((Nat × PeriodicClause Variable) × OneInThreeAux)

namespace PeriodicOneInThree

/-- Exactly one Boolean in a finite list is true. -/
def ExactlyOne (values : List Bool) : Prop :=
  values.count true = 1

instance (values : List Bool) : Decidable (ExactlyOne values) := by
  unfold ExactlyOne
  infer_instance

/-- The truth values contributed by a periodic clause at one translate. -/
def clauseValues {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clause : PeriodicClause Variable) : List Bool :=
  clause.map fun literal =>
    assignment literal.atom (Cell.add translate literal.offset) ==
      literal.value

/-- A clause holds in the 1-in-3 sense when exactly one literal occurrence
is true. -/
def ClauseHolds {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clause : PeriodicClause Variable) : Prop :=
  ExactlyOne (clauseValues assignment translate clause)

/-- An assignment satisfies every exact-one clause at every translate. -/
def Satisfies {Variable : Type*} (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) : Prop :=
  ∀ translate clause, clause ∈ formula.clauses →
    ClauseHolds assignment translate clause

/-- A periodic exact-one formula has some plane-wide satisfying assignment. -/
def Satisfiable {Variable : Type*} (formula : PeriodicCNF Variable) : Prop :=
  ∃ assignment : Variable → Cell → Bool, Satisfies formula assignment

/-- Negate a periodic literal without changing its atom or offset. -/
def negate {Variable : Type*} (literal : PeriodicLiteral Variable) :
    PeriodicLiteral Variable :=
  ⟨literal.atom, literal.offset, !literal.value⟩

/-- Embed a source literal into the enlarged variable type. -/
def liftLiteral {Variable : Type*} (literal : PeriodicLiteral Variable) :
    PeriodicLiteral (OneInThreeVariable Variable) :=
  ⟨Sum.inl literal.atom, literal.offset, literal.value⟩

/-- The first source offset, or the origin for an empty source clause. -/
def anchor {Variable : Type*} (clause : PeriodicClause Variable) : Cell :=
  (clause.head?.map PeriodicLiteral.offset).getD (0, 0)

/-- A positive or negative auxiliary literal, anchored to its source clause. -/
def auxiliary {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (kind : OneInThreeAux)
    (value : Bool) :
    PeriodicLiteral (OneInThreeVariable Variable) :=
  ⟨Sum.inr ((clauseIndex, source), kind), anchor source, value⟩

/-- The three exact-one clauses implementing one three-literal disjunction. -/
def disjunctionGadget {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (first second third :
      PeriodicLiteral (OneInThreeVariable Variable)) :
    List (PeriodicClause (OneInThreeVariable Variable)) :=
  [[first,
      auxiliary clauseIndex source .firstChoice true,
      auxiliary clauseIndex source .secondChoice true],
    [negate second,
      auxiliary clauseIndex source .firstChoice true,
      auxiliary clauseIndex source .firstSlack true],
    [negate third,
      auxiliary clauseIndex source .secondChoice true,
      auxiliary clauseIndex source .secondSlack true]]

/-- A fresh positive padding literal. -/
def padding {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (kind : OneInThreeAux) :
    PeriodicLiteral (OneInThreeVariable Variable) :=
  auxiliary clauseIndex source kind true

/-- Force a padding variable to false by requiring its negative unit literal
to be the unique true literal. -/
def forcePaddingFalse {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (kind : OneInThreeAux) :
    PeriodicClause (OneInThreeVariable Variable) :=
  [auxiliary clauseIndex source kind false]

/-- Replace one width-at-most-three disjunction by exact-one clauses.
Longer clauses are truncated; correctness is stated under the source width
bound used by the reduction. -/
def clauseClauses {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) :
    List (PeriodicClause (OneInThreeVariable Variable)) :=
  match source with
  | [] =>
      disjunctionGadget clauseIndex source
          (padding clauseIndex source .firstPadding)
          (padding clauseIndex source .secondPadding)
          (padding clauseIndex source .thirdPadding) ++
        [forcePaddingFalse clauseIndex source .firstPadding,
          forcePaddingFalse clauseIndex source .secondPadding,
          forcePaddingFalse clauseIndex source .thirdPadding]
  | [first] =>
      disjunctionGadget clauseIndex source
          (liftLiteral first)
          (padding clauseIndex source .secondPadding)
          (padding clauseIndex source .thirdPadding) ++
        [forcePaddingFalse clauseIndex source .secondPadding,
          forcePaddingFalse clauseIndex source .thirdPadding]
  | [first, second] =>
      disjunctionGadget clauseIndex source
          (liftLiteral first) (liftLiteral second)
          (padding clauseIndex source .thirdPadding) ++
        [forcePaddingFalse clauseIndex source .thirdPadding]
  | first :: second :: third :: _ =>
      disjunctionGadget clauseIndex source
        (liftLiteral first) (liftLiteral second) (liftLiteral third)

/-- Apply the exact-one clause gadget at every source-clause position. -/
def formula {Variable : Type*} (source : PeriodicCNF Variable) :
    PeriodicCNF (OneInThreeVariable Variable) where
  clauses := source.clauses.zipIdx.flatMap fun (clause, clauseIndex) =>
    clauseClauses clauseIndex clause

/-- Boolean semantics of the three exact-one clauses in the core gadget. -/
def DisjunctionGadgetHolds
    (first second third firstChoice secondChoice
      firstSlack secondSlack : Bool) : Prop :=
  ExactlyOne [first, firstChoice, secondChoice] ∧
    ExactlyOne [!second, firstChoice, firstSlack] ∧
    ExactlyOne [!third, secondChoice, secondSlack]

instance (first second third firstChoice secondChoice
    firstSlack secondSlack : Bool) :
    Decidable (DisjunctionGadgetHolds first second third
      firstChoice secondChoice firstSlack secondSlack) := by
  unfold DisjunctionGadgetHolds
  infer_instance

/-- The finite truth table underlying Figure 7. -/
theorem exists_disjunctionGadgetHolds_iff
    (first second third : Bool) :
    (∃ firstChoice secondChoice firstSlack secondSlack,
      DisjunctionGadgetHolds first second third
        firstChoice secondChoice firstSlack secondSlack) ↔
      first = true ∨ second = true ∨ third = true := by
  cases first <;> cases second <;> cases third <;>
    simp only [Bool.exists_bool] <;> decide

@[simp]
theorem negate_atom {Variable : Type*}
    (literal : PeriodicLiteral Variable) :
    (negate literal).atom = literal.atom := rfl

@[simp]
theorem negate_offset {Variable : Type*}
    (literal : PeriodicLiteral Variable) :
    (negate literal).offset = literal.offset := rfl

@[simp]
theorem negate_value {Variable : Type*}
    (literal : PeriodicLiteral Variable) :
    (negate literal).value = !literal.value := rfl

@[simp]
theorem negate_holds_iff {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (literal : PeriodicLiteral Variable) :
    (negate literal).Holds assignment translate ↔
      ¬literal.Holds assignment translate := by
  change
    (assignment literal.atom (Cell.add translate literal.offset) =
        !literal.value ↔
      ¬assignment literal.atom (Cell.add translate literal.offset) =
        literal.value)
  cases assignment literal.atom (Cell.add translate literal.offset) <;>
    cases literal.value <;> simp

theorem liftLiteral_offsetDistance {Variable : Type*}
    (first second : PeriodicLiteral Variable) :
    PeriodicClause.offsetDistance
        (liftLiteral first) (liftLiteral second) =
      PeriodicClause.offsetDistance first second := by
  rfl

theorem anchor_offsetDistance_le_one {Variable : Type*}
    {source : PeriodicClause Variable} (sourceLocal : source.IsLocal)
    {literal : PeriodicLiteral Variable} (literalMem : literal ∈ source) :
    (literal.offset.1 - (anchor source).1).natAbs +
        (literal.offset.2 - (anchor source).2).natAbs ≤ 1 := by
  cases source with
  | nil => simp at literalMem
  | cons first rest =>
      exact sourceLocal literal literalMem first (by simp)

/-- Every generated literal is placed either at a source-literal offset or at
the source clause's anchor. -/
def Supported {Variable : Type*} (source : PeriodicClause Variable)
    (literal : PeriodicLiteral (OneInThreeVariable Variable)) : Prop :=
  (∃ original ∈ source, literal.offset = original.offset) ∨
    literal.offset = anchor source

theorem supported_offsetDistance_le_one {Variable : Type*}
    {source : PeriodicClause Variable} (sourceLocal : source.IsLocal)
    {first second : PeriodicLiteral (OneInThreeVariable Variable)}
    (firstSupported : Supported source first)
    (secondSupported : Supported source second) :
    PeriodicClause.offsetDistance first second ≤ 1 := by
  rcases firstSupported with
      ⟨originalFirst, firstMem, firstOffset⟩ | firstOffset <;>
    rcases secondSupported with
      ⟨originalSecond, secondMem, secondOffset⟩ | secondOffset
  · simpa [PeriodicClause.offsetDistance, firstOffset, secondOffset] using
      sourceLocal originalFirst firstMem originalSecond secondMem
  · cases source with
    | nil => simp at firstMem
    | cons anchorLiteral rest =>
        simpa [PeriodicClause.offsetDistance, anchor, firstOffset,
          secondOffset] using
          sourceLocal originalFirst firstMem anchorLiteral (by simp)
  · cases source with
    | nil => simp at secondMem
    | cons anchorLiteral rest =>
        simpa [PeriodicClause.offsetDistance, anchor, firstOffset,
          secondOffset] using
          sourceLocal anchorLiteral (by simp) originalSecond secondMem
  · simp [PeriodicClause.offsetDistance, firstOffset, secondOffset]

theorem clauseClauses_supported {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    ∀ clause ∈ clauseClauses clauseIndex source,
      ∀ literal ∈ clause, Supported source literal := by
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseClauses, disjunctionGadget, forcePaddingFalse,
      padding, auxiliary, Supported]
  · rcases rest with _ | ⟨second, rest⟩
    · simp [clauseClauses, disjunctionGadget, forcePaddingFalse,
        padding, auxiliary, liftLiteral, negate, Supported]
    · rcases rest with _ | ⟨third, rest⟩
      · simp [clauseClauses, disjunctionGadget, forcePaddingFalse,
          padding, auxiliary, liftLiteral, negate, Supported]
      · simp [clauseClauses, disjunctionGadget, auxiliary,
          liftLiteral, negate, Supported]

/-- The clause gadget preserves the paper's locality condition. -/
theorem clauseClauses_areLocal {Variable : Type*}
    (clauseIndex : Nat) {source : PeriodicClause Variable}
    (sourceLocal : source.IsLocal) :
    ∀ clause ∈ clauseClauses clauseIndex source, clause.IsLocal := by
  intro clause clauseMem first firstMem second secondMem
  exact supported_offsetDistance_le_one sourceLocal
    (clauseClauses_supported clauseIndex source clause clauseMem
      first firstMem)
    (clauseClauses_supported clauseIndex source clause clauseMem
      second secondMem)

/-- Every generated exact-one clause has width at most three. -/
theorem clauseClauses_widthAtMostThree {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    ∀ clause ∈ clauseClauses clauseIndex source,
      clause.WidthAtMost 3 := by
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseClauses, disjunctionGadget, forcePaddingFalse,
      PeriodicClause.WidthAtMost]
  · rcases rest with _ | ⟨second, rest⟩
    · simp [clauseClauses, disjunctionGadget, forcePaddingFalse,
        PeriodicClause.WidthAtMost]
    · rcases rest with _ | ⟨third, rest⟩
      · simp [clauseClauses, disjunctionGadget, forcePaddingFalse,
          PeriodicClause.WidthAtMost]
      · simp [clauseClauses, disjunctionGadget,
          PeriodicClause.WidthAtMost]

/-- The complete exact-one formula has width at most three. -/
theorem formula_widthAtMostThree {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (formula source).WidthAtMost 3 := by
  intro clause clauseMem
  simp only [formula, List.mem_flatMap] at clauseMem
  rcases clauseMem with ⟨tagged, taggedMem, clauseMem⟩
  exact clauseClauses_widthAtMostThree tagged.2 tagged.1 clause clauseMem

/-- The complete exact-one reduction preserves locality. -/
theorem formula_isLocal {Variable : Type*}
    {source : PeriodicCNF Variable} (sourceLocal : source.IsLocal) :
    (formula source).IsLocal := by
  intro clause clauseMem
  simp only [formula, List.mem_flatMap] at clauseMem
  rcases clauseMem with ⟨tagged, taggedMem, clauseMem⟩
  exact clauseClauses_areLocal tagged.2
    (sourceLocal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMem))
    clause clauseMem

end PeriodicOneInThree
end LeanTrominoes
