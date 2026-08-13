/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Anchor normalization of positioned periodic clauses

A periodic clause orbit is unchanged when every literal offset is shifted by
the same vector and the translate at which the clause is read is shifted in
the opposite direction.  We use that freedom to subtract each clause's first
literal offset.

After normalization:

* every nonempty clause has anchor zero;
* the incidence-graph edge offsets are unchanged;
* the displayed clause position becomes its canonical prototype position;
* satisfiability is unchanged.

This is the geometric gauge needed by the planar 3DM assembly, whose
variable-side triples reference clause terminals at the negated normalized
literal offset.
-/

namespace LeanTrominoes

namespace PeriodicLiteral

/-- Subtract one common clause anchor from a literal offset. -/
def anchorNormalize
    {Variable : Type*} (anchor : Cell)
    (literal : PeriodicLiteral Variable) :
    PeriodicLiteral Variable :=
  ⟨literal.atom, Cell.sub literal.offset anchor, literal.value⟩

@[simp]
theorem anchorNormalize_atom
    {Variable : Type*} (anchor : Cell)
    (literal : PeriodicLiteral Variable) :
    (literal.anchorNormalize anchor).atom = literal.atom := by
  rfl

@[simp]
theorem anchorNormalize_offset
    {Variable : Type*} (anchor : Cell)
    (literal : PeriodicLiteral Variable) :
    (literal.anchorNormalize anchor).offset =
      Cell.sub literal.offset anchor := by
  rfl

@[simp]
theorem anchorNormalize_value
    {Variable : Type*} (anchor : Cell)
    (literal : PeriodicLiteral Variable) :
    (literal.anchorNormalize anchor).value = literal.value := by
  rfl

end PeriodicLiteral

namespace PeriodicClause

/-- Shift a complete clause orbit to the gauge where its first offset is
zero. -/
def anchorNormalize
    {Variable : Type*} (clause : PeriodicClause Variable) :
    PeriodicClause Variable :=
  clause.map
    (PeriodicLiteral.anchorNormalize
      (PeriodicCNF.clauseAnchor clause))

/-- Anchor normalization preserves the literal-list length. -/
@[simp]
theorem anchorNormalize_length
    {Variable : Type*} (clause : PeriodicClause Variable) :
    clause.anchorNormalize.length = clause.length := by
  simp [anchorNormalize]

/-- Every anchor-normalized clause has common anchor zero, including the
empty clause. -/
@[simp]
theorem clauseAnchor_anchorNormalize
    {Variable : Type*} (clause : PeriodicClause Variable) :
    PeriodicCNF.clauseAnchor clause.anchorNormalize = (0, 0) := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      rcases first with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
      simp [anchorNormalize, PeriodicCNF.clauseAnchor,
        PeriodicLiteral.anchorNormalize, Cell.sub]

/-- Reading a normalized clause at `translate` is the same as reading the
original clause at `translate - anchor`. -/
theorem anchorNormalize_holds_iff
    {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Variable) :
    clause.anchorNormalize.Holds assignment translate ↔
      clause.Holds assignment
        (Cell.sub translate (PeriodicCNF.clauseAnchor clause)) := by
  constructor
  · rintro ⟨normalizedLiteral, normalizedMember, normalizedHolds⟩
    rcases List.mem_map.mp normalizedMember with
      ⟨literal, literalMember, normalizedLiteralEq⟩
    subst normalizedLiteral
    refine ⟨literal, literalMember, ?_⟩
    unfold PeriodicLiteral.Holds at normalizedHolds ⊢
    rw [PeriodicLiteral.anchorNormalize_value] at normalizedHolds
    rw [PeriodicLiteral.anchorNormalize_atom,
      PeriodicLiteral.anchorNormalize_offset] at normalizedHolds
    convert normalizedHolds using 1
    apply congrArg (assignment literal.atom)
    rcases translate with ⟨translateX, translateY⟩
    rcases literal.offset with ⟨offsetX, offsetY⟩
    rcases PeriodicCNF.clauseAnchor clause with
      ⟨anchorX, anchorY⟩
    apply Prod.ext <;> simp [Cell.add, Cell.sub] <;> ring
  · rintro ⟨literal, literalMember, literalHolds⟩
    refine
      ⟨literal.anchorNormalize
          (PeriodicCNF.clauseAnchor clause),
        List.mem_map.mpr ⟨literal, literalMember, rfl⟩, ?_⟩
    unfold PeriodicLiteral.Holds at literalHolds ⊢
    rw [PeriodicLiteral.anchorNormalize_value,
      PeriodicLiteral.anchorNormalize_atom,
      PeriodicLiteral.anchorNormalize_offset]
    convert literalHolds using 1
    apply congrArg (assignment literal.atom)
    rcases translate with ⟨translateX, translateY⟩
    rcases literal.offset with ⟨offsetX, offsetY⟩
    rcases PeriodicCNF.clauseAnchor clause with
      ⟨anchorX, anchorY⟩
    apply Prod.ext <;> simp [Cell.add, Cell.sub] <;> ring

end PeriodicClause

namespace PeriodicCNF

/-- Normalize every clause orbit independently. -/
def anchorNormalize
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    PeriodicCNF Variable :=
  ⟨formula.clauses.map PeriodicClause.anchorNormalize⟩

/-- Anchor normalization preserves satisfaction under the same plane-wide
assignment. -/
theorem anchorNormalize_satisfies_iff
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    formula.anchorNormalize.Satisfies assignment ↔
      formula.Satisfies assignment := by
  constructor
  · intro normalizedSatisfies translate clause clauseMember
    have normalizedClauseMember :
        clause.anchorNormalize ∈
          formula.anchorNormalize.clauses :=
      List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
    have normalizedHolds :=
      normalizedSatisfies
        (Cell.add translate
          (PeriodicCNF.clauseAnchor clause))
        clause.anchorNormalize normalizedClauseMember
    have originalHolds :=
      (PeriodicClause.anchorNormalize_holds_iff
        assignment
        (Cell.add translate
          (PeriodicCNF.clauseAnchor clause))
        clause).mp normalizedHolds
    simpa [Cell.add, Cell.sub] using originalHolds
  · intro originalSatisfies translate normalizedClause
      normalizedClauseMember
    rcases List.mem_map.mp normalizedClauseMember with
      ⟨clause, clauseMember, normalizedClauseEq⟩
    subst normalizedClause
    apply
      (PeriodicClause.anchorNormalize_holds_iff
        assignment translate clause).mpr
    exact originalSatisfies
      (Cell.sub translate (PeriodicCNF.clauseAnchor clause))
      clause clauseMember

/-- Existence of a plane-wide satisfying assignment is invariant under
clause-anchor normalization. -/
theorem anchorNormalize_satisfiable_iff
    {Variable : Type*}
    (formula : PeriodicCNF Variable) :
    formula.anchorNormalize.Satisfiable ↔
      formula.Satisfiable := by
  constructor <;> rintro ⟨assignment, satisfies⟩
  · exact
      ⟨assignment,
        (formula.anchorNormalize_satisfies_iff assignment).mp
          satisfies⟩
  · exact
      ⟨assignment,
        (formula.anchorNormalize_satisfies_iff assignment).mpr
          satisfies⟩

/-- Subtracting a common anchor preserves every clause-width bound. -/
theorem anchorNormalize_widthAtMost
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (width : Nat)
    (bounded : formula.WidthAtMost width) :
    formula.anchorNormalize.WidthAtMost width := by
  intro normalizedClause normalizedClauseMem
  rcases List.mem_map.mp normalizedClauseMem with
    ⟨clause, clauseMem, normalizedClauseEq⟩
  subst normalizedClause
  simpa [PeriodicClause.WidthAtMost] using
    bounded clause clauseMem

end PeriodicCNF

namespace PositionedPeriodicCNF

/-- Normalize clause offsets and move each displayed clause point to the
corresponding canonical prototype position. -/
def anchorNormalize
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF Variable :=
  ⟨source.clauses.map fun clause =>
    ⟨canonicalClausePosition placement clause,
      clause.literals.anchorNormalize⟩⟩

/-- Erasing positions commutes exactly with anchor normalization. -/
@[simp]
theorem erase_anchorNormalize
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    (source.anchorNormalize placement).erase =
      source.erase.anchorNormalize := by
  simp [anchorNormalize, PositionedPeriodicCNF.erase,
    PeriodicCNF.anchorNormalize, List.map_map,
    Function.comp_def]

/-- Positioned anchor normalization preserves satisfiability. -/
theorem anchorNormalize_satisfiable_iff
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    (source.anchorNormalize placement).erase.Satisfiable ↔
      source.erase.Satisfiable := by
  rw [erase_anchorNormalize,
    PeriodicCNF.anchorNormalize_satisfiable_iff]

end PositionedPeriodicCNF

end LeanTrominoes
