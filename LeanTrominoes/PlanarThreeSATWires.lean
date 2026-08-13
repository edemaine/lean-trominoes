/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATFamilies

/-!
# Positioned equality links for planar SAT wires

Between macrocell gadgets, a logical wire is a chain of distinct variable
vertices joined by the standard two binary implication clauses.  This file
packages one positioned equality link and proves the exact semantics of an
arbitrary finite family of such links.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Two clause positions for the opposite implications of an equality link. -/
structure EqualityPositions where
  forward : Cell
  backward : Cell
  deriving DecidableEq, Repr

/-- The standard two-clause encoding of `first = second`, with both clauses
positioned explicitly in the drawing. -/
def equalityInstance {Variable : Type*}
    (first second : Variable) (positions : EqualityPositions) :
    List (EmbeddedClause Variable) :=
  [⟨positions.forward, [(first, true), (second, false)]⟩,
    ⟨positions.backward, [(first, false), (second, true)]⟩]

private theorem binaryClauseHolds_iff
    {Variable : Type*}
    (assignment : Variable → Bool)
    (position : Cell)
    (first : Variable) (firstValue : Bool)
    (second : Variable) (secondValue : Bool) :
    ClauseHolds assignment
        ⟨position, [(first, firstValue), (second, secondValue)]⟩ ↔
      assignment first = firstValue ∨
        assignment second = secondValue := by
  unfold ClauseHolds
  constructor
  · rintro ⟨literal, literalMem, holds⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at literalMem
    rcases literalMem with literalEq | literalEq
    · subst literal
      exact Or.inl holds
    · subst literal
      exact Or.inr holds
  · intro holds
    rcases holds with firstHolds | secondHolds
    · exact ⟨(first, firstValue), by simp, firstHolds⟩
    · exact ⟨(second, secondValue), by simp, secondHolds⟩

/-- A positioned equality instance is satisfied exactly when its endpoint
values agree. -/
theorem equalityInstance_holds_iff
    {Variable : Type*}
    (assignment : Variable → Bool)
    (first second : Variable) (positions : EqualityPositions) :
    FormulaHolds assignment
        (equalityInstance first second positions) ↔
      assignment first = assignment second := by
  rw [equalityInstance]
  have formulaIff :
      FormulaHolds assignment
          [⟨positions.forward, [(first, true), (second, false)]⟩,
            ⟨positions.backward, [(first, false), (second, true)]⟩] ↔
        ClauseHolds assignment
            ⟨positions.forward,
              [(first, true), (second, false)]⟩ ∧
          ClauseHolds assignment
            ⟨positions.backward,
              [(first, false), (second, true)]⟩ := by
    simp [FormulaHolds]
  rw [formulaIff,
    binaryClauseHolds_iff,
    binaryClauseHolds_iff]
  cases firstValue : assignment first <;>
    cases secondValue : assignment second <;>
    simp

/-- One equality link in a larger wire family. -/
structure EqualityLink (Variable : Type*) where
  first : Variable
  second : Variable
  positions : EqualityPositions
  deriving DecidableEq, Repr

/-- Concatenate the two implication clauses of every listed equality link. -/
def equalityFamily {Variable : Type*}
    (links : List (EqualityLink Variable)) :
    List (EmbeddedClause Variable) :=
  links.flatMap fun link =>
    equalityInstance link.first link.second link.positions

/-- A family of equality links is satisfied exactly when every listed pair
has equal values. -/
theorem equalityFamily_holds_iff
    {Variable : Type*}
    (assignment : Variable → Bool)
    (links : List (EqualityLink Variable)) :
    FormulaHolds assignment (equalityFamily links) ↔
      ∀ link ∈ links,
        assignment link.first = assignment link.second := by
  rw [equalityFamily, formulaHolds_flatMap_iff]
  constructor
  · intro holds link linkMem
    exact (equalityInstance_holds_iff assignment
      link.first link.second link.positions).mp
        (holds link linkMem)
  · intro equal link linkMem
    exact (equalityInstance_holds_iff assignment
      link.first link.second link.positions).mpr
        (equal link linkMem)

/-- Any endpoint labeling that factors through a common carrier key satisfies
all links whose endpoints have the same key. -/
theorem equalityFamily_holds_of_common_key
    {Variable Key : Type*}
    (key : Variable → Key)
    (value : Key → Bool)
    (links : List (EqualityLink Variable))
    (sameKey : ∀ link ∈ links,
      key link.first = key link.second) :
    FormulaHolds (value ∘ key) (equalityFamily links) := by
  apply (equalityFamily_holds_iff (value ∘ key) links).mpr
  intro link linkMem
  simp only [Function.comp_apply]
  rw [sameKey link linkMem]

end PlanarThreeSAT
end LeanTrominoes
