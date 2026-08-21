/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceSplitRouteDescriptorTokenData

/-! # Finite offset data for forward-local route sources -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceForwardOffset

/-- Encode the only nonzero forward-local offset by one finite bit. -/
def isNext {Variable : Type} (literal : PeriodicLiteral Variable) : Bool :=
  literal.offset == (1, 0)

/-- Horizontal coordinate represented by a forward-local offset bit. -/
def coordinate (next : Bool) : Int :=
  if next then 1 else 0

/-- Relative route offset from one finite anchor bit to one literal bit. -/
def relative (literalNext anchorNext : Bool) : Cell :=
  (coordinate literalNext - coordinate anchorNext, 0)

theorem offset_eq_of_forward {Variable : Type}
    (literal : PeriodicLiteral Variable)
    (forward : literal.IsForwardLocal) :
    literal.offset = (coordinate (isNext literal), 0) := by
  rcases forward with current | next
  · simp [current, coordinate, isNext]
  · simp [next, coordinate, isNext]

theorem sub_eq_relative_of_forward {Variable : Type}
    (literal anchor : PeriodicLiteral Variable)
    (literalForward : literal.IsForwardLocal)
    (anchorForward : anchor.IsForwardLocal) :
    Cell.sub literal.offset anchor.offset =
      relative (isNext literal) (isNext anchor) := by
  rw [offset_eq_of_forward literal literalForward,
    offset_eq_of_forward anchor anchorForward]
  rfl

theorem source_literal_offset_eq_bit
    (source : SourceSplitRouteDescriptorTokens.Source)
    (clause : PeriodicClause Nat) (clauseMem : clause ∈ source.formula.clauses)
    (literal : PeriodicLiteral Nat) (literalMem : literal ∈ clause) :
    literal.offset = (coordinate (isNext literal), 0) :=
  offset_eq_of_forward literal
    (source.isForwardLocal clause clauseMem literal literalMem)

theorem source_literal_sub_eq_relative
    (source : SourceSplitRouteDescriptorTokens.Source)
    (clause : PeriodicClause Nat) (clauseMem : clause ∈ source.formula.clauses)
    (literal anchor : PeriodicLiteral Nat)
    (literalMem : literal ∈ clause) (anchorMem : anchor ∈ clause) :
    Cell.sub literal.offset anchor.offset =
      relative (isNext literal) (isNext anchor) :=
  sub_eq_relative_of_forward literal anchor
    (source.isForwardLocal clause clauseMem literal literalMem)
    (source.isForwardLocal clause clauseMem anchor anchorMem)

@[simp] theorem relative_false_false : relative false false = (0, 0) := rfl

@[simp] theorem relative_true_false : relative true false = (1, 0) := rfl

@[simp] theorem relative_false_true : relative false true = (-1, 0) := rfl

@[simp] theorem relative_true_true : relative true true = (0, 0) := rfl

end SourceForwardOffset
end PeriodicCNF
end LeanTrominoes
