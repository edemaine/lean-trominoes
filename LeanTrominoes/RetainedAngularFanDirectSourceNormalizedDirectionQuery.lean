/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedFirstDirectionStable

/-! # Finite queries for direct-source normalized directions -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Fixed finite input needed to look up one normalized direct-source
clause-side direction.  Retained clauses have width at most three; invalid
literal indices receive the total fallback direction.  The occurrence slot
is absent because normalization preserves the coordinated first direction. -/
structure RetainedDirectSourceNormalizedDirectionQuery where
  kind : RetainedDirectClauseKind
  literalIndex : Fin 3
  deriving DecidableEq, Fintype

/-- Every direct atlas clause has at most three literal choices. -/
theorem retainedDirectSourcePrefixChoices_length_le_three :
    ∀ kind : RetainedDirectClauseKind,
      (retainedDirectSourcePrefixChoices kind).length ≤ 3 := by
  native_decide

/-- Embed a genuine dependent atlas index into the fixed-width query
alphabet. -/
def retainedDirectSourceNormalizedDirectionQueryOfIndex
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    RetainedDirectSourceNormalizedDirectionQuery := {
  kind := kind
  literalIndex := ⟨index.val,
    Nat.lt_of_lt_of_le index.isLt
      (retainedDirectSourcePrefixChoices_length_le_three kind)⟩
}

/-- Total finite normalized-direction lookup. -/
def retainedDirectSourceNormalizedDirectionOfQuery
    (query : RetainedDirectSourceNormalizedDirectionQuery) :
    AxisDirection :=
  if indexLt :
      query.literalIndex.val <
        (retainedDirectSourcePrefixChoices query.kind).length then
    retainedDirectSourceCoordinatedFirstDirection
      query.kind ⟨query.literalIndex.val, indexLt⟩
  else
    .invalid

/-- On a genuine atlas literal index, the total query lookup is the stable
coordinated first-direction table. -/
theorem retainedDirectSourceNormalizedDirectionOfQuery_eq_coordinated
    (kind : RetainedDirectClauseKind)
    (literalIndex : Fin 3)
    (indexLt :
      literalIndex.val <
        (retainedDirectSourcePrefixChoices kind).length) :
    retainedDirectSourceNormalizedDirectionOfQuery
        ⟨kind, literalIndex⟩ =
      retainedDirectSourceCoordinatedFirstDirection
        kind ⟨literalIndex.val, indexLt⟩ := by
  simp only [retainedDirectSourceNormalizedDirectionOfQuery, indexLt, dite_true]

/-- Evaluating the fixed-width embedding of a genuine dependent atlas index
recovers the public normalized lookup for every occurrence slot. -/
theorem retainedDirectSourceNormalizedDirectionOfQuery_index
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    retainedDirectSourceNormalizedDirectionOfQuery
        (retainedDirectSourceNormalizedDirectionQueryOfIndex
          kind index) =
      retainedDirectSourceNormalizedFirstDirection kind index slot := by
  unfold retainedDirectSourceNormalizedDirectionQueryOfIndex
  rw [retainedDirectSourceNormalizedDirectionOfQuery_eq_coordinated
    kind
    ⟨index.val,
      Nat.lt_of_lt_of_le index.isLt
        (retainedDirectSourcePrefixChoices_length_le_three kind)⟩
    index.isLt]
  exact
    (retainedDirectSourceNormalizedFirstDirection_eq_coordinated
      kind index slot).symm

/-- Elementwise lookup stream used by the fixed finite transducer. -/
def retainedDirectSourceNormalizedDirections
    (queries : List RetainedDirectSourceNormalizedDirectionQuery) :
    List AxisDirection :=
  queries.flatMap fun query =>
    [retainedDirectSourceNormalizedDirectionOfQuery query]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
