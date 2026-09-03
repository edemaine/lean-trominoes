/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixBlockSemantics

/-! # Pointwise semantics of sparse variable-incidence suffix selection -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace VariableIncidenceSparseSuffixToken

private theorem select_map_alignedBody
    (query : Nat) (keys : List Nat) (body : Nat → List AxisDirection)
    (keysNodup : keys.Nodup) :
    (keys.map fun key => (key, body key)).flatMap (fun candidate =>
        if query = candidate.1 then candidate.2 else []) =
      if query ∈ keys then body query else [] := by
  induction keys with
  | nil => simp
  | cons key keys induction =>
      have parts := List.nodup_cons.mp keysNodup
      by_cases same : query = key
      · subst key
        simp only [List.map_cons, List.flatMap_cons, List.mem_cons,
          true_or, if_true]
        rw [induction parts.2, if_neg parts.1]
        simp
      · simp only [List.map_cons, List.flatMap_cons, if_neg same,
          List.nil_append]
        rw [induction parts.2]
        simp [same]

private theorem zip_map_alignedBody
    (keys : List Nat) (body : Nat → List AxisDirection) :
    keys.zip (keys.map body) =
      keys.map fun key => (key, body key) := by
  induction keys with
  | nil => rfl
  | cons key keys induction => simp [induction]

/-- With aligned duplicate-free candidate keys, a sparse suffix query returns
the uniquely aligned routed body when present and the empty body otherwise. -/
theorem sparseBodies_eq_map_alignedBody_or_empty
    (queries keys : List Nat) (bodies : List (List AxisDirection))
    (aligned : keys.length = bodies.length) (keysNodup : keys.Nodup) :
    sparseBodies queries keys bodies =
      queries.map fun query =>
        if query ∈ keys then
          FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            keys bodies query
        else [] := by
  unfold sparseBodies
  let body := FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody keys bodies
  have bodiesEq : bodies = keys.map body :=
    FiniteAlphabetKeyedDelimitedBlockLookup.bodies_eq_map_alignedBody
      keys bodies aligned keysNodup
  conv_lhs => rw [bodiesEq]
  rw [zip_map_alignedBody keys body]
  apply List.map_congr_left
  intro query _queryMember
  exact select_map_alignedBody query keys body keysNodup

end VariableIncidenceSparseSuffixToken
end LeanTrominoes.PeriodicCNFStripReduction

end
