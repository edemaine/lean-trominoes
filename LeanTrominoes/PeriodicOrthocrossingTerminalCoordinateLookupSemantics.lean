/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordKeyedValueLookupMappedSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCompactKeySemantics

/-! # Physical terminal data selected in periodic atom-occurrence order -/

namespace LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCompactKeys

/-- Every valid terminal query selects its translation-zero physical datum.
All other atom families contribute zero, independently of the source-word encoding. -/
theorem lookup_eq_queryData
    {Variable : Type} [DecidableEq Variable] (formula : PeriodicCNF Variable)
    (queries : List (WrappedPeriodicPlanarSATVariable Variable))
    (valid : ∀ query ∈ queries,
      RetainedDrawingPeriodicPlanarSATVariableValid formula query.original)
    (sourceWord : Variable → List Bool) (datum : CarrierNode → Nat) :
    DelimitedBinaryWordKeyedValueLookup.values
        ⟨queries.map (RetainedCompactAtomWords.word sourceWord)⟩
        ⟨(nodes (PeriodicCNF.numericRouteDescriptors formula)).map nodeWord⟩
        ((nodes (PeriodicCNF.numericRouteDescriptors formula)).map datum) =
      queries.map (queryDatum datum) := by
  apply DelimitedBinaryWordKeyedValueLookup.values_map_candidates
  · intro query queryMember candidate candidateMember equal
    cases queryEq : queryNode query with
    | none =>
        exact False.elim (queryNode_none_word_ne sourceWord query candidate queryEq equal)
    | some node =>
        have nodeMember := queryNode_mem formula query (valid query queryMember) node queryEq
        have keyEq : nodeWord node = nodeWord candidate :=
          (queryNode_word_eq sourceWord query node queryEq).symm.trans equal
        have nodeEq := nodeWord_injective_on (PeriodicCNF.numericRouteDescriptors formula)
          node nodeMember candidate candidateMember keyEq
        rw [← nodeEq]
        simp [queryDatum, queryEq]
  · intro query queryMember missing
    cases queryEq : queryNode query with
    | none => simp [queryDatum, queryEq]
    | some node =>
        exact False.elim (missing (List.mem_map.mpr
          ⟨node, queryNode_mem formula query (valid query queryMember) node queryEq,
            (queryNode_word_eq sourceWord query node queryEq).symm⟩))

end LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCompactKeys
