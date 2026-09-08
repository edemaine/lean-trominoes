/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingInternalCrossingCoordinateKeyCompiler
import LeanTrominoes.DelimitedBinaryWordKeyedValueLookupMappedSemantics

/-! # Exact lookup of crossing data for internal gadget occurrences -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.InternalCrossingCoordinateKeys
open PeriodicCNFStripReduction.DirectSourceFinalAtomWords

theorem mem_candidates_iff (descriptors : List RouteDescriptor) (candidate : Candidate) :
    candidate ∈ candidates descriptors ↔ candidate.2 ∈ CarrierCrossingMacroOrigin.nodes descriptors := by
  rcases candidate with ⟨role, node⟩
  simp [candidates]

theorem nodeWord_injective_on (descriptors : List RouteDescriptor)
    (first : Candidate) (firstMember : first ∈ candidates descriptors)
    (second : Candidate) (secondMember : second ∈ candidates descriptors)
    (equal : nodeWord first = nodeWord second) : first = second := by
  have payloadEq :
      CarrierNodeSourceKeys.word (CarrierNodeSourceKeys.pair first.2) ++ crossoverInternalWord first.1 =
        CarrierNodeSourceKeys.word (CarrierNodeSourceKeys.pair second.2) ++ crossoverInternalWord second.1 := by
    simpa [nodeWord] using equal
  have decodedEq :
      (CarrierNodeSourceKeys.pair first.2, crossoverInternalWord first.1) =
        (CarrierNodeSourceKeys.pair second.2, crossoverInternalWord second.1) := by
    apply Option.some.inj
    simpa using congrArg CarrierNodeSourceKeys.decode payloadEq
  have nodeEq : first.2 = second.2 := by
    apply CarrierCrossingCoordinateKeys.nodeWord_injective_on descriptors
      first.2 ((mem_candidates_iff descriptors first).mp firstMember)
      second.2 ((mem_candidates_iff descriptors second).mp secondMember)
    have pairEq : CarrierNodeSourceKeys.pair first.2 = CarrierNodeSourceKeys.pair second.2 :=
      congrArg Prod.fst decodedEq
    simp only [CarrierCrossingCoordinateKeys.nodeWord, pairEq]
  have roleEq : first.1 = second.1 := by
    have appendedEq : crossoverInternalWord first.1 ++ [] = crossoverInternalWord second.1 ++ [] := by
      simpa using congrArg Prod.snd decodedEq
    have decodedRoleEq := congrArg decodeCrossoverInternal appendedEq
    simp only [decodeCrossoverInternal_word_append] at decodedRoleEq
    exact congrArg (fun pair : PlanarThreeSAT.CrossoverInternal × List Bool => pair.1)
      (Option.some.inj decodedRoleEq)
  exact Prod.ext roleEq nodeEq

/-- The left boundary is the canonical physical key of an internal crossing atom. -/
def queryCandidate {Variable : Type*} (query : WrappedPeriodicPlanarSATVariable Variable) :
    Option Candidate :=
  match query.original with
  | .crossoverInternal (crossing, role) => some (role, .boundary ⟨crossing, .left⟩)
  | _ => none

def queryDatum {Variable : Type*} (datum : Candidate → Nat)
    (query : WrappedPeriodicPlanarSATVariable Variable) : Nat :=
  ((queryCandidate query).map datum).getD 0

theorem queryCandidate_word_eq {Variable : Type*} (sourceWord : Variable → List Bool)
    (query : WrappedPeriodicPlanarSATVariable Variable) (candidate : Candidate)
    (equal : queryCandidate query = some candidate) :
    RetainedCompactAtomWords.word sourceWord query = nodeWord candidate := by
  rcases query with ⟨query⟩
  cases query <;> simp only [queryCandidate, reduceCtorEq] at equal
  rename_i internal
  rcases internal with ⟨crossing, role⟩
  cases Option.some.inj equal
  rfl

theorem queryCandidate_none_word_ne {Variable : Type*} (sourceWord : Variable → List Bool)
    (query : WrappedPeriodicPlanarSATVariable Variable) (candidate : Candidate)
    (equal : queryCandidate query = none) :
    RetainedCompactAtomWords.word sourceWord query ≠ nodeWord candidate := by
  rcases query with ⟨query⟩
  cases query <;> simp [queryCandidate] at equal
  all_goals simp [RetainedCompactAtomWords.word, nodeWord]

theorem queryCandidate_mem {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula query.original)
    (candidate : Candidate) (equal : queryCandidate query = some candidate) :
    candidate ∈ candidates (PeriodicCNF.numericRouteDescriptors formula) := by
  rcases query with ⟨query⟩
  cases query <;> simp only [queryCandidate, reduceCtorEq] at equal
  rename_i internal
  rcases internal with ⟨crossing, role⟩
  cases Option.some.inj equal
  rw [mem_candidates_iff]
  exact CarrierCrossingCoordinateKeys.queryNode_mem formula nonempty
    ⟨.boundary ⟨crossing, .left⟩⟩
    (RetainedCompactAtomWords.crossingLeft_valid_of_internal_valid formula crossing role valid)
    (.boundary ⟨crossing, .left⟩) rfl

/-- Every valid internal occurrence selects its own crossing and internal role. -/
theorem lookup_eq_queryData
    {Variable : Type} [DecidableEq Variable] (formula : PeriodicCNF Variable)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (queries : List (WrappedPeriodicPlanarSATVariable Variable))
    (valid : ∀ query ∈ queries,
      RetainedDrawingPeriodicPlanarSATVariableValid formula query.original)
    (sourceWord : Variable → List Bool) (datum : Candidate → Nat) :
    DelimitedBinaryWordKeyedValueLookup.values
        ⟨queries.map (RetainedCompactAtomWords.word sourceWord)⟩
        ⟨(candidates (PeriodicCNF.numericRouteDescriptors formula)).map nodeWord⟩
        ((candidates (PeriodicCNF.numericRouteDescriptors formula)).map datum) =
      queries.map (queryDatum datum) := by
  apply DelimitedBinaryWordKeyedValueLookup.values_map_candidates
  · intro query queryMember candidate candidateMember equal
    cases queryEq : queryCandidate query with
    | none =>
        exact False.elim (queryCandidate_none_word_ne sourceWord query candidate queryEq equal)
    | some selected =>
        have selectedMember := queryCandidate_mem formula nonempty query (valid query queryMember) selected queryEq
        have keyEq : nodeWord selected = nodeWord candidate :=
          (queryCandidate_word_eq sourceWord query selected queryEq).symm.trans equal
        have candidateEq := nodeWord_injective_on (PeriodicCNF.numericRouteDescriptors formula)
          selected selectedMember candidate candidateMember keyEq
        rw [← candidateEq]
        simp [queryDatum, queryEq]
  · intro query queryMember missing
    cases queryEq : queryCandidate query with
    | none => simp [queryDatum, queryEq]
    | some selected =>
        exact False.elim (missing (List.mem_map.mpr
          ⟨selected, queryCandidate_mem formula nonempty query (valid query queryMember) selected queryEq,
            (queryCandidate_word_eq sourceWord query selected queryEq).symm⟩))

end LeanTrominoes.PeriodicOrthocrossing.InternalCrossingCoordinateKeys
end
