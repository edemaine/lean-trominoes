/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceDirectionBlockListSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixSemantics

/-! # Complete block semantics of sparse variable-incidence suffixes -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

namespace VariableIncidenceSparseSuffixToken

/-- Non-list form of the one-token routed tagging operation. -/
def routedToken : VariableIncidenceDirectionToken →
    VariableIncidenceSparseSuffixToken
  | .value direction => .routedDirection direction
  | .blockEnd => .routedEnd

@[simp] theorem routedBlock_eq_singleton
    (token : VariableIncidenceDirectionToken) :
    routedBlock token = [routedToken token] := by
  cases token <;> rfl

@[simp] theorem flatMap_routedBlock
    (tokens : List VariableIncidenceDirectionToken) :
    tokens.flatMap routedBlock = tokens.map routedToken := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [induction]

private theorem zip_map_right
    {First Second Third : Type}
    (firsts : List First) (seconds : List Second)
    (transform : Second → Third)
    (aligned : firsts.length = seconds.length) :
    firsts.zip (seconds.map transform) =
      (firsts.zip seconds).map fun pair =>
        (pair.1, transform pair.2) := by
  induction firsts generalizing seconds with
  | nil => rfl
  | cons first firsts induction =>
      cases seconds with
      | nil => simp at aligned
      | cons second seconds =>
          have tailAligned : firsts.length = seconds.length := by
            simpa using aligned
          simp only [List.map_cons, List.zip_cons_cons]
          rw [induction seconds tailAligned]

private theorem routedCandidatePairs
    (blockKeys : List Nat) (bodies : List (List AxisDirection))
    (aligned : bodies.length = blockKeys.length) :
    (FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys blockKeys
        (FiniteAlphabetDelimitedBlockJoin.blocks bodies)).zip
      ((FiniteAlphabetDelimitedBlockJoin.blocks bodies).flatMap
        routedBlock) =
      (blockKeys.zip bodies).flatMap fun candidate =>
        (FiniteAlphabetDelimitedBlockJoin.block candidate.2).map fun token =>
          (candidate.1, routedToken token) := by
  rw [flatMap_routedBlock]
  rw [zip_map_right _ _ routedToken (by
    rw [FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys_length])]
  rw [FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys_blocks_zip
    blockKeys bodies aligned]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro candidate candidateMember
  rw [List.map_map]
  rfl

private theorem defaultCandidatePairs (queries : List Nat) :
    queries.zip (queries.map fun _ => defaultEnd) =
      queries.map fun query => (query, defaultEnd) := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      simp only [List.map_cons, List.zip_cons_cons]
      rw [induction]

private theorem candidatePairs
    (queries blockKeys : List Nat) (bodies : List (List AxisDirection))
    (aligned : bodies.length = blockKeys.length) :
    (FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys blockKeys
          (FiniteAlphabetDelimitedBlockJoin.blocks bodies) ++ queries).zip
        ((FiniteAlphabetDelimitedBlockJoin.blocks bodies).flatMap
            routedBlock ++
          queries.map fun _ => defaultEnd) =
      ((blockKeys.zip bodies).flatMap fun candidate =>
        (FiniteAlphabetDelimitedBlockJoin.block candidate.2).map fun token =>
          (candidate.1, routedToken token)) ++
        queries.map fun query => (query, defaultEnd) := by
  rw [List.zip_append (by
    rw [FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys_length,
      flatMap_routedBlock, List.length_map])]
  rw [routedCandidatePairs blockKeys bodies aligned,
    defaultCandidatePairs]

private theorem selectDefaults_none
    (query : Nat) (keys : List Nat)
    (absent : query ∉ keys) :
    (keys.map fun key => (key, defaultEnd)).flatMap
        (fun candidate =>
          if query = candidate.1 then [candidate.2] else []) = [] := by
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      have different : query ≠ key := by
        intro same
        apply absent
        simp [same]
      have tailAbsent : query ∉ keys := by
        intro member
        exact absent (by simp [member])
      simp [different, induction tailAbsent]

private theorem selectDefaults_unique
    (query : Nat) (keys : List Nat)
    (keysNodup : keys.Nodup) (present : query ∈ keys) :
    (keys.map fun key => (key, defaultEnd)).flatMap
        (fun candidate =>
          if query = candidate.1 then [candidate.2] else []) =
      [defaultEnd] := by
  induction keys with
  | nil => simp at present
  | cons key keys induction =>
      have parts := List.nodup_cons.mp keysNodup
      by_cases same : query = key
      · subst query
        simp [selectDefaults_none key keys parts.1]
      · have tailPresent : query ∈ keys := by
          simpa [same] using present
        simp [same, induction parts.2 tailPresent]

@[simp] theorem output_taggedBlock (body : List AxisDirection) :
    ((FiniteAlphabetDelimitedBlockJoin.block body).map routedToken).flatMap
        outputBlock =
      body.map FiniteAlphabetDelimitedBlockJoin.Token.value := by
  unfold FiniteAlphabetDelimitedBlockJoin.block
  rw [List.map_append, List.flatMap_append, List.map_map,
    List.flatMap_map]
  simp only [routedToken, outputBlock, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    body.flatMap (fun direction =>
      [FiniteAlphabetDelimitedBlockJoin.Token.value direction]) =
      body.map FiniteAlphabetDelimitedBlockJoin.Token.value
  rw [← List.map_eq_flatMap]

private theorem output_selectedRouted
    (query : Nat) (candidates : List (Nat × List AxisDirection)) :
    (candidates.flatMap fun candidate =>
        if query = candidate.1 then
          (FiniteAlphabetDelimitedBlockJoin.block candidate.2).map
            routedToken
        else []).flatMap outputBlock =
      (candidates.flatMap fun candidate =>
        if query = candidate.1 then candidate.2 else []).map
          FiniteAlphabetDelimitedBlockJoin.Token.value := by
  rw [List.flatMap_assoc, List.map_flatMap]
  apply List.flatMap_congr
  intro candidate candidateMember
  by_cases same : query = candidate.1
  · simp [same, output_taggedBlock]
  · simp [same]

private theorem select_routedKey
    (query key : Nat) (tokens : List VariableIncidenceDirectionToken) :
    (tokens.map fun token => (key, routedToken token)).flatMap
        (fun candidate =>
          if query = candidate.1 then [candidate.2] else []) =
      if query = key then tokens.map routedToken else [] := by
  induction tokens with
  | nil => simp
  | cons token tokens induction =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [induction]
      by_cases same : query = key <;> simp [same]

private theorem select_routedCandidates
    (query : Nat) (candidates : List (Nat × List AxisDirection)) :
    ((candidates.flatMap fun candidate =>
        (FiniteAlphabetDelimitedBlockJoin.block candidate.2).map fun token =>
          (candidate.1, routedToken token)).flatMap fun candidate =>
            if query = candidate.1 then [candidate.2] else []) =
      candidates.flatMap fun candidate =>
        if query = candidate.1 then
          (FiniteAlphabetDelimitedBlockJoin.block candidate.2).map routedToken
        else [] := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [select_routedKey, induction]

/-- Per-query routed directions, concatenating all bodies carrying the
requested incidence key. -/
def sparseBodies (queries blockKeys : List Nat)
    (bodies : List (List AxisDirection)) : List (List AxisDirection) :=
  queries.map fun query =>
    (blockKeys.zip bodies).flatMap fun candidate =>
      if query = candidate.1 then candidate.2 else []

/-- Keyed routed candidates plus one default delimiter per query serialize
exactly one complete sparse suffix body per query. -/
theorem output_expected
    (queries blockKeys : List Nat) (bodies : List (List AxisDirection))
    (aligned : bodies.length = blockKeys.length)
    (queriesNodup : queries.Nodup) :
    output
        (FiniteAlphabetKeyedValueLookup.expected queries
          (FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys blockKeys
              (FiniteAlphabetDelimitedBlockJoin.blocks bodies) ++ queries)
          ((FiniteAlphabetDelimitedBlockJoin.blocks bodies).flatMap
              routedBlock ++
            queries.map fun _ => defaultEnd)) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (sparseBodies queries blockKeys bodies) := by
  unfold output FiniteAlphabetKeyedValueLookup.expected sparseBodies
  rw [candidatePairs queries blockKeys bodies aligned]
  unfold FiniteAlphabetDelimitedBlockJoin.blocks
  rw [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro query queryMember
  rw [List.flatMap_append]
  rw [List.flatMap_append]
  rw [select_routedCandidates]
  rw [selectDefaults_unique query queries queriesNodup queryMember]
  rw [output_selectedRouted]
  simp [outputBlock, FiniteAlphabetDelimitedBlockJoin.block]

end VariableIncidenceSparseSuffixToken

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem map_const_eq_of_length
    {First Second Output : Type}
    (firsts : List First) (seconds : List Second) (value : Output)
    (aligned : firsts.length = seconds.length) :
    firsts.map (fun _ => value) = seconds.map (fun _ => value) := by
  induction firsts generalizing seconds with
  | nil =>
      cases seconds <;> simp_all
  | cons first firsts induction =>
      cases seconds with
      | nil => simp at aligned
      | cons second seconds =>
          simp only [List.map_cons]
          rw [induction seconds (by simpa using aligned)]

private theorem
    directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
        decider symbols =
      FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys
          (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
          (FiniteAlphabetDelimitedBlockJoin.blocks
            (directSourceFinalGroupedColoredOccurrenceDirectionBodies
              decider symbols)) ++
        directSourceFinalGroupedVariableIncidenceKeys decider symbols := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
    directSourceFinalGroupedRoutedDirectionTokenKeys
  rw [directSourceFinalGroupedColoredOccurrenceDirectionTokens_eq_bodyList]

private theorem
    directSourceFinalGroupedVariableIncidenceSuffixCandidateValues_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
        decider symbols =
      (FiniteAlphabetDelimitedBlockJoin.blocks
          (directSourceFinalGroupedColoredOccurrenceDirectionBodies
            decider symbols)).flatMap
          VariableIncidenceSparseSuffixToken.routedBlock ++
        (directSourceFinalGroupedVariableIncidenceKeys decider symbols).map
          fun _ => VariableIncidenceSparseSuffixToken.defaultEnd := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
  rw [directSourceFinalGroupedColoredOccurrenceDirectionTokens_eq_bodyList]
  rw [map_const_eq_of_length
    (directSourceFinalGroupedVariableIncidencePrefixQueries decider symbols)
    (directSourceFinalGroupedVariableIncidenceKeys decider symbols)
    VariableIncidenceSparseSuffixToken.defaultEnd
    (directSourceFinalGroupedVariableIncidenceKeys_length
      decider symbols).symm]

/-- Exact sparse suffix bodies selected for the full variable-incidence key
range. -/
noncomputable def directSourceFinalGroupedVariableIncidenceSuffixBodies
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  VariableIncidenceSparseSuffixToken.sparseBodies
    (directSourceFinalGroupedVariableIncidenceKeys decider symbols)
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies decider symbols)

/-- The compiled sparse suffix stream is exactly one complete delimited body
for every full grouped variable incidence. -/
theorem directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens
        decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (directSourceFinalGroupedVariableIncidenceSuffixBodies
          decider symbols) := by
  rw [directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens_eq_expected]
  unfold directSourceFinalGroupedVariableIncidenceSparseSuffixTokensExpected
  rw [directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys_eq_blocks,
    directSourceFinalGroupedVariableIncidenceSuffixCandidateValues_eq_blocks]
  unfold directSourceFinalGroupedVariableIncidenceSuffixBodies
  apply VariableIncidenceSparseSuffixToken.output_expected
  · exact
      directSourceFinalGroupedColoredOccurrenceDirectionBodies_length_eq_keys
        decider symbols
  · rw [directSourceFinalGroupedVariableIncidenceKeys_eq_range]
    exact List.nodup_range

end LeanTrominoes.PeriodicCNFStripReduction

end
