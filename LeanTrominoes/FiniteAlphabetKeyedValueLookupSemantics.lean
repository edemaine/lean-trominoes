/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.UnaryFieldPairPresenceSemantics

/-! # Semantics of keyed finite-alphabet value selection -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetKeyedValueLookup

variable {Value : Type} [Fintype Value] [Nonempty Value]

private theorem word_injective :
    Function.Injective UnaryFieldBinaryWords.word := by
  intro first second wordEq
  have lengthEq := congrArg List.length wordEq
  simpa [UnaryFieldBinaryWords.word] using lengthEq

@[simp] theorem valueCode_pos (value : Value) :
    0 < valueCode value := by
  simp [valueCode]

@[simp] theorem pairValue_boundedCode_valueCode (value : Value) :
    pairValue
        (FiniteIndexSlotUnaryDecoder.boundedCode
          (Fintype.card Value) (valueCode value)) =
      value := by
  let index := Fintype.equivFin Value value
  have decoded :=
    FiniteIndexSlotUnaryDecoder.boundedCode_index_slot
      index (1 : Fin 8)
  change pairValue
      (FiniteIndexSlotUnaryDecoder.boundedCode
        (Fintype.card Value) (8 * index.val + (1 : Fin 8).val)) = value
  rw [decoded]
  exact (Fintype.equivFin Value).symm_apply_apply value

private theorem equalityBits_keyWords
    (queries candidateKeys : List Nat) :
    DelimitedBinaryWordEqualitySquare.equalityBits
        (keyWords queries candidateKeys) =
      (combinedKeys queries candidateKeys).flatMap fun first =>
        (combinedKeys queries candidateKeys).map fun second =>
          decide (first = second) := by
  rw [DelimitedBinaryWordEqualitySquare.equalityBits_eq_flatMap]
  unfold keyWords UnaryFieldBinaryWords.words
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _
  rw [List.map_map]
  apply List.map_congr_left
  intro second _
  simp [word_injective.eq_iff]

private theorem presenceBits_metadata
    (side : UnaryFieldPairPresence.Side)
    (queries : List Nat) (candidateValues : List Value) :
    UnaryFieldPairPresence.bits side
        (metadataPairs queries candidateValues) =
      (metadata queries candidateValues).flatMap fun first =>
        (metadata queries candidateValues).map fun second =>
          match side with
          | .first => decide (first ≠ 0)
          | .second => decide (second ≠ 0) := by
  change UnaryFieldPairPresence.fieldBits side
      (metadata queries candidateValues) = _
  rw [UnaryFieldPairPresence.fieldBits_eq_flatMap]
  apply List.flatMap_congr
  intro first _
  apply List.map_congr_left
  intro second _
  cases side with
  | first =>
      by_cases zero : first = 0
      · simp [UnaryFieldPairPresence.valuePresent, zero]
      · simp [UnaryFieldPairPresence.valuePresent, zero,
          Nat.pos_of_ne_zero zero]
  | second =>
      by_cases zero : second = 0
      · simp [UnaryFieldPairPresence.valuePresent, zero]
      · simp [UnaryFieldPairPresence.valuePresent, zero,
          Nat.pos_of_ne_zero zero]

private theorem repeatedCodes_eq_flatMap
    (queries : List Nat) (candidateValues : List Value) :
    repeatedCodes queries candidateValues =
      (metadata queries candidateValues).flatMap fun _ =>
        metadata queries candidateValues := by
  unfold repeatedCodes metadataPairs metadataWords
    UnaryFieldBinaryWords.words
    DelimitedBinaryWordPairProductMachine.pairs
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro first _
  rw [List.map_map]
  simp [UnaryFieldBinaryWords.word, Function.comp_def]

private def entries (queries candidateKeys : List Nat)
    (candidateValues : List Value) : List (Nat × Nat) :=
  (combinedKeys queries candidateKeys).zip
    (metadata queries candidateValues)

private def entryPairs (queries candidateKeys : List Nat)
    (candidateValues : List Value) :
    List ((Nat × Nat) × (Nat × Nat)) :=
  let all := entries queries candidateKeys candidateValues
  all.flatMap fun first => all.map fun second => (first, second)

private theorem zipWith_eq_map_zip
    {First Second Result : Type}
    (firsts : List First) (seconds : List Second)
    (combine : First → Second → Result) :
    List.zipWith combine firsts seconds =
      (firsts.zip seconds).map fun pair =>
        combine pair.1 pair.2 := by
  induction firsts generalizing seconds with
  | nil => rfl
  | cons first firsts induction =>
      cases seconds with
      | nil => rfl
      | cons second seconds =>
          simp only [List.zipWith_cons_cons, List.zip_cons_cons,
            List.map_cons]
          rw [induction seconds]

private theorem zip_self_eq_map {Entry : Type}
    (entries : List Entry) :
    entries.zip entries = entries.map fun entry => (entry, entry) := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.zip_cons_cons, List.map_cons, induction]

private theorem zipWith_rectangular
    {First Second Left Right Result : Type}
    (firstOuter firstInner : List First)
    (secondOuter secondInner : List Second)
    (outerLength : firstOuter.length = secondOuter.length)
    (innerLength : firstInner.length = secondInner.length)
    (left : First → First → Left)
    (right : Second → Second → Right)
    (combine : Left → Right → Result) :
    List.zipWith combine
        (firstOuter.flatMap fun first => firstInner.map (left first))
        (secondOuter.flatMap fun first => secondInner.map (right first)) =
      (firstOuter.zip secondOuter).flatMap fun first =>
        (firstInner.zip secondInner).map fun second =>
          combine (left first.1 second.1)
            (right first.2 second.2) := by
  induction firstOuter generalizing secondOuter with
  | nil =>
      have secondOuterNil : secondOuter = [] :=
        List.eq_nil_of_length_eq_zero outerLength.symm
      subst secondOuter
      rfl
  | cons first firstOuter induction =>
      cases secondOuter with
      | nil => simp at outerLength
      | cons second secondOuter =>
          have tailLength : firstOuter.length = secondOuter.length := by
            simpa using outerLength
          rw [List.flatMap_cons, List.flatMap_cons]
          rw [List.zipWith_append (by simpa using innerLength)]
          simp only [List.zip_cons_cons, List.flatMap_cons,
            List.zipWith_map]
          rw [induction secondOuter tailLength]
          rw [zipWith_eq_map_zip]

private theorem zipWith_square
    {First Second Left Right Result : Type}
    (firsts : List First) (seconds : List Second)
    (lengthEq : firsts.length = seconds.length)
    (left : First → First → Left)
    (right : Second → Second → Right)
    (combine : Left → Right → Result) :
    List.zipWith combine
        (firsts.flatMap fun first => firsts.map (left first))
        (seconds.flatMap fun first => seconds.map (right first)) =
      (firsts.zip seconds).flatMap fun first =>
        (firsts.zip seconds).map fun second =>
          combine (left first.1 second.1)
            (right first.2 second.2) :=
  zipWith_rectangular firsts firsts seconds seconds
    lengthEq lengthEq left right combine

private theorem roleBits_eq_flatMap
    (queries : List Nat) (candidateValues : List Value) :
    roleBits queries candidateValues =
      (metadata queries candidateValues).flatMap fun first =>
        (metadata queries candidateValues).map fun second =>
          decide (first = 0) && decide (second ≠ 0) := by
  unfold roleBits
  rw [presenceBits_metadata .first,
    presenceBits_metadata .second, List.map_flatMap]
  simp only [List.map_map]
  let metadataList := metadata queries candidateValues
  change List.zipWith (fun first second => first && second)
      (metadataList.flatMap fun first =>
        metadataList.map fun _ => !decide (first ≠ 0))
      (metadataList.flatMap fun _ =>
        metadataList.map fun second => decide (second ≠ 0)) = _
  rw [zipWith_square metadataList metadataList rfl]
  rw [zip_self_eq_map]
  simp only [List.flatMap_map, List.map_map]
  apply List.flatMap_congr
  intro first _
  apply List.map_congr_left
  intro second _
  by_cases zero : first = 0 <;> simp [zero]

private theorem flatMap_const_eq_of_length
    {First Second Output : Type}
    (firsts : List First) (seconds : List Second)
    (lengthEq : firsts.length = seconds.length) (body : List Output) :
    firsts.flatMap (fun _ => body) =
      seconds.flatMap (fun _ => body) := by
  induction firsts generalizing seconds with
  | nil =>
      have secondsNil : seconds = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst seconds
      rfl
  | cons first firsts induction =>
      cases seconds with
      | nil => simp at lengthEq
      | cons second seconds =>
          have tailLength : firsts.length = seconds.length := by
            simpa using lengthEq
          rw [List.flatMap_cons, List.flatMap_cons,
            induction seconds tailLength]

private theorem squareSecond_of_zip
    {First Second : Type}
    (firsts : List First) (seconds : List Second)
    (lengthEq : firsts.length = seconds.length) :
    seconds.flatMap (fun _ => seconds) =
      (firsts.zip seconds).flatMap fun _ =>
        (firsts.zip seconds).map Prod.snd := by
  have projected : (firsts.zip seconds).map Prod.snd = seconds :=
    List.map_snd_zip (by omega)
  rw [projected]
  exact flatMap_const_eq_of_length seconds (firsts.zip seconds)
    (by simp [lengthEq]) seconds

private theorem controls_eq_map_entryPairs
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length) :
    controls queries candidateKeys candidateValues =
      (entryPairs queries candidateKeys candidateValues).map fun pair =>
        decide (pair.1.1 = pair.2.1) &&
          (decide (pair.1.2 = 0) && decide (pair.2.2 ≠ 0)) := by
  unfold controls
  rw [equalityBits_keyWords, roleBits_eq_flatMap]
  have lengthEq :
      (combinedKeys queries candidateKeys).length =
        (metadata queries candidateValues).length := by
    simp [combinedKeys, metadata, valueCodes, aligned]
  have square := zipWith_square
      (combinedKeys queries candidateKeys)
      (metadata queries candidateValues) lengthEq
      (fun first second => decide (first = second))
      (fun first second => decide (first = 0) && decide (second ≠ 0))
      (fun first second => first && second)
  simp only [entryPairs, entries, List.map_flatMap, List.map_map]
  simpa [List.map_map, Function.comp_def] using square

private theorem repeatedCodes_eq_map_entryPairs
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length) :
    repeatedCodes queries candidateValues =
      (entryPairs queries candidateKeys candidateValues).map
        (fun pair => pair.2.2) := by
  rw [repeatedCodes_eq_flatMap]
  have lengthEq :
      (combinedKeys queries candidateKeys).length =
        (metadata queries candidateValues).length := by
    simp [combinedKeys, metadata, valueCodes, aligned]
  have square := squareSecond_of_zip
      (combinedKeys queries candidateKeys)
      (metadata queries candidateValues) lengthEq
  simp only [entryPairs, entries, List.map_flatMap, List.map_map]
  simpa [List.map_map, Function.comp_def] using square

private theorem selected_map_map
    {Entry Output : Type} (source : List Entry)
    (predicate : Entry → Bool) (output : Entry → Output) :
    DelimitedBinaryWordBooleanFilter.selected
        (source.map predicate) (source.map output) =
      source.flatMap fun entry =>
        if predicate entry then [output entry] else [] := by
  induction source with
  | nil => rfl
  | cons entry source induction =>
      cases predicate entry <;>
        simp [DelimitedBinaryWordBooleanFilter.selected, induction]

private theorem flatMap_const_nil {Entry Output : Type}
    (entries : List Entry) :
    entries.flatMap (fun _ => ([] : List Output)) = [] := by
  induction entries with
  | nil => rfl
  | cons _ entries induction =>
      simpa only [List.flatMap_cons, List.nil_append] using induction

private theorem map_singleton_if
    {Entry Output : Type} (mapping : Entry → Output)
    (condition : Prop) [Decidable condition] (entry : Entry) :
    (if condition then [entry] else []).map mapping =
      if condition then [mapping entry] else [] := by
  by_cases holds : condition <;> simp [holds]

private theorem selectedCodes_eq_entryPairs
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length) :
    selectedCodes queries candidateKeys candidateValues =
      (entryPairs queries candidateKeys candidateValues).flatMap fun pair =>
        if decide (pair.1.1 = pair.2.1) &&
            (decide (pair.1.2 = 0) && decide (pair.2.2 ≠ 0)) then
          [pair.2.2]
        else [] := by
  unfold selectedCodes
  rw [controls_eq_map_entryPairs _ _ _ aligned,
    repeatedCodes_eq_map_entryPairs _ _ _ aligned]
  exact selected_map_map _ _ _

private theorem entries_eq_query_candidate
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length) :
    entries queries candidateKeys candidateValues =
      queries.map (fun query => (query, 0)) ++
        (candidateKeys.zip candidateValues).map fun candidate =>
          (candidate.1, valueCode candidate.2) := by
  unfold entries combinedKeys metadata valueCodes
  rw [List.zip_append (by simp)]
  have queryPart :
      queries.zip (queries.map fun _ => 0) =
        queries.map fun query => (query, 0) := by
    induction queries with
    | nil => rfl
    | cons query queries induction =>
        simp only [List.map_cons, List.zip_cons_cons]
        rw [induction]
  rw [queryPart]
  apply congrArg (List.append _)
  induction candidateKeys generalizing candidateValues with
  | nil =>
      have valuesNil : candidateValues = [] :=
        List.eq_nil_of_length_eq_zero aligned.symm
      subst candidateValues
      rfl
  | cons key keys induction =>
      cases candidateValues with
      | nil => simp at aligned
      | cons value values =>
          have tailLength : keys.length = values.length := by
            simpa using aligned
          simp [induction values tailLength]

private theorem selectedCodes_eq_expectedCodes
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length) :
    selectedCodes queries candidateKeys candidateValues =
      (expected queries candidateKeys candidateValues).map valueCode := by
  rw [selectedCodes_eq_entryPairs _ _ _ aligned]
  unfold entryPairs
  rw [entries_eq_query_candidate _ _ _ aligned]
  unfold expected
  have codeNe (value : Value) : valueCode value ≠ 0 :=
    Nat.ne_of_gt (valueCode_pos value)
  simp [List.flatMap_append, List.map_append, List.map_flatMap,
    List.flatMap_map, List.flatMap_assoc, flatMap_const_nil,
    map_singleton_if, codeNe]

/-- The square implementation is exactly ordinary query-major keyed
selection when the candidate key and value columns are aligned. -/
@[simp] theorem values_eq_expected
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (aligned : candidateKeys.length = candidateValues.length) :
    values queries candidateKeys candidateValues =
      expected queries candidateKeys candidateValues := by
  unfold values decodedPairs FiniteIndexSlotUnaryDecoder.pairs
  rw [selectedCodes_eq_expectedCodes _ _ _ aligned,
    List.map_map, List.map_map]
  calc
    _ = (expected queries candidateKeys candidateValues).map id := by
      apply List.map_congr_left
      intro value _
      exact pairValue_boundedCode_valueCode value
    _ = expected queries candidateKeys candidateValues := List.map_id _

end LeanTrominoes.FiniteAlphabetKeyedValueLookup

end
