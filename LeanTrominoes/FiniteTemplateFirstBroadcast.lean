/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTemplateQuerySemantics
import LeanTrominoes.UnaryIndexedValueLookupCompiler
import LeanTrominoes.UnaryIndexedValueLookupSemantics
import LeanTrominoes.TM2ComputableInPolyTimeCongr

/-! # Broadcast the first value of each finite-shape block -/
noncomputable section
namespace LeanTrominoes.FiniteTemplateFirstBroadcast
open Turing

def offsets {Profile : Type} (size : Profile → Nat) (profile : Profile) : List Nat :=
  List.replicate (size profile) 0

def queries {Profile : Type} (size : Profile → Nat) : List Profile → List Nat :=
  FiniteTemplateQueries.queriesFrom size (offsets size) 0

def compiler {Source Symbol Profile : Type} [Fintype Symbol] [Inhabited Symbol]
    [Fintype Profile] [Inhabited Profile]
    (encodeSource : Source → List Symbol) (size : Profile → Nat)
    (blocks : Source → List (Profile × List Nat))
    (aligned : ∀ s block, block ∈ blocks s → block.2.length = size block.1)
    (profilesCompiler : TM2ComputableInPolyTime encodeSource id (fun s => (blocks s).map Prod.fst))
    (valuesCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun s => (blocks s).flatMap Prod.snd)) :
    TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun s => (blocks s).flatMap (fun block => List.replicate block.2.length (block.2.headD 0))) := by
  let queryCompiler := TM2CompositionMachine.computableInPolyTime profilesCompiler
    (FiniteTemplateQueries.compiler size (offsets size) (fun profile empty => by simpa [offsets] using empty))
  let physical := UnaryIndexedValueLookup.valuesComputableInPolyTime encodeSource
    (fun s => queries size ((blocks s).map Prod.fst)) (fun s => (blocks s).flatMap Prod.snd)
    queryCompiler valuesCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have valid : ∀ profile i, i ∈ offsets size profile → i < size profile := by
    intro profile i member
    simp only [offsets, List.mem_replicate] at member
    omega
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt]
  · rw [queries, FiniteTemplateQueries.queriesFrom_map]
    rw [FiniteTemplateQueries.queriesFrom_size_congr _ (fun block => block.2.length) _ (blocks s)
      (fun block member => (aligned s block member).symm)]
    have localValid (block : Profile × List Nat) (i : Nat)
        (member : i ∈ List.replicate block.2.length 0) : i < block.2.length := by
      simp only [List.mem_replicate] at member
      omega
    have offsetsEq : ∀ block ∈ blocks s, offsets size block.1 = List.replicate block.2.length 0 := by
      intro block member
      rw [offsets, aligned s block member]
    have queriesEq : ∀ start,
        FiniteTemplateQueries.queriesFrom (fun block : Profile × List Nat => block.2.length)
          (fun block => offsets size block.1) start (blocks s) =
        FiniteTemplateQueries.queriesFrom (fun block : Profile × List Nat => block.2.length)
          (fun block => List.replicate block.2.length 0) start (blocks s) := by
      generalize blocks s = bs at offsetsEq ⊢
      induction bs with
      | nil => intro start; rfl
      | cons block rest ih =>
        intro start
        simp only [FiniteTemplateQueries.queriesFrom]
        rw [offsetsEq block (by simp), ih (fun b hb => offsetsEq b (by simp [hb]))]
    rw [queriesEq, FiniteTemplateQueries.lookup Prod.snd _ localValid]
    apply List.flatMap_congr
    intro block _
    simp only [List.map_replicate, List.headD_eq_getD]
  · intro i member
    have h := (FiniteTemplateQueries.queriesFrom_bound size (offsets size) valid _ 0 i member).2
    have lengths : ((blocks s).map (fun block => size block.1)).sum =
        ((blocks s).flatMap Prod.snd).length := by
      rw [List.length_flatMap]
      congr 1
      exact List.map_congr_left (fun block member => (aligned s block member).symm)
    simpa only [List.map_map, Function.comp_def, Nat.zero_add, lengths] using h

def of_lengths {Source Symbol Profile : Type} [Fintype Symbol] [Inhabited Symbol]
    [Fintype Profile] [Inhabited Profile]
    (encodeSource : Source → List Symbol) (size : Profile → Nat)
    (profiles : Source → List Profile) (blocks : Source → List (List Nat))
    (aligned : ∀ s, (blocks s).map List.length = (profiles s).map size)
    (profilesCompiler : TM2ComputableInPolyTime encodeSource id profiles)
    (valuesCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun s => (blocks s).flatten)) :
    TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun s => (blocks s).flatMap (fun block => List.replicate block.length (block.headD 0))) := by
  have lengthEq (s : Source) : (profiles s).length = (blocks s).length := by
    have h := congrArg List.length (aligned s)
    simpa only [List.length_map] using h.symm
  have fstEq (s : Source) : ((profiles s).zip (blocks s)).map Prod.fst = profiles s :=
    List.map_fst_zip (Nat.le_of_eq (lengthEq s))
  have sndEq (s : Source) : ((profiles s).zip (blocks s)).map Prod.snd = blocks s :=
    List.map_snd_zip (Nat.le_of_eq (lengthEq s).symm)
  have lengths (s : Source) (block : Profile × List Nat)
      (member : block ∈ (profiles s).zip (blocks s)) : block.2.length = size block.1 := by
    obtain ⟨i, hi, equal⟩ := List.getElem_of_mem member
    have pi : i < (profiles s).length := by
      have h : i < min (profiles s).length (blocks s).length := by
        simpa only [List.length_zip] using hi
      omega
    have bi : i < (blocks s).length := by
      have h : i < min (profiles s).length (blocks s).length := by
        simpa only [List.length_zip] using hi
      omega
    have h := congrArg (fun fields => fields[i]?) (aligned s)
    simp only [List.getElem?_map, List.getElem?_eq_getElem pi, List.getElem?_eq_getElem bi, Option.map_some] at h
    rw [← equal, List.getElem_zip]
    exact Option.some.inj h
  let result := compiler encodeSource size (fun s => (profiles s).zip (blocks s)) lengths
    (TM2ComputableInPolyTime.of_eq profilesCompiler (fun s => (fstEq s).symm))
    (TM2ComputableInPolyTime.of_eq valuesCompiler (fun s => (congrArg List.flatten (sndEq s)).symm))
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  have h := congrArg (List.flatMap (fun block : List Nat => List.replicate block.length (block.headD 0))) (sndEq s)
  simpa only [List.flatMap_map] using h

end LeanTrominoes.FiniteTemplateFirstBroadcast
end
