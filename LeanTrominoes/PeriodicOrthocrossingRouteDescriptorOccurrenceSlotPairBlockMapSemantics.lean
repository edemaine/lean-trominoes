/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTags
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # End-delimited blocks of canonical descriptor occurrence-slot pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

open RouteDescriptorOccurrenceSlotBinaryWords
open TM2EndDelimitedBlockMap

def isPairEnd : Token → Bool
  | .pairEnd => true
  | _ => false

def descriptorSlotPairBody
    (pair : TaggedDescriptor × TaggedDescriptor) : List Token :=
  .pairStart ::
    (descriptorSlotUnits .first pair.1 ++
      descriptorSlotUnits .second pair.2)

@[simp] theorem descriptorSlotPairTokens_eq_body
    (pair : TaggedDescriptor × TaggedDescriptor) :
    descriptorSlotPairTokens pair = descriptorSlotPairBody pair ++ [.pairEnd] := by
  simp [descriptorSlotPairTokens, descriptorSlotPairBody,
    List.append_assoc]

theorem taggedFields_continue (side : Side) (field : Fin 12)
    (numbers : List Nat) :
    ∀ token ∈ taggedFields side field numbers,
      isPairEnd token = false := by
  induction numbers generalizing field with
  | nil => simp [taggedFields]
  | cons number numbers induction =>
      intro token member
      simp only [taggedFields, List.mem_append] at member
      rcases member with head | tail
      · have tokenEq : token = .unit side field := by
          have repeated : ¬number = 0 ∧ token = .unit side field := by
            simpa using head
          exact repeated.2
        subst token
        rfl
      · exact induction (nextField field) token tail

theorem descriptorSlotPairBody_continue
    (pair : TaggedDescriptor × TaggedDescriptor) :
    ∀ token ∈ descriptorSlotPairBody pair,
      isPairEnd token = false := by
  intro token member
  simp only [descriptorSlotPairBody, List.mem_cons,
    List.mem_append] at member
  rcases member with start | first | second
  · subst token
    rfl
  · exact taggedFields_continue .first 0
      (descriptorSlotFields pair.1) token first
  · exact taggedFields_continue .second 0
      (descriptorSlotFields pair.2) token second

theorem blocksAux_append_pairEnd
    (reverseBlock body rest : List Token)
    (continues : ∀ token ∈ body, isPairEnd token = false) :
    blocksAux isPairEnd reverseBlock (body ++ .pairEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.pairEnd]) ::
        blocksAux isPairEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil => simp [blocksAux, isPairEnd]
  | cons token body induction =>
      have tokenContinues : isPairEnd token = false :=
        continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          isPairEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

theorem blocksAux_descriptorSlotPairTokens_append
    (pair : TaggedDescriptor × TaggedDescriptor) (rest : List Token) :
    blocksAux isPairEnd [] (descriptorSlotPairTokens pair ++ rest) =
      descriptorSlotPairTokens pair :: blocksAux isPairEnd [] rest := by
  rw [descriptorSlotPairTokens_eq_body, List.append_assoc]
  exact blocksAux_append_pairEnd [] (descriptorSlotPairBody pair) rest
    (descriptorSlotPairBody_continue pair)

@[simp] theorem blocks_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    blocks isPairEnd (encodeDescriptorSlotPairs pairs) =
      pairs.map descriptorSlotPairTokens := by
  unfold blocks encodeDescriptorSlotPairs
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rw [List.flatMap_cons, blocksAux_descriptorSlotPairTokens_append,
        List.map_cons, induction]

theorem mappedOutput_encodeDescriptorSlotPairs
    {Target : Type} (function : List Token → List Target)
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    mappedOutput isPairEnd function (encodeDescriptorSlotPairs pairs) =
      pairs.flatMap fun pair => function (descriptorSlotPairTokens pair) := by
  unfold mappedOutput
  rw [blocks_encodeDescriptorSlotPairs, List.flatMap_map]

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
