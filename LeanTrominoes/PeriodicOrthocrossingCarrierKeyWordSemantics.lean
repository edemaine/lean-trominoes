/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData

/-! # Semantics of self-delimiting carrier-key words -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierKeyWords

theorem decodeNatAux_replicate_false
    (count number : Nat) (suffix : List Bool) :
    decodeNatAux count
        (List.replicate number false ++ true :: suffix) =
      some (count + number, suffix) := by
  induction number generalizing count with
  | zero => simp [decodeNatAux]
  | succ number induction =>
      rw [List.replicate_succ, List.cons_append, decodeNatAux,
        induction (count + 1)]
      congr 2
      omega

@[simp] theorem decodeNat_natField_append
    (number : Nat) (suffix : List Bool) :
    decodeNat (natField number ++ suffix) = some (number, suffix) := by
  unfold decodeNat natField
  rw [List.append_assoc]
  simp only [List.singleton_append]
  rw [decodeNatAux_replicate_false]
  simp

@[simp] theorem decodeInt_intField_append
    (integer : Int) (suffix : List Bool) :
    decodeInt (intField integer ++ suffix) = some (integer, suffix) := by
  cases integer <;>
    simp [intField, decodeInt]

@[simp] theorem decode_word_append
    (key : CarrierKey) (suffix : List Bool) :
    decode (word key ++ suffix) = some (key, suffix) := by
  rcases key with ⟨routeIndex, segmentIndex, horizontal, vertical⟩
  simp [word, decode, List.append_assoc]

@[simp] theorem decode_word (key : CarrierKey) :
    decode (word key) = some (key, []) := by
  simpa using decode_word_append key []

/-- Carrier-key words are injective because their four fields decode
canonically. -/
theorem word_injective : Function.Injective word := by
  intro first second wordsEq
  have decodedEq := congrArg decode wordsEq
  simpa using decodedEq

end LeanTrominoes.PeriodicOrthocrossing.CarrierKeyWords
