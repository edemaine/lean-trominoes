/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyWordData

/-! # Exact semantics of carrier-node source-key words -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys

@[simp] theorem decode_word_append
    (keys : SourceKeyPair) (suffix : List Bool) :
    decode (word keys ++ suffix) = some (keys, suffix) := by
  rcases keys with ⟨first, second⟩
  simp [word, decode, List.append_assoc]

@[simp] theorem decode_word (keys : SourceKeyPair) :
    decode (word keys) = some (keys, []) := by
  simpa using decode_word_append keys []

theorem word_injective : Function.Injective word := by
  intro first second wordsEq
  have decodedEq := congrArg decode wordsEq
  simpa using decodedEq

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys
