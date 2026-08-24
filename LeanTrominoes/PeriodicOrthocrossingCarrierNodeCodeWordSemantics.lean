/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordBoundarySemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordTerminalSemantics

/-! # Exact semantics of carrier-node identity words -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

@[simp] theorem decode_word_append
    (code : CarrierNodeCode) (suffix : List Bool) :
    decode (word code ++ suffix) = some (code, suffix) := by
  cases code <;> simp [word, decode]

@[simp] theorem decode_word (code : CarrierNodeCode) :
    decode (word code) = some (code, []) := by
  simpa using decode_word_append code []

/-- Carrier-node identity words are injective because the constructor tag and
every nested field decode canonically. -/
theorem word_injective : Function.Injective word := by
  intro first second wordsEq
  have decodedEq := congrArg decode wordsEq
  simpa using decodedEq

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
