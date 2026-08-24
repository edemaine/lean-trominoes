/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateWordData

/-! # Injectively tagged binary words for optional supported values -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

variable {Value : Type*}

/-- Injective tagged encoding of an optional value: `none` is the rejection
sentinel, while every active value starts with `true`. -/
def valueWord (encodeValue : Value → List Bool) :
    Option Value → List Bool
  | none => sentinelWord
  | some value => true :: encodeValue value

@[simp] theorem valueWord_none (encodeValue : Value → List Bool) :
    valueWord encodeValue none = sentinelWord := rfl

@[simp] theorem valueWord_some (encodeValue : Value → List Bool)
    (value : Value) :
    valueWord encodeValue (some value) = true :: encodeValue value := rfl

end LeanTrominoes.PaddedSupportedCandidateWords
