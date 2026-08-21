/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Tactic.DeriveFintype

/-! # A finite separated encoding for pairs -/

namespace LeanTrominoes
namespace SeparatedProductEncoding

inductive Token (α β : Type*)
  | left (symbol : α)
  | separator
  | right (symbol : β)
  deriving DecidableEq

def encode {α β LeftSymbol RightSymbol : Type*}
    (encodeLeft : α → List LeftSymbol)
    (encodeRight : β → List RightSymbol) :
    α × β → List (Token LeftSymbol RightSymbol)
  | (left, right) =>
      (encodeLeft left).map Token.left ++
        .separator :: (encodeRight right).map Token.right

@[simp] theorem encode_length
    {α β LeftSymbol RightSymbol : Type*}
    (encodeLeft : α → List LeftSymbol)
    (encodeRight : β → List RightSymbol)
    (value : α × β) :
    (encode encodeLeft encodeRight value).length =
      (encodeLeft value.1).length + ((encodeRight value.2).length + 1) := by
  rcases value with ⟨left, right⟩
  simp [encode]

end SeparatedProductEncoding
end LeanTrominoes
