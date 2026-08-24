/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

/-! # Lightweight data for delimiter-encoded binary-word pairs -/

namespace LeanTrominoes.DelimitedBinaryWordPairs

/-- Physical alphabet for a sequence of binary-word pairs. -/
inductive Token
  | pairStart
  | firstBit (value : Bool)
  | middle
  | secondBit (value : Bool)
  | pairEnd
  deriving DecidableEq, Inhabited

/-- Semantic input packaged separately from its delimiter encoding. -/
structure Input where
  pairs : List (List Bool × List Bool)
  deriving DecidableEq

def pairTokens (pair : List Bool × List Bool) : List Token :=
  .pairStart ::
    (pair.1.map .firstBit ++
      .middle :: (pair.2.map .secondBit ++ [.pairEnd]))

def encode (input : Input) : List Token :=
  input.pairs.flatMap pairTokens

end LeanTrominoes.DelimitedBinaryWordPairs
