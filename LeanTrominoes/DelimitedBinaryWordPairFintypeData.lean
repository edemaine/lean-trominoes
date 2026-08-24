/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import LeanTrominoes.DelimitedBinaryWordPairData

/-! # Finiteness of the delimiter-encoded pair alphabet -/

namespace LeanTrominoes.DelimitedBinaryWordPairs

deriving instance Fintype for Token

end LeanTrominoes.DelimitedBinaryWordPairs
