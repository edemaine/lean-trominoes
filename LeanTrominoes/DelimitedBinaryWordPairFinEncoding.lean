/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.DelimitedBinaryWordPairFintypeData
import LeanTrominoes.DelimitedBinaryWordPairParsingSemantics

/-! # Finite encoding of delimiter-encoded binary-word pairs -/

namespace LeanTrominoes.DelimitedBinaryWordPairs

/-- Physical finite encoding used by the equality machine. -/
noncomputable def finEncoding :
    _root_.Computability.FinEncoding Input where
  toEncoding :=
    { Γ := Token
      encode := encode
      decode := decode
      decode_encode := decode_encode }
  ΓFin := inferInstance

/-- One semantic equality bit per encoded pair. -/
def equalities (input : Input) : List Bool :=
  input.pairs.map fun pair => decide (pair.1 = pair.2)

end LeanTrominoes.DelimitedBinaryWordPairs
