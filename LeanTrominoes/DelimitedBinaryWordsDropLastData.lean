/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords

/-! # Removing the final delimited binary word -/

namespace LeanTrominoes.DelimitedBinaryWordsDropLastMachine

/-- Semantic removal of the final delimited binary word. -/
def dropLast (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.words.dropLast⟩

end LeanTrominoes.DelimitedBinaryWordsDropLastMachine
