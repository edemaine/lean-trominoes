/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFourWordExpansionData
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Compiler for four-word expansion of binary-word pairs -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion

open Computability Turing

/-- Pair tokens translate to one adjacent endpoint-word pair in linear
time. -/
noncomputable def componentTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id componentTokens := by
  unfold componentTokens
  exact FiniteBlockTransducer.computableInPolyTime componentBlock

/-- One complete endpoint pair can be duplicated in polynomial time. -/
noncomputable def duplicatedComponentTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id duplicatedComponentTokens := by
  unfold duplicatedComponentTokens
  exact TM2ListAppend.computableInPolyTime
    componentTokensComputableInPolyTime
    componentTokensComputableInPolyTime

/-- Every complete pair in a pair-delimited stream expands independently to
four endpoint words in polynomial time. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens := by
  unfold tokens
  exact TM2EndDelimitedBlockMap.computableInPolyTime
    duplicatedComponentTokensComputableInPolyTime isPairEnd

end LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion

end
