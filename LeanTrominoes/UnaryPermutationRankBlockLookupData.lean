/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionData
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.UnaryPermutationRankLookupData

/-! # Fixed-width block lookup in permutation-rank order -/

namespace LeanTrominoes
namespace UnaryPermutationRankBlockLookup

/-- Repeat every permutation-rank row once for every field in a fixed-width
block. -/
def expandedRows (width : Nat) (ranks : List Nat) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordFixedFieldRowExpansion.rows width
    (UnaryPermutationRankLookup.rankRows ranks)

/-- Original blocks followed by an equal number of zero sentinel fields. -/
def paddedValues (fieldValues : List Nat) : List Nat :=
  fieldValues ++ UnaryFieldConstantStreams.zeros fieldValues

/-- Look up every fixed-width block in increasing permutation-rank order. -/
def values (width : Nat) (ranks fieldValues : List Nat) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (expandedRows width ranks).words (paddedValues fieldValues)

end UnaryPermutationRankBlockLookup
end LeanTrominoes
