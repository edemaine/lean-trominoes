/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairFieldBitData

/-! # Compiler for row and column bits of rank-ordered carrier fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing
open CarrierRankDatumCompiledFields

/-- Strict positivity of either endpoint's selected field over every ordered
pair is polynomial-time computable. -/
noncomputable def fieldPresenceBitsComputableInPolyTime
    (side : UnaryFieldPairPresence.Side) (field : Field) :
    TM2ComputableInPolyTime InputEncoding id
      (fieldPresenceBits side field) :=
  UnaryFieldPairPresence.fieldBitsComputableInPolyTime
    InputEncoding field.rankOrderedValues
    field.rankOrderedValuesComputableInPolyTime side

/-- Zero tests of either endpoint's selected field over every ordered pair
are polynomial-time computable. -/
noncomputable def fieldZeroBitsComputableInPolyTime
    (side : UnaryFieldPairPresence.Side) (field : Field) :
    TM2ComputableInPolyTime InputEncoding id (fieldZeroBits side field) :=
  AlignedBooleanListClosure.mapNegatedComputableInPolyTime
    InputEncoding (fieldPresenceBits side field)
    (fieldPresenceBitsComputableInPolyTime side field)

noncomputable def axisBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id axisBits :=
  fieldPresenceBitsComputableInPolyTime .first .horizontal

noncomputable def firstBoundaryBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id firstBoundaryBits :=
  fieldPresenceBitsComputableInPolyTime .first .boundaryPresence

noncomputable def secondBoundaryBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id secondBoundaryBits :=
  fieldPresenceBitsComputableInPolyTime .second .boundaryPresence

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
