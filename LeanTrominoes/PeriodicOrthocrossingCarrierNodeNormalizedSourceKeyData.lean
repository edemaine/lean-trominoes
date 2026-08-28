/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyWordData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationData

/-! # Translation-normalized compact source keys for carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNodeNormalizedSourceKeys

/-- Translation-zero terminal or period-normalized boundary represented as a
physical carrier node, using only the numeric drawing period. -/
def nodeAtPeriod (period : Nat) : CarrierNode → CarrierNode
  | .terminal terminal =>
      .terminal ⟨terminal.indexed, (0, 0), terminal.endpoint⟩
  | .boundary boundary =>
      .boundary
        ⟨crossingRecordPeriodNormalizeAtPeriod period boundary.crossing,
          boundary.side⟩

/-- Compact source-pair identity of a normalized physical carrier node. -/
def pairAtPeriod (period : Nat) (node : CarrierNode) :
    CarrierNodeSourceKeys.SourceKeyPair :=
  CarrierNodeSourceKeys.pair (nodeAtPeriod period node)

/-- The normalized compact identity reconstructed from one reversible rank
datum. -/
def datumPairAtPeriod (period : Nat) (datum : CarrierNodeRankDatum) :
    CarrierNodeSourceKeys.SourceKeyPair :=
  pairAtPeriod period datum.identity.node

/-- Constructor-tagged compact carrier atom word at an explicit numeric
drawing period. -/
def compactWordAtPeriod (period : Nat) : CarrierNode → List Bool
  | .terminal terminal =>
      false :: false :: CarrierKeyWords.word
        (pairAtPeriod period (.terminal terminal)).1
  | .boundary boundary =>
      false :: true :: CarrierNodeSourceKeys.word
        (pairAtPeriod period (.boundary boundary))

end CarrierNodeNormalizedSourceKeys
end LeanTrominoes.PeriodicOrthocrossing
