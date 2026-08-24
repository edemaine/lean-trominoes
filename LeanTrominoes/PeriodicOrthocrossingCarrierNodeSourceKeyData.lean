/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Compact source keys for carrier-node identities -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys

abbrev CarrierKey := CarrierKeyWords.CarrierKey
abbrev SourceKeyPair := CarrierKey × CarrierKey

def segmentEndTag : SegmentEnd → Nat
  | .start => 0
  | .finish => 1

def crossingSideTag : CrossingSide → Nat
  | .left => 2
  | .right => 3
  | .top => 4
  | .bottom => 5

/-- Reserve the low three bits of the segment-index field for the node kind
and endpoint/side tag. -/
def taggedKey (key : CarrierKey) (tag : Nat) : CarrierKey :=
  (key.1, 8 * key.2.1 + tag, key.2.2)

def firstCrossingKey (boundary : CrossingBoundary) : CarrierKey :=
  PeriodicGridDrawing.SegmentOccurrenceKey
    boundary.crossing.first boundary.crossing.firstTranslate

def secondCrossingKey (boundary : CrossingBoundary) : CarrierKey :=
  PeriodicGridDrawing.SegmentOccurrenceKey
    boundary.crossing.second boundary.crossing.secondTranslate

/-- A terminal repeats its tagged occurrence key; a crossing boundary uses a
tagged first occurrence key followed by the unmodified second occurrence key.
On descriptor-reconstructed carrier nodes this pair retains exactly the
finite source information needed for identity comparison. -/
def pair : CarrierNode → SourceKeyPair
  | .terminal terminal =>
      let key := taggedKey terminal.carrierKey
        (segmentEndTag terminal.endpoint)
      (key, key)
  | .boundary boundary =>
      (taggedKey (firstCrossingKey boundary)
        (crossingSideTag boundary.side),
      secondCrossingKey boundary)

def datumPair (datum : CarrierNodeRankDatum) : SourceKeyPair :=
  pair datum.identity.node

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys
