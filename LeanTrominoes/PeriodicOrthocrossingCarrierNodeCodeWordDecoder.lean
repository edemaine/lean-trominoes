/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordData

/-! # Decoder for carrier-node identity words -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

open CarrierKeyWords

def decodeCell (bits : List Bool) : Option (Cell × List Bool) := do
  let (horizontal, bits) ← decodeInt bits
  let (vertical, bits) ← decodeInt bits
  pure ((horizontal, vertical), bits)

def decodeIndexedSegment
    (bits : List Bool) : Option (IndexedGridSegmentCode × List Bool) := do
  let (routeIndex, bits) ← decodeNat bits
  let (segmentIndex, bits) ← decodeNat bits
  let (start, bits) ← decodeCell bits
  let (finish, bits) ← decodeCell bits
  pure (⟨routeIndex, segmentIndex, start, finish⟩, bits)

def decodeCrossingRecord
    (bits : List Bool) : Option (CrossingRecordCode × List Bool) := do
  let (first, bits) ← decodeIndexedSegment bits
  let (firstTranslate, bits) ← decodeCell bits
  let (second, bits) ← decodeIndexedSegment bits
  let (secondTranslate, bits) ← decodeCell bits
  let (point, bits) ← decodeCell bits
  pure (⟨first, firstTranslate, second, secondTranslate, point⟩, bits)

def decodeSegmentEnd :
    List Bool → Option (SegmentEnd × List Bool)
  | false :: bits => some (.start, bits)
  | true :: bits => some (.finish, bits)
  | [] => none

def decodeSegmentTerminal
    (bits : List Bool) : Option (SegmentTerminalCode × List Bool) := do
  let (indexed, bits) ← decodeIndexedSegment bits
  let (translate, bits) ← decodeCell bits
  let (endpoint, bits) ← decodeSegmentEnd bits
  pure (⟨indexed, translate, endpoint⟩, bits)

def decodeCrossingSide :
    List Bool → Option (CrossingSide × List Bool)
  | false :: false :: bits => some (.left, bits)
  | false :: true :: bits => some (.right, bits)
  | true :: false :: bits => some (.top, bits)
  | true :: true :: bits => some (.bottom, bits)
  | _ => none

def decodeCrossingBoundary
    (bits : List Bool) : Option (CrossingBoundaryCode × List Bool) := do
  let (crossing, bits) ← decodeCrossingRecord bits
  let (side, bits) ← decodeCrossingSide bits
  pure (⟨crossing, side⟩, bits)

def decode :
    List Bool → Option (CarrierNodeCode × List Bool)
  | false :: bits => do
      let (boundary, bits) ← decodeCrossingBoundary bits
      pure (.boundary boundary, bits)
  | true :: bits => do
      let (terminal, bits) ← decodeSegmentTerminal bits
      pure (.terminal terminal, bits)
  | [] => none

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
