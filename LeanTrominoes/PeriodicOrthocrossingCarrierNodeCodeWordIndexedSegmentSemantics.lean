/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordFieldSemantics

/-! # Decoding indexed-segment carrier identity fields -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

@[simp] theorem decodeIndexedSegment_indexedSegmentWord_append
    (code : IndexedGridSegmentCode) (suffix : List Bool) :
    decodeIndexedSegment (indexedSegmentWord code ++ suffix) =
      some (code, suffix) := by
  rcases code with ⟨routeIndex, segmentIndex, start, finish⟩
  simp [decodeIndexedSegment, indexedSegmentWord, List.append_assoc]

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
