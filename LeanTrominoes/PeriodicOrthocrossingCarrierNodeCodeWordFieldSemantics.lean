/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordDecoder

/-! # Decoding primitive carrier-node identity fields -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

@[simp] theorem decodeCell_cellWord_append
    (cell : Cell) (suffix : List Bool) :
    decodeCell (cellWord cell ++ suffix) = some (cell, suffix) := by
  rcases cell with ⟨horizontal, vertical⟩
  simp [decodeCell, cellWord, List.append_assoc]

@[simp] theorem decodeSegmentEnd_segmentEndWord_append
    (endpoint : SegmentEnd) (suffix : List Bool) :
    decodeSegmentEnd (segmentEndWord endpoint ++ suffix) =
      some (endpoint, suffix) := by
  cases endpoint <;> simp [segmentEndWord, decodeSegmentEnd]

@[simp] theorem decodeCrossingSide_crossingSideWord_append
    (side : CrossingSide) (suffix : List Bool) :
    decodeCrossingSide (crossingSideWord side ++ suffix) =
      some (side, suffix) := by
  cases side <;> simp [crossingSideWord, decodeCrossingSide]

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
