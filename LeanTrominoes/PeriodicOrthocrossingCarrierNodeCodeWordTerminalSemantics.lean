/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordIndexedSegmentSemantics

/-! # Decoding terminal carrier-node identity words -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

@[simp] theorem decodeSegmentTerminal_segmentTerminalWord_append
    (code : SegmentTerminalCode) (suffix : List Bool) :
    decodeSegmentTerminal (segmentTerminalWord code ++ suffix) =
      some (code, suffix) := by
  rcases code with ⟨indexed, translate, endpoint⟩
  simp [decodeSegmentTerminal, segmentTerminalWord, List.append_assoc]

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
