/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordIndexedSegmentSemantics

/-! # Decoding crossing-record carrier identity fields -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

@[simp] theorem decodeCrossingRecord_crossingRecordWord_append
    (code : CrossingRecordCode) (suffix : List Bool) :
    decodeCrossingRecord (crossingRecordWord code ++ suffix) =
      some (code, suffix) := by
  rcases code with
    ⟨first, firstTranslate, second, secondTranslate, point⟩
  simp [decodeCrossingRecord, crossingRecordWord, List.append_assoc]

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
