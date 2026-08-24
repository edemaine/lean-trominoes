/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordCrossingRecordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordFieldSemantics

/-! # Decoding crossing-boundary carrier-node identity words -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

@[simp] theorem decodeCrossingBoundary_crossingBoundaryWord_append
    (code : CrossingBoundaryCode) (suffix : List Bool) :
    decodeCrossingBoundary (crossingBoundaryWord code ++ suffix) =
      some (code, suffix) := by
  rcases code with ⟨crossing, side⟩
  simp [decodeCrossingBoundary, crossingBoundaryWord,
    List.append_assoc]

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
