/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingCarrierKeyScanData

/-! # One retained crossing-shift carrier-key block -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Projecting the four boundary sides of one retained crossing translate
gives two horizontal-key copies followed by two vertical-key copies. -/
theorem retainedCrossingBoundaryKeyBlock_eq_shiftBlock
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (crossing : CrossingRecord)
    (shift : Cell) :
    ([⟨crossing.periodTranslate graph shift, .left⟩,
        ⟨crossing.periodTranslate graph shift, .right⟩,
        ⟨crossing.periodTranslate graph shift, .top⟩,
        ⟨crossing.periodTranslate graph shift, .bottom⟩] :
      List CrossingBoundary).map CrossingBoundary.carrierKey =
        retainedCrossingCarrierKeyShiftBlock graph crossing shift := by
  simp [retainedCrossingCarrierKeyShiftBlock,
    CrossingBoundary.carrierKey, occurrenceCarrierKey,
    CrossingRecord.periodTranslate]

end LeanTrominoes.PeriodicOrthocrossing
