/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceStableRank

/-! # Counting semantics of retained angular occurrence stable ranks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- A genuine occurrence's stable terminal rank is its number of strictly
smaller terminal keys plus the number of equal-key occurrences earlier in
the source presentation. -/
theorem retainedOccurrenceStableTerminalRank_eq_counts
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    retainedOccurrenceStableTerminalRank source routes atom copy =
      ((occurrenceVariables source atom).filter fun other =>
        decide
          (retainedOccurrenceTerminalCoordinate routes other <
            retainedOccurrenceTerminalCoordinate routes copy)).length +
      (((occurrenceVariables source atom).take
          ((occurrenceVariables source atom).idxOf copy)).filter fun other =>
        decide
          (retainedOccurrenceTerminalCoordinate routes other =
            retainedOccurrenceTerminalCoordinate routes copy)).length := by
  unfold retainedOccurrenceStableTerminalRank
  simpa using
    (StableListRanks.selectedIndexedLowerRank_eq
      (retainedOccurrenceTerminalCoordinate routes)
      (fun _ : ThreeOccurrenceVariable Variable => true)
      (occurrenceVariables source atom)
      ((occurrenceVariables source atom).idxOf copy) copy
      (List.getElem?_idxOf copyMember))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
