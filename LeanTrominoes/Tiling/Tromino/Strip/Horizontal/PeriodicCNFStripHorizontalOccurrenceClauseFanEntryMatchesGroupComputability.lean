/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryGroupComputability
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMClauseRibbonFanDataEncoding

/-! # Computability of clause-terminal entry matching -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntryMatchesGroupComputed_primrec₂ :
    Primrec₂ fun
      (input : HorizontalClauseRibbonGroupInput)
      (entry : HorizontalClauseOccurrenceEntry) =>
        horizontalOccurrenceClauseEntryMatchesGroupComputed (input, entry) := by
  change Primrec horizontalOccurrenceClauseEntryMatchesGroupComputed
  have group : Primrec fun data :
      HorizontalClauseRibbonGroupInput ×
        HorizontalClauseOccurrenceEntry =>
      horizontalOccurrenceClauseEntryGroupComputed
        (data.1.1, data.2) :=
    horizontalOccurrenceClauseEntryGroupComputed_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have equal : Primrec₂ fun first second : PlanarThreeDM.X3CClauseTerminalGroup =>
      decide (first = second) :=
    Primrec.eq.decide
  exact (equal.comp group (Primrec.snd.comp Primrec.fst)).of_eq
    (g := horizontalOccurrenceClauseEntryMatchesGroupComputed)
    (fun _ => by
      unfold horizontalOccurrenceClauseEntryMatchesGroupComputed
      rfl)

end PeriodicCNFStripReduction
end LeanTrominoes
