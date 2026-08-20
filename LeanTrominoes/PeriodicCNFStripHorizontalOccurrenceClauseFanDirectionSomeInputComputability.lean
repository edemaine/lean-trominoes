/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanData

/-! # Computability of found clause-direction route inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseDirectionSomeInput_primrec :
    Primrec fun input :
        HorizontalClauseRibbonGroupInput × HorizontalClauseOccurrenceEntry =>
      ((input.1.1.1, input.2.1), input.2.2) := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
