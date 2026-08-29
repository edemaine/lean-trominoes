/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeSize
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankStream

/-! # Length of the global retained-occurrence stable-rank stream -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicThreeSATThree

@[simp] theorem retainedOccurrenceGlobalStableTerminalRanks_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableTerminalRanks source routes).length =
      PeriodicCNF.presentationLiteralCount source := by
  unfold retainedOccurrenceGlobalStableTerminalRanks
  simp [allOccurrenceVariables, taggedLiterals_length]

end LeanTrominoes.PeriodicEightOccurrenceSplit
