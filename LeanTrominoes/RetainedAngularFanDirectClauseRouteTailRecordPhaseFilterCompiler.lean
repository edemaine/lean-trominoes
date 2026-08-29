/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilter

/-! # Compilers for direct clause route-tail phase filters -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- The crossover phase selector is a fixed finite block transduction. -/
noncomputable def
    retainedDirectCrossoverRouteTailRecordSlotInputsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      retainedDirectCrossoverRouteTailRecordSlotInputs := by
  unfold retainedDirectCrossoverRouteTailRecordSlotInputs
  exact FiniteBlockTransducer.computableInPolyTime
    retainedDirectCrossoverRouteTailRecordSlotInputBlock

/-- The routed suffix selector is a fixed finite block transduction. -/
noncomputable def
    retainedDirectRoutedRouteTailRecordSlotInputsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      retainedDirectRoutedRouteTailRecordSlotInputs := by
  unfold retainedDirectRoutedRouteTailRecordSlotInputs
  exact FiniteBlockTransducer.computableInPolyTime
    retainedDirectRoutedRouteTailRecordSlotInputBlock

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
