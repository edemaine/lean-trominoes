/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenParserExecution

/-! # Exact complete execution of sparse assignment-token expansion -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

/-- Exact allowance for parsing, cleanup, and final reversal. -/
def totalTime (tromino : Tromino) (tokens : List InputToken) : Nat :=
  (GadgetSparseAssignmentTokens.expand tromino tokens).length + 1 +
    scanTime tromino .horizontal 0 0 tokens

theorem initList_eq_scanHorizontalCfg (tromino : Tromino)
    (tokens : List InputToken) :
    initList (machine tromino) tokens =
      scanHorizontalCfg (activeData tokens 0 0 [] []) := by
  unfold initList machine scanHorizontalCfg cfg activeData
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (tromino : Tromino)
    (output : List OutputToken) :
    haltList (machine tromino) output = haltCfg output := by
  unfold haltList machine haltCfg haltDataCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

/-- The fixed finite machine emits exactly the total semantic expansion on
every finite assignment-token word. -/
def machine_outputsInTime (tromino : Tromino) (tokens : List InputToken) :
    TM2OutputsInTime (machine tromino) tokens
      (some (GadgetSparseAssignmentTokens.expand tromino tokens))
      (totalTime tromino tokens) := by
  have scanned := scan_evalsInTime tromino .horizontal 0 0 tokens [] []
  have scanned' : EvalsToInTime (TM2.step (program tromino))
      (scanHorizontalCfg (activeData tokens 0 0 [] []))
      (some (reverseOutputCfg
        (activeData [] 0 0
          (GadgetSparseAssignmentTokens.expand tromino tokens).reverse [])))
      (scanTime tromino .horizontal 0 0 tokens) := by
    simpa [phaseCfg, phaseData, phaseVertical, phaseExpand,
      GadgetSparseAssignmentTokens.expand] using scanned
  have reversed := reverseOutput_evalsInTime tromino
    (GadgetSparseAssignmentTokens.expand tromino tokens).reverse
    (activeData [] 0 0
      (GadgetSparseAssignmentTokens.expand tromino tokens).reverse []) rfl
  have whole := EvalsToInTime.trans (TM2.step (program tromino))
    (scanTime tromino .horizontal 0 0 tokens)
    ((GadgetSparseAssignmentTokens.expand tromino tokens).reverse.length + 1)
    (scanHorizontalCfg (activeData tokens 0 0 [] []))
    (reverseOutputCfg
      (activeData [] 0 0
        (GadgetSparseAssignmentTokens.expand tromino tokens).reverse []))
    (some (haltCfg (GadgetSparseAssignmentTokens.expand tromino tokens)))
    scanned' (by
      simpa [activeData, haltCfg, List.append_nil] using reversed)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step (program tromino)))^[whole.steps]
        (some (initList (machine tromino) tokens)) =
          some (haltList (machine tromino)
            (GadgetSparseAssignmentTokens.expand tromino tokens))
    rw [initList_eq_scanHorizontalCfg, haltList_eq_haltCfg]
    exact whole.evals_in_steps
  · apply whole.steps_le_m.trans
    simp [totalTime]

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
