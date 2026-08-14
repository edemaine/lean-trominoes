/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterTemplate

/-!
# Complete indexed template input scan

Lift item retention and template execution through the complete input word,
tracking the exact selected-position counter, reversed retained input, reversed
semantic token output, and runtime.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter

def scanTime {Data : Type} (family : Family Data) :
    Nat → List Data → Nat
  | _, [] => 1
  | position, item :: items =>
      2 +
        (match family item with
        | none => 0
        | some recipes => templateTime recipes position) +
        scanTime family
          (if (family item).isSome then position + 1 else position) items

def scan_evalsInTime {Data : Type} [Inhabited Data]
    (family : Family Data) (position : Nat) (items : List Data)
    (data : TapeData Data) (inputEq : data.input = items)
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program family))
      (scanCfg data)
      (some (clearProcessedCfg
        { data with
          input := []
          inputReverse := items.reverse ++ data.inputReverse
          processed :=
            List.replicate
              (position + IndexedTemplateEmitter.selectedCount family items) ()
          scratch := []
          tokenReverse :=
            (emittedAux family position items).reverse ++
              data.tokenReverse }))
      (scanTime family position items) := by
  induction items generalizing position data with
  | nil =>
      have step := oneStep (step_scan_nil family data inputEq)
      convert step using 1 <;>
        simp [scanTime, IndexedTemplateEmitter.selectedCount, emittedAux,
          processedEq, scratchEq]
  | cons item items induction =>
      let retainedData : TapeData Data :=
        { data with
          input := items
          inputReverse := item :: data.inputReverse }
      have retained := oneStep
        (step_scan_cons family data item items inputEq)
      cases value : family item with
      | none =>
          have dispatched := oneStep
            (step_beginItem_none family item retainedData value)
          have firstTwo := EvalsToInTime.trans
            (TM2.step (program family))
            1 1 (scanCfg data) (beginItemCfg item retainedData)
            (some (scanCfg retainedData)) retained dispatched
          have rest := induction position retainedData rfl (by
            simpa [retainedData] using processedEq) (by
            simpa [retainedData] using scratchEq)
          have composed := EvalsToInTime.trans
            (TM2.step (program family))
            2 (scanTime family position items)
            (scanCfg data) (scanCfg retainedData)
            (some (clearProcessedCfg
              { retainedData with
                input := []
                inputReverse := items.reverse ++ retainedData.inputReverse
                processed := List.replicate
                  (position +
                    IndexedTemplateEmitter.selectedCount family items) ()
                scratch := []
                tokenReverse :=
                  (emittedAux family position items).reverse ++
                    retainedData.tokenReverse }))
            firstTwo rest
          convert composed using 1
          · simp [retainedData, IndexedTemplateEmitter.selectedCount,
              emittedAux, value,
              List.reverse_cons, List.append_assoc]
          · simp [scanTime, value]
            omega
      | some recipes =>
          by_cases empty : recipes.length = 0
          · have recipesEmpty : recipes = [] :=
              List.eq_nil_of_length_eq_zero empty
            have dispatched := oneStep
              (step_beginItem_some_empty family item recipes retainedData
                value empty)
            let nextData : TapeData Data :=
              { retainedData with processed := () :: retainedData.processed }
            have firstTwo := EvalsToInTime.trans
              (TM2.step (program family))
              1 1 (scanCfg data) (beginItemCfg item retainedData)
              (some (scanCfg nextData)) retained (by
                simpa [nextData] using dispatched)
            have rest := induction (position + 1) nextData rfl (by
              simp [nextData, retainedData, processedEq,
                List.replicate_succ]) (by
              simpa [nextData, retainedData] using scratchEq)
            have composed := EvalsToInTime.trans
              (TM2.step (program family))
              2 (scanTime family (position + 1) items)
              (scanCfg data) (scanCfg nextData)
              (some (clearProcessedCfg
                { nextData with
                  input := []
                  inputReverse := items.reverse ++ nextData.inputReverse
                  processed := List.replicate
                    (position + 1 +
                      IndexedTemplateEmitter.selectedCount family items) ()
                  scratch := []
                  tokenReverse :=
                    (emittedAux family (position + 1) items).reverse ++
                      nextData.tokenReverse }))
              firstTwo rest
            convert composed using 1
            · subst recipes
              simp [nextData, retainedData,
                IndexedTemplateEmitter.selectedCount, emittedAux, value,
                positionTokens, List.reverse_cons, List.append_assoc]
              congr 3
              omega
            · subst recipes
              simp [scanTime, value, templateTime]
              omega
          · have nonempty : 0 < recipes.length := by omega
            have dispatched := oneStep
              (step_beginItem_some_nonempty family item recipes retainedData
                value nonempty)
            have indexedNonempty :
                0 < (recipesFor family item).length := by
              simpa [recipesFor, value] using nonempty
            let selectedData : TapeData Data := retainedData
            have firstTwo := EvalsToInTime.trans
              (TM2.step (program family))
              1 1 (scanCfg data) (beginItemCfg item retainedData)
              (some (executeCfg item ⟨0, indexedNonempty⟩ selectedData))
              retained (by simpa [selectedData] using dispatched)
            have templateRun := executeRecipes_evalsInTime family item
              ⟨0, indexedNonempty⟩ position selectedData (by
                simpa [selectedData, retainedData] using processedEq) (by
                simpa [selectedData, retainedData] using scratchEq)
            let emittedData : TapeData Data :=
              { selectedData with
                processed := () :: List.replicate position ()
                scratch := []
                tokenReverse :=
                  (positionTokens recipes position).reverse ++
                    selectedData.tokenReverse }
            have throughTemplate := EvalsToInTime.trans
              (TM2.step (program family))
              2 (templateTime recipes position)
              (scanCfg data)
              (executeCfg item ⟨0, indexedNonempty⟩ selectedData)
              (some (scanCfg emittedData)) firstTwo (by
                convert templateRun using 1 <;>
                  simp [emittedData, selectedData, recipesFor, value])
            have rest := induction (position + 1) emittedData rfl (by
              simp [emittedData, List.replicate_succ]) rfl
            have composed := EvalsToInTime.trans
              (TM2.step (program family))
              (templateTime recipes position + 2)
              (scanTime family (position + 1) items)
              (scanCfg data) (scanCfg emittedData)
              (some (clearProcessedCfg
                { emittedData with
                  input := []
                  inputReverse := items.reverse ++ emittedData.inputReverse
                  processed := List.replicate
                    (position + 1 +
                      IndexedTemplateEmitter.selectedCount family items) ()
                  scratch := []
                  tokenReverse :=
                    (emittedAux family (position + 1) items).reverse ++
                      emittedData.tokenReverse }))
              throughTemplate rest
            convert composed using 1
            · simp [emittedData, selectedData, retainedData,
                IndexedTemplateEmitter.selectedCount, emittedAux, value,
                List.reverse_append, List.reverse_cons, List.append_assoc]
              congr 3
              omega
            · simp [scanTime, value]
              omega

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
