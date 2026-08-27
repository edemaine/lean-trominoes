/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordData
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Compiler for routed Figure 9 source-tail records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteTailRecord

open Computability Turing

/-- One fixed header-index scan is a finite-state linear-time compiler. -/
noncomputable def indexedOutputComputableInPolyTime
    (index : HeaderIndex) :
    TM2ComputableInPolyTime id id (indexedOutput index) :=
  FiniteStateTransducer.computableInPolyTime none
    (transition index) finish

/-- Concatenate the outputs of an arbitrary fixed index list. -/
def indexedOutputsFor (indices : List HeaderIndex)
    (input : List Token) : List OutputToken :=
  indices.flatMap fun index => indexedOutput index input

/-- A fixed list of bounded scans remains polynomial-time computable. -/
noncomputable def indexedOutputsForComputableInPolyTime :
    (indices : List HeaderIndex) →
      TM2ComputableInPolyTime id id (indexedOutputsFor indices)
  | [] => by
      change TM2ComputableInPolyTime id id
        (fun _ : List Token => ([] : List OutputToken))
      let empty := FiniteBlockTransducer.computableInPolyTime
        (fun _ : Token => ([] : List OutputToken))
      refine
        { tm := empty.tm
          inputAlphabet := empty.inputAlphabet
          outputAlphabet := empty.outputAlphabet
          time := empty.time
          outputsFun := ?_ }
      intro input
      have outputEq :
          input.flatMap (fun _ : Token => ([] : List OutputToken)) = [] := by
        induction input with
        | nil => rfl
        | cons _ input induction => exact induction
      have run := empty.outputsFun input
      rw [outputEq] at run
      exact run
  | index :: indices => by
      change TM2ComputableInPolyTime id id
        (fun input => indexedOutput index input ++
          indexedOutputsFor indices input)
      exact TM2ListAppend.computableInPolyTime
        (indexedOutputComputableInPolyTime index)
        (indexedOutputsForComputableInPolyTime indices)

/-- The complete forty-three-scan clause expansion is polynomial time. -/
noncomputable def expandedRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id expandedRecords := by
  change TM2ComputableInPolyTime id id
    (indexedOutputsFor (List.finRange 43))
  exact indexedOutputsForComputableInPolyTime (List.finRange 43)

/-- Recognize the explicit boundary of one flat source-clause record. -/
def isClauseEnd : Token → Bool
  | .clauseEnd => true
  | _ => false

/-- Map the certified forty-three-scan expansion independently over every
complete clause record in an arbitrary physical stream. -/
def batchedRecords (input : List Token) : List OutputToken :=
  TM2EndDelimitedBlockMap.mappedOutput
    isClauseEnd expandedRecords input

/-- Repeated clause-record expansion is polynomial time. -/
noncomputable def batchedRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id batchedRecords :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    expandedRecordsComputableInPolyTime isClauseEnd

end HorizontalRoutedRouteTailRecord
end PeriodicCNFStripReduction
end LeanTrominoes

end
