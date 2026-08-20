/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineOneHotEmitterSpec
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time clause-profile scan of unary transition programs -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace UnaryProgramClauseProfile

open AffineEmitterPipeline
open UnaryProgramTokens

noncomputable def programScanComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List ClauseProfile) Token ClauseProfile id id
      programScan :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

def rootPhase : Phase ClauseProfile :=
  BoundedMachineOneHotEmitter.fixedPhase [.clauseMarker]

def decodeRootItem : Workspace ClauseProfile → List ClauseProfile
  | .inl profile => [profile]
  | .inr .clauseMarker => [.unary (current true)]
  | .inr _ => []

def appendRoot (profiles : List ClauseProfile) : List ClauseProfile :=
  (rootPhase.run (embedData profiles)).flatMap decodeRootItem

@[simp] theorem appendRoot_eq (profiles : List ClauseProfile) :
    appendRoot profiles = profiles ++ [.unary (current true)] := by
  unfold appendRoot
  rw [show rootPhase.run (embedData profiles) =
      embedData profiles ++
        ([.clauseMarker] : List Token).map fun token =>
          (Sum.inr token : Workspace ClauseProfile) by
    simpa [rootPhase] using
      Phase.run_embed_append_tokens rootPhase profiles []]
  simp [embedData, decodeRootItem, List.flatMap_map]

noncomputable def appendRootComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List ClauseProfile) (List ClauseProfile)
      ClauseProfile ClauseProfile id id appendRoot := by
  let embedded := TM2CompositionMachine.computableInPolyTime
    (embedDataComputableInPolyTime (Data := ClauseProfile))
    rootPhase.computableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime embedded
    (FiniteBlockTransducer.computableInPolyTime decodeRootItem)
  exact complete

noncomputable def requestScanComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List ClauseProfile) Token ClauseProfile id id
      requestScan := by
  let complete := TM2CompositionMachine.computableInPolyTime
    programScanComputableInPolyTime appendRootComputableInPolyTime
  refine
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := ?_ }
  intro tokens
  have run := complete.outputsFun tokens
  simpa [requestScan, appendRoot_eq] using run

end UnaryProgramClauseProfile
end PeriodicCNF
end LeanTrominoes
