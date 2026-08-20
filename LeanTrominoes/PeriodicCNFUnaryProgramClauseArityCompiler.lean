/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineOneHotEmitterSpec
import LeanTrominoes.PeriodicCNFUnaryProgramClauseArityData
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time clause-arity scan of unary transition programs -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace UnaryProgramClauseArity

open AffineEmitterPipeline
open UnaryProgramTokens

/-- A finite block transducer recognizes the clause arities contributed by
each unary-program token. -/
noncomputable def programScanComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List Arity) Token Arity id id programScan :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

def rootPhase : Phase Arity :=
  BoundedMachineOneHotEmitter.fixedPhase [.clauseMarker]

def decodeRootItem : Workspace Arity → List Arity
  | .inl arity => [arity]
  | .inr .clauseMarker => [.unary]
  | .inr _ => []

/-- Append the forced-root clause using a fixed affine emitter phase, then
erase the shared emitter workspace. -/
def appendRoot (arities : List Arity) : List Arity :=
  (rootPhase.run (embedData arities)).flatMap decodeRootItem

@[simp] theorem appendRoot_eq (arities : List Arity) :
    appendRoot arities = arities ++ [.unary] := by
  unfold appendRoot
  rw [show rootPhase.run (embedData arities) =
      embedData arities ++
        ([.clauseMarker] : List Token).map fun token =>
          (Sum.inr token : Workspace Arity) by
    simpa [rootPhase] using
      Phase.run_embed_append_tokens rootPhase arities []]
  simp [embedData, decodeRootItem, List.flatMap_map]

noncomputable def appendRootComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Arity) (List Arity) Arity Arity id id appendRoot := by
  let embedded := TM2CompositionMachine.computableInPolyTime
    (embedDataComputableInPolyTime (Data := Arity))
    rootPhase.computableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime embedded
    (FiniteBlockTransducer.computableInPolyTime decodeRootItem)
  exact complete

/-- The full scan, including the forced-root clause, is polynomial time. -/
noncomputable def requestScanComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List Arity) Token Arity id id requestScan := by
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

end UnaryProgramClauseArity
end PeriodicCNF
end LeanTrominoes
