/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineIndexedEmitterPipelineData
import LeanTrominoes.PeriodicCNFPolySpaceRequestEmitter
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTableAppenderData

/-! # Indexed phase boundary for all four affine vertex tables -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open GadgetSparseAffineIndexedEmitter

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineTablePhaseDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- All four finite-table blocks in canonical contracted-vertex order. -/
def directSparseComputedAffineTableVertexRequestsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  directSparseComputedAffineTableTripleRequestsOfSymbols decider symbols ++
    (directSparseComputedAffineTableElementRequestsOfSymbols
        decider .red symbols ++
      (directSparseComputedAffineTableElementRequestsOfSymbols
          decider .green symbols ++
        directSparseComputedAffineTableElementRequestsOfSymbols
          decider .blue symbols))

/-- The combined table word is exactly the canonical compact vertex-request
word, not merely a pointwise or permuted representation. -/
theorem directSparseComputedAffineVertexRequestsOfSymbols_eq_table
    (symbols : List encoding.Γ) :
    directSparseComputedAffineVertexRequestsOfSymbols decider symbols =
      directSparseComputedAffineTableVertexRequestsOfSymbols
        decider symbols := by
  rw [directSparseComputedAffineVertexRequestsOfSymbols_eq_indexed,
    directSparseComputedAffineIndexedVertexRequestsOfSymbols_eq_blocks,
    directSparseComputedAffineIndexedTripleRequestsOfSymbols_eq_table,
    directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table,
    directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table,
    directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table]
  rfl

/-- Four fixed indexed record families over the already generated unary
program stream, together with exact blockwise table specifications. -/
structure DirectSparseAffineTablePhaseFamilies where
  triples : RecordFamily PeriodicCNF.UnaryProgramTokens.Token
  red : RecordFamily PeriodicCNF.UnaryProgramTokens.Token
  green : RecordFamily PeriodicCNF.UnaryProgramTokens.Token
  blue : RecordFamily PeriodicCNF.UnaryProgramTokens.Token
  triples_correct : ∀ symbols,
    recordsEmitted triples
        (PeriodicCNF.PolySpaceRequestEmitter.sourceTokens decider symbols) =
      directSparseComputedAffineTableTripleRequestsOfSymbols decider symbols
  red_correct : ∀ symbols,
    recordsEmitted red
        (PeriodicCNF.PolySpaceRequestEmitter.sourceTokens decider symbols) =
      directSparseComputedAffineTableElementRequestsOfSymbols
        decider .red symbols
  green_correct : ∀ symbols,
    recordsEmitted green
        (PeriodicCNF.PolySpaceRequestEmitter.sourceTokens decider symbols) =
      directSparseComputedAffineTableElementRequestsOfSymbols
        decider .green symbols
  blue_correct : ∀ symbols,
    recordsEmitted blue
        (PeriodicCNF.PolySpaceRequestEmitter.sourceTokens decider symbols) =
      directSparseComputedAffineTableElementRequestsOfSymbols
        decider .blue symbols

namespace DirectSparseAffineTablePhaseFamilies

def families (phases : DirectSparseAffineTablePhaseFamilies decider) :
    List (RecordFamily PeriodicCNF.UnaryProgramTokens.Token) :=
  [phases.triples, phases.red, phases.green, phases.blue]

/-- Named output function of the shared phase pipeline on the uniform source
token stream. -/
def output (phases : DirectSparseAffineTablePhaseFamilies decider)
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  emittedPhases phases.families
    (PeriodicCNF.PolySpaceRequestEmitter.sourceTokens decider symbols)

/-- The shared four-phase scan emits the complete combined table word. -/
theorem emitted_eq_table
    (phases : DirectSparseAffineTablePhaseFamilies decider)
    (symbols : List encoding.Γ) :
    output decider phases symbols =
      directSparseComputedAffineTableVertexRequestsOfSymbols
        decider symbols := by
  unfold output
  rw [emittedPhases_eq_phaseOutputs]
  simp only [families, phaseOutputs, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [phases.triples_correct, phases.red_correct,
    phases.green_correct, phases.blue_correct]
  rfl

end DirectSparseAffineTablePhaseFamilies

end PeriodicCNFStripReduction
end LeanTrominoes
