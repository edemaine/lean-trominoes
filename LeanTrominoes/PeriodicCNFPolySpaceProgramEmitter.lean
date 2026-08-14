/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceFreshPrefixEmitter
import LeanTrominoes.PeriodicCNFPolySpaceOrdinaryEmitter

/-!
# Uniform normalized compact-request token emission

Compose the fresh-atom header, complete reset and ordinary branches, and the
outer Boolean closers.  One fixed finite machine handles every prepared source
word and emits exactly the finite token stream consumed by the verified unary
request finalizer.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceProgramEmitter

open AffineEmitterPipeline
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding
abbrev InputWorkspace := PolySpaceFreshPrefixEmitter.Workspace
  (encoding := encoding)
abbrev Data := PolySpaceOrdinaryEmitter.Data (encoding := encoding)
abbrev Workspace := PolySpaceOrdinaryEmitter.Workspace (encoding := encoding)

local instance symbolInhabited : Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedFresh⟩

/-- Operators closing the reset/ordinary disjunction and its conjunction with
structural well-formedness. -/
def outerEnding : List Token :=
  instructionTokens .disjoin ++ instructionTokens .conjoin

/-- Exact complete normalized bounded-machine program token stream. -/
def programTokens (symbols : List encoding.Γ) : List Token :=
  PolySpaceOrdinaryEmitter.emitted decider symbols ++ outerEnding

theorem programTokens_eq_ofProgram (symbols : List encoding.Γ) :
    programTokens decider symbols =
      ofProgram (PolySpaceProgramSpec.program decider symbols) := by
  unfold programTokens PolySpaceOrdinaryEmitter.emitted
    PolySpaceResetEmitter.emitted outerEnding PolySpaceProgramSpec.program
    BoundedMachineProgram.designatedMachineResetClock
  rw [PolySpaceOrdinaryEmitter.ordinaryTokens_eq_program,
    ofProgram_conjoin, ofProgram_disjoin]
  ac_rfl

/-- Exact finite request token stream, before clause counting and native-field
expansion. -/
def emitted (symbols : List encoding.Γ) : List Token :=
  PolySpaceFreshPrefixEmitter.emitted
      (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
    programTokens decider symbols

@[simp]
theorem emitted_eq_requestSource (symbols : List encoding.Γ) :
    emitted decider symbols =
      requestSource (PolySpaceProgramSpec.fresh decider symbols)
        (PolySpaceProgramSpec.program decider symbols) := by
  unfold emitted requestSource
  rw [PolySpaceFreshPrefixEmitter.emitted_preparedSources,
    programTokens_eq_ofProgram]
  ac_rfl

/-- The uniform input-preserving request emitter. -/
def run : List (InputWorkspace (encoding := encoding)) →
    List (Workspace (encoding := encoding)) :=
  fun workspace =>
    PolySpaceInitialStackScheduleEmitter.appendTokens outerEnding
      (PolySpaceOrdinaryEmitter.uniformRun decider
        (PolySpaceFreshPrefixEmitter.run (encoding := encoding) workspace))

noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id (run decider) := by
  let throughFresh := TM2CompositionMachine.computableInPolyTime
    (PolySpaceFreshPrefixEmitter.computableInPolyTime
      (encoding := encoding))
    (PolySpaceOrdinaryEmitter.uniformComputableInPolyTime decider)
  let complete := TM2CompositionMachine.computableInPolyTime throughFresh
    (PolySpaceInitialStackScheduleEmitter.appendTokensComputableInPolyTime
      (Item := Data (encoding := encoding)) outerEnding)
  exact complete

@[simp]
theorem extractTokens_run_embedData (symbols : List encoding.Γ) :
    extractTokens
        (run decider
          (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols))) =
      requestSource (PolySpaceProgramSpec.fresh decider symbols)
        (PolySpaceProgramSpec.program decider symbols) := by
  unfold run
  rw [PolySpaceInitialStackScheduleEmitter.appendTokens_eq,
    PolySpaceInitialStackScheduleEmitter.extractTokens_append,
    PolySpaceInitialStackScheduleEmitter.extractTokens_map_tokens,
    PolySpaceFreshPrefixEmitter.run_embedData,
    PolySpaceOrdinaryEmitter.extractTokens_uniformRun_embed_append_tokens]
  rw [← emitted_eq_requestSource decider symbols]
  unfold emitted programTokens
  ac_rfl

/-- Direct token-only behavior of the uniform emitter on a prepared word. -/
def tokensRun (word : List (Symbol (encoding := encoding))) : List Token :=
  extractTokens (run decider (embedData word))

@[simp]
theorem tokensRun_preparedSources (symbols : List encoding.Γ) :
    tokensRun decider
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      requestSource (PolySpaceProgramSpec.fresh decider symbols)
        (PolySpaceProgramSpec.program decider symbols) := by
  exact extractTokens_run_embedData decider symbols

noncomputable def tokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Symbol (encoding := encoding))) (List Token)
      (Symbol (encoding := encoding)) Token id id (tokensRun decider) := by
  let embedded := TM2CompositionMachine.computableInPolyTime
    (embedDataComputableInPolyTime (Data := Symbol (encoding := encoding)))
    (computableInPolyTime decider)
  let complete := TM2CompositionMachine.computableInPolyTime embedded
    (extractTokensComputableInPolyTime (Data := Data (encoding := encoding)))
  exact complete

end PolySpaceProgramEmitter
end PeriodicCNF
end LeanTrominoes
