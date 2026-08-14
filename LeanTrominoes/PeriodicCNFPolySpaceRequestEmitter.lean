/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceProgramEmitter
import LeanTrominoes.PeriodicCNFUnaryProgramTokenFinalizer

/-!
# Complete source-uniform compact-request generation

Compose prepared-word construction, normalized finite-token emission, exact
clause counting and header rotation, and unary-field encoding.  The resulting
fixed finite machine maps every source-symbol word to the exact native compact
request consumed by the verified transition evaluator.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceRequestEmitter

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

abbrev PreparedSymbol := PolySpaceUnaryPreparedLayout.Symbol encoding

/-- Token output after uniform source preparation and normalized program
emission. -/
def sourceTokens (symbols : List encoding.Γ) :
    List UnaryProgramTokens.Token :=
  PolySpaceProgramEmitter.tokensRun decider
    (PolySpaceUnaryPreparedLayout.preparedSources decider symbols)

@[simp]
theorem sourceTokens_eq_requestSource (symbols : List encoding.Γ) :
    sourceTokens decider symbols =
      UnaryProgramTokens.requestSource
        (PolySpaceProgramSpec.fresh decider symbols)
        (PolySpaceProgramSpec.program decider symbols) := by
  exact PolySpaceProgramEmitter.tokensRun_preparedSources decider symbols

noncomputable def sourceTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List UnaryProgramTokens.Token)
      encoding.Γ UnaryProgramTokens.Token id id
      (sourceTokens decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (PolySpaceUnaryPreparedLayout.preparedComputableInPolyTime decider)
    (PolySpaceProgramEmitter.tokensComputableInPolyTime decider)
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List UnaryProgramTokens.Token)
    encoding.Γ UnaryProgramTokens.Token id id
    (fun symbols =>
      PolySpaceProgramEmitter.tokensRun decider
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols))
  exact composed

/-- Delimiter-terminated unary request fields after exact clause counting. -/
def sourceUnaryRequest (symbols : List encoding.Γ) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryProgramTokenFinalizer.countAndFinalize (sourceTokens decider symbols)

@[simp]
theorem sourceUnaryRequest_eq_unaryFields (symbols : List encoding.Γ) :
    sourceUnaryRequest decider symbols =
      UnaryFieldEncoderMachine.unaryFields
        (PolySpaceProgramSpec.fields decider symbols) := by
  unfold sourceUnaryRequest
  rw [sourceTokens_eq_requestSource,
    UnaryProgramTokenFinalizer.countAndFinalize_requestSource]
  rfl

noncomputable def sourceUnaryRequestComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List UnaryFieldEncoderMachine.Symbol)
      encoding.Γ UnaryFieldEncoderMachine.Symbol id id
      (sourceUnaryRequest decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (sourceTokensComputableInPolyTime decider)
    UnaryProgramTokenFinalizer.countAndFinalizeComputableInPolyTime
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List UnaryFieldEncoderMachine.Symbol)
    encoding.Γ UnaryFieldEncoderMachine.Symbol id id
    (fun symbols =>
      UnaryProgramTokenFinalizer.countAndFinalize
        (sourceTokens decider symbols))
  exact composed

/-- Reinterpret the exact unary output as an encoding of the normalized
natural request fields. -/
noncomputable def unaryFieldsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol id
      UnaryFieldEncoderMachine.unaryFields
      (PolySpaceProgramSpec.fields decider) := by
  let raw := sourceUnaryRequestComputableInPolyTime decider
  refine
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := ?_ }
  intro symbols
  simpa only [id_eq, sourceUnaryRequest_eq_unaryFields] using
    raw.outputsFun symbols

/-- The normalized request fields in the evaluator's canonical native natural
encoding. -/
noncomputable def nativeFieldsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ PartrecToTM2.Γ' id PartrecToTM2.trList
      (PolySpaceProgramSpec.fields decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (unaryFieldsComputableInPolyTime decider)
    UnaryFieldEncoderMachine.computableInPolyTime
  simpa only [id_eq] using composed

/-- Complete direct source request generator expected by the verified
transition evaluator. -/
noncomputable def sourceRequestComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      TransitionEvaluatorMachine.TransitionCompilerRequest
      encoding.Γ PartrecToTM2.Γ' id
      TransitionEvaluatorMachine.TransitionCompilerRequest.encode
      (PolySpaceNativeCompiler.sourceCompilerRequest decider) := by
  let fields := nativeFieldsComputableInPolyTime decider
  refine
    { tm := fields.tm
      inputAlphabet := fields.inputAlphabet
      outputAlphabet := fields.outputAlphabet
      time := fields.time
      outputsFun := ?_ }
  intro symbols
  simpa only [id_eq, PolySpaceProgramSpec.trList_fields] using
    fields.outputsFun symbols

end PolySpaceRequestEmitter
end PeriodicCNF
end LeanTrominoes
