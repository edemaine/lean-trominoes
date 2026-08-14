/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFBivariateTemplateEmitterTime
import LeanTrominoes.PeriodicCNFMachineBivariateClockTemplates
import LeanTrominoes.PeriodicCNFMachineOneHotEmitterSpec
import LeanTrominoes.PeriodicCNFPolySpaceUnaryPreparedLayout

/-!
# Polynomial-time clock-reset emission for the PSPACE reduction

The bivariate pass emits every `not next(clockBit)` operand and the empty
conjunction constant.  A following affine pass emits one conjunction closer
per unary clock marker.  Both passes preserve the prepared input, so their
selector counts remain exact; after token extraction their composition is the
normalized bounded-machine clock-reset word.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceClockResetEmitter

open UnaryProgramTokens
open UnaryProgramTokenAlgebra
open AffineEmitterPipeline
open BoundedMachineOneHotEmitter
open BoundedMachineBivariateClock

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding
abbrev Workspace := AffineEmitterPipeline.Workspace (Symbol (encoding := encoding))

local instance symbolInhabited :
    Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedSpace⟩

/-- First pass: emit every clock-reset operand, followed by the constant-true
base case of the right-associated conjunction. -/
def operandRun (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  BivariateTemplateEmitterMachine.appendedOutput
    PolySpaceUnaryPreparedLayout.isSpace
    PolySpaceUnaryPreparedLayout.isClock
    (resetBit (tm := decider.tm)).recipes (allEnding 0) workspace

/-- Second pass: append one conjunction closer per unary clock marker. -/
def closingPhase : AffineEmitterPipeline.Phase
    (Symbol (encoding := encoding)) :=
  conjoinPhase PolySpaceUnaryPreparedLayout.isClock

/-- Complete input-preserving clock-reset pass. -/
def runWorkspace (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  (closingPhase (encoding := encoding)).run
    (operandRun decider workspace)

theorem bivariateSelectedCount_embedData
    (selected : Symbol (encoding := encoding) → Bool)
    (data : List (Symbol (encoding := encoding))) :
    BivariateTemplateEmitterMachine.selectedCount selected (embedData data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  change AffineTemplateEmitterMachine.selectedCount selected (embedData data) =
    UnaryPolynomialPaddingMachine.selectedCount selected data
  exact AffineEmitterPipeline.selectedCount_embedData selected data

theorem operandRun_embedData
    (data : List (Symbol (encoding := encoding))) :
    operandRun decider (embedData data) =
      embedData data ++
        (BivariateTemplateEmitterMachine.positionRangeTokens
            (resetBit (tm := decider.tm)).recipes
            (PolySpaceUnaryPreparedLayout.space data) 0
            (PolySpaceUnaryPreparedLayout.clockWidth data) ++
          allEnding 0).map Sum.inr := by
  unfold operandRun BivariateTemplateEmitterMachine.appendedOutput
  rw [bivariateSelectedCount_embedData,
    bivariateSelectedCount_embedData]
  rfl

theorem closingPhase_emitted
    (data : List (Symbol (encoding := encoding))) :
    (closingPhase (encoding := encoding)).emitted data =
      repeatInstructionTokens .conjoin
        (PolySpaceUnaryPreparedLayout.clockWidth data) := by
  apply conjoinPhase_emitted
  rfl

theorem allEnding_eq_base_append_closers (count : Nat) :
    allEnding count =
      allEnding 0 ++ repeatInstructionTokens .conjoin count := by
  simpa [allEnding] using foldEnding_add true .conjoin 0 count

/-- Exact token suffix produced from an arbitrary four-block input. -/
def emitted (data : List (Symbol (encoding := encoding))) : List Token :=
  clockResetTokens (tm := decider.tm)
    (PolySpaceUnaryPreparedLayout.space data)
    (PolySpaceUnaryPreparedLayout.clockWidth data)

theorem runWorkspace_embedData
    (data : List (Symbol (encoding := encoding))) :
    runWorkspace decider (embedData data) =
      embedData data ++
        (emitted decider data).map Sum.inr := by
  unfold runWorkspace
  rw [operandRun_embedData]
  rw [AffineEmitterPipeline.Phase.run_embed_append_tokens]
  rw [closingPhase_emitted]
  unfold emitted clockResetTokens
  rw [allEnding_eq_base_append_closers
    (PolySpaceUnaryPreparedLayout.clockWidth data)]
  simp [List.map_append, List.append_assoc]

@[simp]
theorem extractTokens_runWorkspace_embedData
    (data : List (Symbol (encoding := encoding))) :
    extractTokens (runWorkspace decider (embedData data)) =
      emitted decider data := by
  rw [runWorkspace_embedData]
  unfold extractTokens embedData
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]
  simp

/-- The two input-preserving passes are polynomial-time on their shared
workspace alphabet. -/
noncomputable def runWorkspaceComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding)) (Workspace (encoding := encoding))
      id id (runWorkspace decider) := by
  let operands :=
    BivariateTemplateEmitterMachine.computableInPolyTime
      (Data := Symbol (encoding := encoding))
      PolySpaceUnaryPreparedLayout.isSpace
      PolySpaceUnaryPreparedLayout.isClock
      (resetBit (tm := decider.tm)).recipes (allEnding 0)
  let closers :=
    (closingPhase (encoding := encoding)).computableInPolyTime
  let combined := TM2CompositionMachine.computableInPolyTime operands closers
  refine
    { tm := combined.tm
      inputAlphabet := combined.inputAlphabet
      outputAlphabet := combined.outputAlphabet
      time := combined.time
      outputsFun := ?_ }
  intro workspace
  exact combined.outputsFun workspace

/-- Embed the prepared input once, emit and close all clock-reset operands,
then delete the retained input. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Symbol (encoding := encoding))) (List Token)
      (Symbol (encoding := encoding)) Token id id (emitted decider) := by
  let first := TM2CompositionMachine.computableInPolyTime
    (embedDataComputableInPolyTime
      (Data := Symbol (encoding := encoding)))
    (runWorkspaceComputableInPolyTime decider)
  let complete := TM2CompositionMachine.computableInPolyTime first
    (extractTokensComputableInPolyTime
      (Data := Symbol (encoding := encoding)))
  refine
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := ?_ }
  intro data
  have run := complete.outputsFun data
  rw [extractTokens_runWorkspace_embedData] at run
  exact run

/-- On the actual prepared source word, the verified machine emits precisely
the normalized clock-reset program at the reduction's runtime widths. -/
theorem emitted_preparedSources (symbols : List encoding.Γ) :
    emitted decider
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      ofProgram
        (BoundedMachineProgram.clockReset (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)) :=
  by
  unfold emitted
  rw [PolySpaceUnaryPreparedLayout.space_preparedSources,
    PolySpaceUnaryPreparedLayout.clockWidth_preparedSources,
    clockResetTokens_eq]

end PolySpaceClockResetEmitter
end PeriodicCNF
end LeanTrominoes
