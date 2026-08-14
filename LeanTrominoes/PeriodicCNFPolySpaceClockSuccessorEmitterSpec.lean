/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterTime
import LeanTrominoes.PeriodicCNFPolySpaceClockResetEmitterSpec

/-!
# Polynomial-time clock-successor emission for the PSPACE reduction

The generic triangular emitter is specialized to the verified rise, bit
equality, and fall recipes.  On a prepared four-block input its exact token
suffix is the normalized bounded-machine clock-successor program, and the
input-preserving workspace pass plus embedding/extraction is polynomial-time.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceClockSuccessorEmitter

open UnaryProgramTokens
open UnaryProgramTokenAlgebra
open AffineEmitterPipeline
open BoundedMachineOneHotEmitter
open BoundedMachineBivariateClockSuccessor

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

/-- Fixed triangular-machine parameters realizing clock succession. -/
def parameters : TriangularTemplateEmitterMachine.Parameters
    (Symbol (encoding := encoding)) where
  firstSelected := PolySpaceUnaryPreparedLayout.isSpace
  secondSelected := PolySpaceUnaryPreparedLayout.isClock
  outerFirst := (rise (tm := decider.tm)).recipes
  inner := (equalBit (tm := decider.tm)).recipes
  outerSecond := (fall (tm := decider.tm)).recipes
  innerBase := ofProgram (TransitionProgram.constant true)
  innerCloser := ofProgram [.conjoin]
  frameCloser := ofProgram [.conjoin]
  finalBase := ofProgram (TransitionProgram.constant false)
  finalCloser := ofProgram [.conjoin, .disjoin]

/-- Complete input-preserving clock-successor workspace pass. -/
def runWorkspace (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  TriangularTemplateEmitterMachine.appendedOutput
    (parameters decider).firstSelected (parameters decider).secondSelected
    (parameters decider).outerFirst (parameters decider).inner
    (parameters decider).outerSecond (parameters decider).innerBase
    (parameters decider).innerCloser (parameters decider).frameCloser
    (parameters decider).finalBase (parameters decider).finalCloser workspace

theorem selectedCount_embedData
    (selected : Symbol (encoding := encoding) → Bool)
    (data : List (Symbol (encoding := encoding))) :
    TriangularTemplateEmitterMachine.selectedCount selected (embedData data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  change AffineTemplateEmitterMachine.selectedCount selected (embedData data) =
    UnaryPolynomialPaddingMachine.selectedCount selected data
  exact AffineEmitterPipeline.selectedCount_embedData selected data

/-- Exact clock-successor suffix for an arbitrary prepared-shape word. -/
def emitted (data : List (Symbol (encoding := encoding))) : List Token :=
  clockSuccessorTokens (tm := decider.tm)
    (PolySpaceUnaryPreparedLayout.space data)
    (PolySpaceUnaryPreparedLayout.clockWidth data)

theorem runWorkspace_embedData
    (data : List (Symbol (encoding := encoding))) :
    runWorkspace decider (embedData data) =
      embedData data ++ (emitted decider data).map Sum.inr := by
  unfold runWorkspace TriangularTemplateEmitterMachine.appendedOutput
  rw [selectedCount_embedData, selectedCount_embedData]
  change embedData data ++
      (TriangularTemplateEmitter.emitted
        (rise (tm := decider.tm)).recipes
        (equalBit (tm := decider.tm)).recipes
        (fall (tm := decider.tm)).recipes
        (ofProgram (TransitionProgram.constant true))
        (ofProgram [.conjoin]) (ofProgram [.conjoin])
        (ofProgram (TransitionProgram.constant false))
        (ofProgram [.conjoin, .disjoin])
        (PolySpaceUnaryPreparedLayout.space data)
        (PolySpaceUnaryPreparedLayout.clockWidth data)).map Sum.inr = _
  rw [TriangularTemplateEmitter.emitted_clockSuccessor]
  rfl

@[simp]
theorem extractTokens_runWorkspace_embedData
    (data : List (Symbol (encoding := encoding))) :
    extractTokens (runWorkspace decider (embedData data)) =
      emitted decider data := by
  rw [runWorkspace_embedData]
  unfold extractTokens embedData
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]
  simp

/-- The input-preserving clock-successor pass is polynomial-time. -/
noncomputable def runWorkspaceComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding)) (Workspace (encoding := encoding))
      id id (runWorkspace decider) := by
  exact TriangularTemplateEmitterMachine.computableInPolyTime
    (parameters decider)

/-- Embed the prepared input once, emit clock succession, then extract only
the generated tokens. -/
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

/-- On the actual prepared source word, the machine emits precisely the
normalized clock-successor program at the reduction's runtime widths. -/
theorem emitted_preparedSources (symbols : List encoding.Γ) :
    emitted decider
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      ofProgram
        (BoundedMachineProgram.clockSuccessor (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)) :=
  by
  unfold emitted
  rw [PolySpaceUnaryPreparedLayout.space_preparedSources,
    PolySpaceUnaryPreparedLayout.clockWidth_preparedSources,
    clockSuccessorTokens_eq]

end PolySpaceClockSuccessorEmitter
end PeriodicCNF
end LeanTrominoes
