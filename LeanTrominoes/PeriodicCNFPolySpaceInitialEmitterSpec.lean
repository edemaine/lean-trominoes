/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceResetPrefixEmitter

/-!
# Source-dependent initial-configuration emitter specification

The reset branch next tests the source-dependent initial configuration.  Only
the input stack has a nonempty occupied prefix: its cells are the decoded
finite source symbols in order.  Every remaining represented cell, and every
cell of every other stack, is `none`.  This file exposes that split as the
exact postorder token schedule to be implemented by the next counter machine.
-/

noncomputable section

namespace LeanTrominoes

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace PolySpaceInitialEmitter

open AffineEmitterPipeline
open BoundedMachineAtom
open BoundedMachineFixedConfigurationEmitter
open BoundedMachineOneHotEmitter
open SelectedPrefixMarkerMachine
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding

def target (symbols : List encoding.Γ) : decider.tm.Cfg :=
  PolySpaceCompiler.initialConfigurationOfSymbols decider symbols

def space (symbols : List encoding.Γ) : Nat :=
  PolySpaceCompiler.spaceOfSymbols decider symbols

@[simp]
theorem target_stack_input (symbols : List encoding.Γ) :
    (target decider symbols).stk decider.tm.k₀ =
      symbols.map decider.inputAlphabet.invFun := by
  simp [target, PolySpaceCompiler.initialConfigurationOfSymbols, initList]

theorem target_stack_other (symbols : List encoding.Γ)
    (stack : decider.tm.K) (different : stack ≠ decider.tm.k₀) :
    (target decider symbols).stk stack = [] := by
  simp [target, PolySpaceCompiler.initialConfigurationOfSymbols,
    initList, different]

theorem sourceLength_le_space (symbols : List encoding.Γ) :
    symbols.length ≤ space decider symbols := by
  unfold space PolySpaceCompiler.spaceOfSymbols
  omega

/-- Literal occupied-prefix cells of the input stack, with their source symbol
decoded by the fixed input-alphabet equivalence. -/
def sourcePrefixTokens (symbols : List encoding.Γ) : List Token :=
  (List.range symbols.length).flatMap fun position =>
    ofProgram
      (stackCellIs (tm := decider.tm) .next decider.tm.k₀ position
        (symbols[position]?.map decider.inputAlphabet.invFun))

@[simp]
theorem sourcePrefixTokens_eq (symbols : List encoding.Γ) :
    sourcePrefixTokens decider symbols =
      stackPrefixTokens (tm := decider.tm) .next
        (target decider symbols) decider.tm.k₀ := by
  unfold sourcePrefixTokens stackPrefixTokens
  rw [target_stack_input]
  simp only [List.length_map]
  apply List.flatMap_congr
  intro position membership
  rw [List.getElem?_map]

/-- `none` cells beginning at a specified occupied-prefix length. -/
def emptyTailTokens (stack : decider.tm.K) (prefixLength count : Nat) :
    List Token :=
  (List.range count).flatMap fun offset =>
    ofProgram
      (stackCellIs (tm := decider.tm) .next stack
        (prefixLength + offset) none)

/-- Complete postorder token schedule for one initial stack: occupied prefix,
empty tail, the empty conjunction base, and every conjunction closer. -/
def stackSchedule (symbols : List encoding.Γ) (stack : decider.tm.K) :
    List Token :=
  let prefixLength := ((target decider symbols).stk stack).length
  stackPrefixTokens (tm := decider.tm) .next
      (target decider symbols) stack ++
    emptyTailTokens decider stack prefixLength
      (space decider symbols - prefixLength) ++
    allEnding prefixLength ++
    repeatInstructionTokens .conjoin
      (space decider symbols - prefixLength)

theorem targetStackFitsSpace (symbols : List encoding.Γ)
    (stack : decider.tm.K) :
    ((target decider symbols).stk stack).length ≤ space decider symbols := by
  by_cases equal : stack = decider.tm.k₀
  · subst equal
    rw [target_stack_input, List.length_map]
    exact sourceLength_le_space decider symbols
  · rw [target_stack_other decider symbols stack equal]
    simp

/-- The exposed per-stack schedule is exactly the normalized bounded stack
test. -/
theorem stackSchedule_eq (symbols : List encoding.Γ)
    (stack : decider.tm.K) :
    stackSchedule decider symbols stack =
      ofProgram
        (stackIs (tm := decider.tm) .next
          (target decider symbols) stack (space decider symbols)) := by
  let prefixLength := ((target decider symbols).stk stack).length
  have fits : prefixLength ≤ space decider symbols :=
    targetStackFitsSpace decider symbols stack
  have operands := stackOperandTokens_split (tm := decider.tm)
    .next (target decider symbols) stack (space decider symbols) fits
  have ending : allEnding (space decider symbols) =
      allEnding prefixLength ++
        repeatInstructionTokens .conjoin
          (space decider symbols - prefixLength) := by
    calc
      allEnding (space decider symbols) =
          allEnding (prefixLength +
            (space decider symbols - prefixLength)) := by congr 1; omega
      _ = _ := by
        simpa [allEnding] using
          foldEnding_add true .conjoin prefixLength
            (space decider symbols - prefixLength)
  unfold stackSchedule emptyTailTokens stackIs
  change stackPrefixTokens (tm := decider.tm) .next
        (target decider symbols) stack ++
      (List.range (space decider symbols - prefixLength)).flatMap
        (fun offset =>
          ofProgram (stackCellIs (tm := decider.tm) .next stack
            (prefixLength + offset) none)) ++
      allEnding prefixLength ++
      repeatInstructionTokens .conjoin
        (space decider symbols - prefixLength) = _
  rw [ofProgram_all, List.length_map, List.length_finRange,
    operands, ending]
  simp only [prefixLength, Nat.add_comm]
  ac_rfl

/-- Exact full next-initial endpoint schedule, including the fixed label and
control fields and both levels of conjunction folding. -/
def schedule (symbols : List encoding.Γ) : List Token :=
  ofProgram
      (labelIs (tm := decider.tm) .next (target decider symbols).l) ++
    ofProgram
      (controlIs (tm := decider.tm) .next (target decider symbols).var) ++
    (finiteValues decider.tm.K).flatMap
      (stackSchedule decider symbols) ++
    allEnding (Fintype.card decider.tm.K) ++
    instructionTokens .conjoin ++ instructionTokens .conjoin

/-- The finite schedule is precisely the normalized source-dependent
`nextConfigIs` word needed by the reset branch. -/
theorem schedule_eq (symbols : List encoding.Γ) :
    schedule decider symbols =
      ofProgram
        (BoundedMachineProgram.nextConfigIs (tm := decider.tm)
          (space := space decider symbols) (target decider symbols)) := by
  rw [← configurationIs_next]
  unfold schedule configurationIs
  rw [ofProgram_conjoin, ofProgram_conjoin, ofProgram_all,
    List.length_map, finiteValues_length]
  have stackWords :
      (finiteValues decider.tm.K).flatMap (stackSchedule decider symbols) =
        ((finiteValues decider.tm.K).map fun stack =>
          stackIs (tm := decider.tm) .next
            (target decider symbols) stack
            (space decider symbols)).flatMap ofProgram := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro stack _
    exact stackSchedule_eq decider symbols stack
  rw [stackWords]
  ac_rfl

end PolySpaceInitialEmitter
end PeriodicCNF
end LeanTrominoes
