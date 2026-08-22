/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # Configurations for the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def stackContents (inner : FinTM2) (Source Target : Type)
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse output : List Target) :
    ∀ stack, List (Alphabet inner Source Target stack)
  | .input => input
  | .blockReverse => blockReverse
  | .inner stack => innerContents stack
  | .outputReverse => outputReverse
  | .output => output

def emptyInnerStacks (inner : FinTM2) :
    ∀ stack, List (inner.Γ stack) :=
  fun _ => []

def collectCfg (inner : FinTM2) (Source Target : Type)
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some .collect, initialState inner Source Target,
    stackContents inner Source Target input blockReverse innerContents
      outputReverse []⟩

def prepareCfg (inner : FinTM2) (Source Target : Type)
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some .prepareBlock, initialState inner Source Target,
    stackContents inner Source Target input blockReverse innerContents
      outputReverse []⟩

def liftInnerCfg (inner : FinTM2) (Source Target : Type)
    (input : List Source) (outputReverse : List Target)
    (configuration : inner.Cfg) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) where
  l := match configuration.l with
    | some label => some (.inner label)
    | none => some .drainInnerOutput
  var :=
    ⟨configuration.var, none, none, true⟩
  stk := stackContents inner Source Target input [] configuration.stk
    outputReverse []

def drainOutputCfg (inner : FinTM2) (Source Target : Type)
    (input : List Source)
    (innerState : inner.σ)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some .drainInnerOutput, ⟨innerState, none, none, true⟩,
    stackContents inner Source Target input [] innerContents outputReverse []⟩

def cleanupCfg (inner : FinTM2) (Source Target : Type)
    (position : Fin (Fintype.card inner.K + 1))
    (input : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some (.cleanup position), initialState inner Source Target,
    stackContents inner Source Target input [] innerContents outputReverse []⟩

def discardCfg (inner : FinTM2) (Source Target : Type)
    (blockReverse : List Source) (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some .discardPartial, initialState inner Source Target,
    stackContents inner Source Target [] blockReverse (emptyInnerStacks inner)
      outputReverse []⟩

def reverseCfg (inner : FinTM2) (Source Target : Type)
    (outputReverse output : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some .reverseOutput, initialState inner Source Target,
    stackContents inner Source Target [] [] (emptyInnerStacks inner)
      outputReverse output⟩

def haltCfg (inner : FinTM2) (Source Target : Type)
    (output : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨none, initialState inner Source Target,
    stackContents inner Source Target [] [] (emptyInnerStacks inner) [] output⟩

@[simp] theorem update_stacks_input
    (inner : FinTM2) (Source Target : Type)
    (decEq : DecidableEq (Stack inner.K))
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse output : List Target) (value : List Source) :
    @Function.update _ _ decEq
        (stackContents inner Source Target input blockReverse innerContents
          outputReverse output)
        Stack.input value =
      stackContents inner Source Target value blockReverse innerContents
        outputReverse output := by
  funext stack
  cases stack <;> simp [stackContents, Function.update]

@[simp] theorem update_stacks_blockReverse
    (inner : FinTM2) (Source Target : Type)
    (decEq : DecidableEq (Stack inner.K))
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse output : List Target) (value : List Source) :
    @Function.update _ _ decEq
        (stackContents inner Source Target input blockReverse innerContents
          outputReverse output)
        Stack.blockReverse value =
      stackContents inner Source Target input value innerContents
        outputReverse output := by
  funext stack
  cases stack <;> simp [stackContents, Function.update]

@[simp] theorem update_stacks_inner
    (inner : FinTM2) (Source Target : Type)
    (decEq : DecidableEq (Stack inner.K))
    (innerDecEq : DecidableEq inner.K)
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse output : List Target)
    (target : inner.K) (value : List (inner.Γ target)) :
    @Function.update _ _ decEq
        (stackContents inner Source Target input blockReverse innerContents
          outputReverse output)
        (.inner target) value =
      stackContents inner Source Target input blockReverse
        (@Function.update _ _ innerDecEq innerContents target value)
        outputReverse output := by
  funext stack
  cases stack with
  | input | blockReverse | outputReverse | output => simp [stackContents]
  | inner stack =>
      by_cases equal : stack = target
      · subst stack
        simp [stackContents]
      · have taggedNe :
            (Stack.inner stack : Stack inner.K) ≠ .inner target := by
          intro taggedEq
          exact equal (Stack.inner.inj taggedEq)
        simp [stackContents, Function.update_of_ne equal,
          Function.update_of_ne taggedNe]

@[simp] theorem update_stacks_outputReverse
    (inner : FinTM2) (Source Target : Type)
    (decEq : DecidableEq (Stack inner.K))
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse output : List Target) (value : List Target) :
    @Function.update _ _ decEq
        (stackContents inner Source Target input blockReverse innerContents
          outputReverse output)
        Stack.outputReverse value =
      stackContents inner Source Target input blockReverse innerContents value
        output := by
  funext stack
  cases stack <;> simp [stackContents, Function.update]

@[simp] theorem update_stacks_output
    (inner : FinTM2) (Source Target : Type)
    (decEq : DecidableEq (Stack inner.K))
    (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse output : List Target) (value : List Target) :
    @Function.update _ _ decEq
        (stackContents inner Source Target input blockReverse innerContents
          outputReverse output)
        Stack.output value =
      stackContents inner Source Target input blockReverse innerContents
        outputReverse value := by
  funext stack
  cases stack <;> simp [stackContents, Function.update]

end TM2EndDelimitedBlockMap
end LeanTrominoes
