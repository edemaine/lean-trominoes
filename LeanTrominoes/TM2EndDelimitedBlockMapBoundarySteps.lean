/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapConfigurations

/-! # Boundary-phase steps of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def pushBlockCfg (inner : FinTM2) (Source Target : Type)
    (symbol : Source) (input blockReverse : List Source)
    (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some (.pushBlock (.inl symbol)),
    ⟨inner.initialState, some symbol, none, true⟩,
    stackContents inner Source Target input blockReverse
      (emptyInnerStacks inner) outputReverse []⟩

def pushInnerCfg (inner : FinTM2) (Source Target : Type)
    (symbol : Source) (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some (.pushInner (.inl symbol)),
    ⟨inner.initialState, some symbol, none, true⟩,
    stackContents inner Source Target input blockReverse innerContents
      outputReverse []⟩

def pushOutputCfg (inner : FinTM2) (Source Target : Type)
    (symbol : Target) (input : List Source)
    (innerState : inner.σ)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (outputReverse : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some (.pushOutput (.inr symbol)),
    ⟨innerState, none, some symbol, true⟩,
    stackContents inner Source Target input [] innerContents
      outputReverse []⟩

def pushFinalCfg (inner : FinTM2) (Source Target : Type)
    (symbol : Target) (outputReverse output : List Target) :
    TM2.Cfg (Alphabet inner Source Target)
      (CombinedLabel inner Source Target)
      (CombinedState inner Source Target) :=
  ⟨some (.pushFinal (.inr symbol)),
    ⟨inner.initialState, none, some symbol, true⟩,
    stackContents inner Source Target [] [] (emptyInnerStacks inner)
      outputReverse output⟩

theorem step_collect_cons
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Source) (input blockReverse : List Source)
    (outputReverse : List Target) :
    (machine inner isEnd).step
        (collectCfg inner.tm Source Target (symbol :: input) blockReverse
          (emptyInnerStacks inner.tm) outputReverse) =
      some (pushBlockCfg inner.tm Source Target symbol input blockReverse
        outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, collectCfg,
    pushBlockCfg, initialState, stackContents, setSource, sourceIsNone,
    sourceValue]

theorem step_collect_nil
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (blockReverse : List Source) (outputReverse : List Target) :
    (machine inner isEnd).step
        (collectCfg inner.tm Source Target [] blockReverse
          (emptyInnerStacks inner.tm) outputReverse) =
      some (discardCfg inner.tm Source Target blockReverse outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, collectCfg,
    discardCfg, initialState, stackContents, setSource, sourceIsNone]

theorem step_pushBlock_end
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Source) (input blockReverse : List Source)
    (outputReverse : List Target) (ends : isEnd symbol = true) :
    (machine inner isEnd).step
        (pushBlockCfg inner.tm Source Target symbol input blockReverse
          outputReverse) =
      some (prepareCfg inner.tm Source Target input
        (symbol :: blockReverse) (emptyInnerStacks inner.tm)
        outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, pushBlockCfg,
    prepareCfg, initialState, stackContents, setSource, ends]

theorem step_pushBlock_continues
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Source) (input blockReverse : List Source)
    (outputReverse : List Target) (continues : isEnd symbol = false) :
    (machine inner isEnd).step
        (pushBlockCfg inner.tm Source Target symbol input blockReverse
          outputReverse) =
      some (collectCfg inner.tm Source Target input
        (symbol :: blockReverse) (emptyInnerStacks inner.tm)
        outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, pushBlockCfg,
    collectCfg, initialState, stackContents, setSource, continues]

theorem step_prepare_cons
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Source) (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target) :
    (machine inner isEnd).step
        (prepareCfg inner.tm Source Target input (symbol :: blockReverse)
          innerContents outputReverse) =
      some (pushInnerCfg inner.tm Source Target symbol input blockReverse
        innerContents outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, prepareCfg,
    pushInnerCfg, initialState, stackContents, setSource, sourceIsNone,
    sourceValue]

theorem step_pushInner
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Source) (input blockReverse : List Source)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target) :
    (machine inner isEnd).step
        (pushInnerCfg inner.tm Source Target symbol input blockReverse
          innerContents outputReverse) =
      some (prepareCfg inner.tm Source Target input blockReverse
        (Function.update innerContents inner.tm.k₀
          (inner.inputAlphabet.invFun symbol ::
            innerContents inner.tm.k₀))
        outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, pushInnerCfg,
    prepareCfg, initialState, stackContents, setSource]

end TM2EndDelimitedBlockMap
end LeanTrominoes
