/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapBlockExecution

/-! # Data for complete end-delimited block-map executions -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

section

variable {Source Target : Type}
variable [Fintype Source] [Fintype Target]
variable [Inhabited Source] [Inhabited Target]
variable {function : List Source → List Target}

/-- Exact recursive bound used by the complete execution proof. -/
def mapRunTime (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) :
    List Source → List Source → List Target → Nat
  | [], blockReverse, outputReverse =>
      (2 * outputReverse.length + 1) + (blockReverse.length + 1) + 1
  | symbol :: input, blockReverse, outputReverse =>
      if isEnd symbol then
        let block := (symbol :: blockReverse).reverse
        mapRunTime inner isEnd input []
            ((function block).reverse ++ outputReverse) +
          (blockRunTime inner block + 2)
      else
        mapRunTime inner isEnd input (symbol :: blockReverse)
          outputReverse + 2

theorem initialStacks_eq_initList
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (input : List Source) :
    stackContents inner.tm Source Target input []
        (emptyInnerStacks inner.tm) [] [] =
      (initList (machine inner isEnd) input).stk := by
  funext stack
  cases stack <;>
    simp [stackContents, emptyInnerStacks, initList, machine]

theorem collectCfg_eq_initList
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool) (input : List Source) :
    collectCfg inner.tm Source Target input []
        (emptyInnerStacks inner.tm) [] =
      initList (machine inner isEnd) input := by
  rw [collectCfg, initialStacks_eq_initList inner isEnd input]
  rfl

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
