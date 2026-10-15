/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Basic

namespace LeanTrominoes.CompletionPattern

/-- Bits are ordered top left, top right, bottom left, bottom right. -/
def state4 (a b c d : Bool) : Fin 16 :=
  ⟨(if a then 8 else 0) + (if b then 4 else 0) +
    (if c then 2 else 0) + (if d then 1 else 0), by cases a <;> cases b <;> cases c <;> cases d <;> decide⟩

/-- Bits are ordered top, bottom. -/
def state2 (a b : Bool) : Fin 4 :=
  ⟨(if a then 2 else 0) + (if b then 1 else 0), by cases a <;> cases b <;> decide⟩

end LeanTrominoes.CompletionPattern
