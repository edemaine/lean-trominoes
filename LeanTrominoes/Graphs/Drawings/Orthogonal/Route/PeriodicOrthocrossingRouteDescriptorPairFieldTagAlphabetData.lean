/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

/-! # Finite alphabet for route-descriptor pair field tags -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags

inductive Side
  | first
  | second
  deriving DecidableEq

/-- Unary units tagged by descriptor side and one of the eleven field
positions, with explicit pair boundaries. -/
inductive Token
  | pairStart
  | unit (side : Side) (field : Fin 11)
  | pairEnd
  deriving DecidableEq, Inhabited

def nextField (field : Fin 11) : Fin 11 :=
  ⟨(field.val + 1) % 11, Nat.mod_lt _ (by decide)⟩

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags
