/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagAlphabetData

/-! # Finite alphabet for occurrence-slot pair field tags -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

abbrev Side := RouteDescriptorPairFieldTags.Side

/-- Unary units tagged by pair side and one of twelve field positions.  The
first eleven positions are the descriptor fields and position eleven is the
fixed occurrence-slot index. -/
inductive Token
  | pairStart
  | unit (side : Side) (field : Fin 12)
  | pairEnd
  deriving DecidableEq, Inhabited

def nextField (field : Fin 12) : Fin 12 :=
  ⟨(field.val + 1) % 12, Nat.mod_lt _ (by decide)⟩

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
