/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Tactic.DeriveFintype
import LeanTrominoes.DelimitedBinaryWordPairFintypeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagControlData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagFintypeData

/-! # Finiteness of occurrence-slot pair tagger data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

instance tokenFintype : Fintype Token := derive_fintype% Token
instance controlFintype : Fintype Control := derive_fintype% Control

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
