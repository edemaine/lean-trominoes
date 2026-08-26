/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalValidity

/-! # Global key-major stable carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

abbrev InputEncoding := CarrierRankKeyEquality.InputEncoding

def additionInput (descriptors : List RouteDescriptor) :
    UnaryAlignedAddMachine.Input where
  firsts := CarrierRankKeyBlockStarts.starts descriptors
  seconds := CarrierRankStableLower.ranks descriptors
  valid := CarrierRankGlobalValidity.valid descriptors

/-- Last-occurrence-ordered key-block start plus stable geometric rank within
that key, for every compact carrier datum. -/
def ranks (descriptors : List RouteDescriptor) : List Nat :=
  UnaryAlignedAddMachine.sums
    (CarrierRankKeyBlockStarts.starts descriptors)
    (CarrierRankStableLower.ranks descriptors)

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
