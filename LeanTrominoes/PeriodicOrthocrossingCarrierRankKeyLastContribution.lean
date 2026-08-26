/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRankValidity

/-! # Last-occurrence contributions of compiled carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyLastContributions

/-- Stable key-occurrence ranks paired with their full multiplicities. -/
def filterInput (descriptors : List RouteDescriptor) :
    UnarySuccessorEqualityFilterMachine.Input where
  ranks := CarrierRankKeyOccurrenceRanks.ranks descriptors
  sizes := CarrierRankKeyGroupSizes.sizes descriptors
  valid := CarrierRankKeyRankValidity.valid descriptors

/-- Retain each key's full multiplicity exactly at its final presentation. -/
def contributions (descriptors : List RouteDescriptor) : List Nat :=
  UnarySuccessorEqualityFilterMachine.selectedValues
    (CarrierRankKeyOccurrenceRanks.ranks descriptors)
    (CarrierRankKeyGroupSizes.sizes descriptors)

end CarrierRankKeyLastContributions
end LeanTrominoes.PeriodicOrthocrossing
