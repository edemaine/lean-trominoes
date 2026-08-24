/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Semantics of compiler-facing carrier-node rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The compiler-facing datum projection is globally injective because it
retains the finite source-node identity used by deduplication. -/
theorem carrierNodeRankDatumAtPeriod_injective (period : Nat) :
    Function.Injective (carrierNodeRankDatumAtPeriod period) := by
  intro first second equal
  exact congrArg CarrierNodeRankDatum.identity equal

@[simp] theorem carrierNodeRankDatumAtPeriod_sameCrossoverSite
    (period : Nat) (first second : CarrierNode) :
    (carrierNodeRankDatumAtPeriod period first).sameCrossoverSite
        (carrierNodeRankDatumAtPeriod period second) =
      first.sameCrossoverSite second := by
  cases first with
  | boundary firstBoundary =>
      cases second with
      | boundary secondBoundary => rfl
      | terminal secondTerminal => rfl
  | terminal firstTerminal =>
      cases second <;> rfl

@[simp] theorem carrierNodeRankDatumAtPeriod_pairRepresentativeShift
    (period : Nat) (first second : CarrierNode) :
    (carrierNodeRankDatumAtPeriod period first).pairRepresentativeShift
        (carrierNodeRankDatumAtPeriod period second) =
      carrierNodePairRepresentativeShiftAtPeriod period (first, second) := by
  cases first with
  | boundary firstBoundary => rfl
  | terminal firstTerminal =>
      cases second <;> rfl

@[simp] theorem carrierNodeRankDatumAtPeriod_pairIsRepresentative
    (period : Nat) (first second : CarrierNode) :
    (carrierNodeRankDatumAtPeriod period first).pairIsRepresentative
        (carrierNodeRankDatumAtPeriod period second) =
      decide
        (CarrierNodePairIsRepresentativeAtPeriod
          period (first, second)) := by
  simp [CarrierNodeRankDatum.pairIsRepresentative,
    CarrierNodePairIsRepresentativeAtPeriod]

@[simp] theorem carrierNodeRankDatumAtPeriod_pairNextSlice
    (period : Nat) (first second : CarrierNode) :
    (carrierNodeRankDatumAtPeriod period first).pairNextSlice
        (carrierNodeRankDatumAtPeriod period second) =
      carrierNodePairNextSliceAtPeriod period (first, second) := by
  rfl

@[simp] theorem carrierNodeRankDatumAtPeriod_pairBits
    (period : Nat) (first second : CarrierNode) :
    (carrierNodeRankDatumAtPeriod period first).pairBits
        (carrierNodeRankDatumAtPeriod period second) =
      (first.isHorizontal,
        carrierNodePairNextSliceAtPeriod period (first, second)) := by
  rfl

end LeanTrominoes.PeriodicOrthocrossing
