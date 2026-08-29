/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalColumnStreamDefinitions

/-! # Row-major carrier fallback terminal-data block streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierFallbackTerminalData

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

abbrev IndexedCarrierEntry :=
  (CarrierNodeRankDatum × Nat) × Nat

/-- Selected carrier axes and natural spans in row-major rank order. -/
def selectedBlocks
    (entries : List IndexedCarrierEntry) : List (Bool × Nat) :=
  entries.flatMap fun first =>
    entries.flatMap fun second =>
      if CarrierRankOrderedPairs.retainedPredicate first second then
        [(first.1.1.horizontal,
          (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat)]
      else []

/-- Terminal data obtained directly from selected natural-span blocks. -/
def terminalData
    (entries : List IndexedCarrierEntry) :
    List PeriodicEightOccurrenceSplit.RetainedTerminalData :=
  (selectedBlocks entries).flatMap fun block =>
    carrierLensRouteTerminalDataBlock block.1 block.2

/-- Established sparse selected signed-span terminal-data blocks. -/
def selectedTerminalDataBlocks
    (entries : List IndexedCarrierEntry) :
    List (List PeriodicEightOccurrenceSplit.RetainedTerminalData) :=
  entries.flatMap fun first =>
    entries.filterMap fun second =>
      if CarrierRankOrderedPairs.retainedPredicate first second then
        some (CarrierRankOrderedPairs.retainedPairTerminalDataBlock
          first.1.1 second.1.1)
      else none

private theorem row_eq
    (entries : List IndexedCarrierEntry)
    (first : IndexedCarrierEntry) :
    (entries.flatMap fun second =>
      if CarrierRankOrderedPairs.retainedPredicate first second then
        carrierLensRouteTerminalDataBlock first.1.1.horizontal
          (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
      else []) =
      (entries.filterMap fun second =>
        if CarrierRankOrderedPairs.retainedPredicate first second then
          some (CarrierRankOrderedPairs.retainedPairTerminalDataBlock
            first.1.1 second.1.1)
        else none).flatten := by
  induction entries with
  | nil => rfl
  | cons second entries induction =>
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases retained :
          CarrierRankOrderedPairs.retainedPredicate first second with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        exact induction
      | true =>
        simp only [if_true, List.flatten_cons]
        have headEq :
            CarrierRankOrderedPairs.retainedPairTerminalDataBlock
                first.1.1 second.1.1 =
              carrierLensRouteTerminalDataBlock first.1.1.horizontal
                (second.1.1.orderCoordinate -
                  first.1.1.orderCoordinate).toNat := by
          rfl
        rw [headEq, induction]

/-- Flattening selected signed-span terminal blocks is identical to
flattening the corresponding selected natural-span singleton stream. -/
theorem rows_eq
    (entries rows : List IndexedCarrierEntry) :
    (rows.flatMap fun first =>
      entries.flatMap fun second =>
        if CarrierRankOrderedPairs.retainedPredicate first second then
          carrierLensRouteTerminalDataBlock first.1.1.horizontal
            (second.1.1.orderCoordinate -
              first.1.1.orderCoordinate).toNat
        else []) =
      (rows.flatMap fun first =>
        entries.filterMap fun second =>
          if CarrierRankOrderedPairs.retainedPredicate first second then
            some (CarrierRankOrderedPairs.retainedPairTerminalDataBlock
              first.1.1 second.1.1)
          else none).flatten := by
  induction rows with
  | nil => rfl
  | cons first rows induction =>
      simp only [List.flatMap_cons, List.flatten_append]
      rw [row_eq, induction]

/-- The natural-span selected presentation is exactly the flattening of the
established sparse signed-span terminal block stream. -/
theorem terminalData_eq_selectedTerminalDataBlocks
    (entries : List IndexedCarrierEntry) :
    terminalData entries = (selectedTerminalDataBlocks entries).flatten := by
  unfold terminalData selectedBlocks selectedTerminalDataBlocks
  rw [List.flatMap_assoc]
  have normalized :
      (entries.flatMap fun first =>
        (entries.flatMap fun second =>
          if CarrierRankOrderedPairs.retainedPredicate first second then
            [(first.1.1.horizontal,
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat)]
          else []).flatMap fun block =>
            carrierLensRouteTerminalDataBlock block.1 block.2) =
        (entries.flatMap fun first =>
          entries.flatMap fun second =>
            if CarrierRankOrderedPairs.retainedPredicate first second then
              carrierLensRouteTerminalDataBlock first.1.1.horizontal
                (second.1.1.orderCoordinate -
                  first.1.1.orderCoordinate).toNat
            else []) := by
    apply List.flatMap_congr
    intro first _firstMember
    rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro second _secondMember
    cases retained :
        CarrierRankOrderedPairs.retainedPredicate first second <;>
      simp
  rw [normalized]
  exact rows_eq entries entries

end CarrierFallbackTerminalData
end LeanTrominoes.PeriodicOrthocrossing
