/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionBasicComputability

/-!
# Position computability for routed polarity normalization

This module certifies the scaled source placement, the two route-selected raw
positions, and the final fresh-variable gauge pointwise.  The function-valued
placement records themselves remain proof-neutral runtime parameters.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The refined placement period is primitive recursive in the source
placement period. -/
theorem refinedPlacement_period_primrec
    {Input : Type*} [Primcodable Input]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec fun input : Input =>
      (refinedPlacement
        ({ period := period input
           position := fun _ : Unit => (0, 0) } :
          PeriodicVariablePlacement Unit)).period := by
  exact (Primrec.nat_mul.comp
    (Primrec.const refinementFactor) periodPrimrec).of_eq fun _ => rfl

/-- Refined variable positions are primitive recursive whenever the source
position query is. -/
theorem refinedPlacement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (position : Input → Variable → Cell)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      position input.1 input.2) :
    Primrec fun input : Input × Variable =>
      (refinedPlacement
        ({ period := period input.1
           position := position input.1 } :
          PeriodicVariablePlacement Variable)).position input.2 := by
  exact (Computability.cell_scale_primrec.comp
    (Primrec.const (refinementFactor : Int)) positionPrimrec).of_eq
      fun _ => rfl

/-- A semantic offset translated by the refined placement is primitive
recursive in the unrefined period. -/
theorem refinedPlacement_translation_primrec
    {Input : Type*} [Primcodable Input]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec fun input : Input × Cell =>
      (refinedPlacement
        ({ period := period input.1
           position := fun _ : Unit => (0, 0) } :
          PeriodicVariablePlacement Unit)).translation input.2 := by
  have refinedPeriod : Primrec fun input : Input × Cell =>
      refinementFactor * period input.1 :=
    Primrec.nat_mul.comp (Primrec.const refinementFactor)
      (periodPrimrec.comp Primrec.fst)
  exact (Computability.cell_scale_primrec.comp
    (Computability.int_ofNat_primrec.comp refinedPeriod)
    Primrec.snd).of_eq fun _ => rfl

/-- The raw fresh-variable position selected at the first inserted route
vertex is primitive recursive. -/
theorem rawPositions_freshVariable_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : Input × FreshOccurrence Variable =>
      (rawPositions
        ({ period := period input.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable)
        (routes input.1)).freshVariable input.2 := by
  have selected : Primrec fun input : Input × FreshOccurrence Variable =>
      routePoint (routes input.1) input.2 1 :=
    (routePoint_primrec routes routesPrimrec).comp
      (Primrec.pair Primrec.id (Primrec.const 1))
  have offset : Primrec fun input : Input × FreshOccurrence Variable =>
      input.2.2.offset :=
    PeriodicThreeCNF.literal_offset_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have translated : Primrec fun input :
      Input × FreshOccurrence Variable =>
      (refinedPlacement
        ({ period := period input.1
           position := fun _ : Unit => (0, 0) } :
          PeriodicVariablePlacement Unit)).translation input.2.2.offset :=
    (refinedPlacement_translation_primrec period periodPrimrec).comp
      (Primrec.pair Primrec.fst offset)
  exact (Computability.cell_sub_primrec.comp selected translated).of_eq
    fun _ => rfl

/-- The raw complement-clause position selected at the second inserted route
vertex is primitive recursive. -/
theorem rawPositions_complementClause_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : Input × FreshOccurrence Variable =>
      (rawPositions
        ({ period := period input.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable)
        (routes input.1)).complementClause input.2 := by
  exact ((routePoint_primrec routes routesPrimrec).comp
    (Primrec.pair Primrec.id (Primrec.const 2))).of_eq fun _ => rfl

/-- The final gauge keeps original variables fixed and removes the retained
offset from every fresh complement variable. -/
theorem freshGauge_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (freshGauge : PolarityNormalizedVariable Variable → Cell) := by
  have freshOffset : Primrec fun fresh : FreshOccurrence Variable =>
      fresh.2.offset :=
    PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd
  have fresh : Primrec fun fresh : FreshOccurrence Variable =>
      Cell.sub (0, 0) fresh.2.offset :=
    Computability.cell_sub_primrec.comp
      (Primrec.const ((0, 0) : Cell)) freshOffset
  exact (Primrec.sumCasesOn Primrec.id
    (Primrec.const ((0, 0) : Cell)).to₂
    (fresh.comp Primrec.snd).to₂).of_eq fun atom => by
      cases atom <;> rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
