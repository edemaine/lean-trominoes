/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteNatHorizontalCursor

/-! # Complement-counter raster route cursor

The route-record machine stores a horizontal coordinate together with the
number of remaining positions before wraparound.  East and west steps then
move one unary unit between the two counters, with whole-counter swaps only
at the two boundaries.
-/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

theorem natHorizontalLocation_ext
    {first second : NatHorizontalLocation}
    (horizontal : first.horizontal = second.horizontal)
    (vertical : first.vertical = second.vertical) : first = second := by
  rcases first with ⟨firstHorizontal, firstVertical⟩
  rcases second with ⟨secondHorizontal, secondVertical⟩
  simp_all

structure ComplementLocation where
  horizontal : Nat
  horizontalComplement : Nat
  vertical : Int
  deriving DecidableEq, Repr

def ComplementLocation.period (location : ComplementLocation) : Nat :=
  location.horizontal + location.horizontalComplement + 1

def ComplementLocation.toNatHorizontal
    (location : ComplementLocation) : NatHorizontalLocation :=
  ⟨location.horizontal, location.vertical⟩

/-- One constant-local counter transition. -/
def advanceComplementLocation
    (location : ComplementLocation) :
    AxisDirection → ComplementLocation
  | .east =>
      if location.horizontalComplement = 0 then
        ⟨0, location.horizontal, location.vertical⟩
      else
        ⟨location.horizontal + 1,
          location.horizontalComplement - 1, location.vertical⟩
  | .west =>
      if location.horizontal = 0 then
        ⟨location.horizontalComplement, 0, location.vertical⟩
      else
        ⟨location.horizontal - 1,
          location.horizontalComplement + 1, location.vertical⟩
  | .north =>
      { location with vertical := location.vertical - 1 }
  | .south =>
      { location with vertical := location.vertical + 1 }
  | .invalid => location

/-- Every counter transition preserves the represented horizontal period. -/
@[simp] theorem advanceComplementLocation_period
    (location : ComplementLocation) (direction : AxisDirection) :
    (advanceComplementLocation location direction).period =
      location.period := by
  rcases location with ⟨horizontal, complement, vertical⟩
  cases direction <;>
    simp [advanceComplementLocation, ComplementLocation.period] <;>
    split <;> simp_all <;> omega

/-- Complement movement implements the exact natural-horizontal modular
transition. -/
@[simp] theorem advanceComplementLocation_toNatHorizontal
    (location : ComplementLocation) (direction : AxisDirection) :
    (advanceComplementLocation location direction).toNatHorizontal =
      advanceNatHorizontalLocation location.period
        location.toNatHorizontal direction := by
  rcases location with ⟨horizontal, complement, vertical⟩
  have horizontalRemainder :
      (((horizontal : Int) % (horizontal + complement + 1 : Nat)).toNat) =
        horizontal := by
    rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
    simp
  simp only [Nat.cast_add, Nat.cast_one] at horizontalRemainder
  cases direction <;> simp only [advanceComplementLocation]
  · -- east
      split
      · rename_i complementZero
        subst complement
        simp [ComplementLocation.toNatHorizontal,
          ComplementLocation.period, advanceNatHorizontalLocation,
          PeriodicThreeDM.stripDirectionStep]
      · rename_i complementNe
        have complementPositive : 0 < complement :=
          Nat.pos_of_ne_zero complementNe
        have remainderToNat :
            ((((horizontal : Int) + 1) %
                (horizontal + complement + 1 : Nat)).toNat) =
              horizontal + 1 := by
          rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Int.toNat_natCast (horizontal + 1))
        simp only [Nat.cast_add, Nat.cast_one] at remainderToNat
        simp [ComplementLocation.toNatHorizontal,
          ComplementLocation.period, advanceNatHorizontalLocation,
          PeriodicThreeDM.stripDirectionStep, remainderToNat]
  · -- north
    simp only [ComplementLocation.toNatHorizontal,
      ComplementLocation.period, advanceNatHorizontalLocation,
      PeriodicThreeDM.stripDirectionStep]
    apply natHorizontalLocation_ext
    · exact horizontalRemainder.symm
    · ring
  · -- west
      split
      · rename_i horizontalZero
        subst horizontal
        have remainderToNat :
            (((-1 : Int) % (complement + 1 : Nat)).toNat) = complement := by
          have remainder :
              ((-1 : Int) % (complement + 1 : Nat)) = complement := by
            have complementRemainder :
                ((complement : Int) % (complement + 1 : Nat)) =
                  complement :=
              Int.emod_eq_of_lt (by omega) (by push_cast; omega)
            have shifted := Int.emod_eq_sub_self_emod
              (a := (complement : Int))
              (b := (complement + 1 : Nat))
            calc
              (-1 : Int) % (complement + 1 : Nat) =
                  ((complement : Int) - (complement + 1 : Nat)) %
                    (complement + 1 : Nat) := by
                    congr 2
                    push_cast
                    omega
              _ = (complement : Int) % (complement + 1 : Nat) :=
                shifted.symm
              _ = complement := complementRemainder
          rw [remainder]
          simp
        simp only [Nat.cast_add, Nat.cast_one] at remainderToNat
        simp [ComplementLocation.toNatHorizontal,
          ComplementLocation.period, advanceNatHorizontalLocation,
          PeriodicThreeDM.stripDirectionStep, remainderToNat]
      · rename_i horizontalNe
        have horizontalPositive : 0 < horizontal :=
          Nat.pos_of_ne_zero horizontalNe
        have remainderToNat :
            ((((horizontal : Int) - 1) %
                (horizontal + complement + 1 : Nat)).toNat) =
              horizontal - 1 := by
          rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
          have castSub :
              ((horizontal - 1 : Nat) : Int) =
                (horizontal : Int) - 1 := by
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr horizontalNe)]
            rfl
          rw [← castSub]
          exact Int.toNat_natCast _
        simp only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg]
          at remainderToNat
        simp [ComplementLocation.toNatHorizontal,
          ComplementLocation.period, advanceNatHorizontalLocation,
          PeriodicThreeDM.stripDirectionStep, remainderToNat]
  · -- south
    simp only [ComplementLocation.toNatHorizontal,
      ComplementLocation.period, advanceNatHorizontalLocation,
      PeriodicThreeDM.stripDirectionStep]
    apply natHorizontalLocation_ext
    · exact horizontalRemainder.symm
    · simp
  · -- invalid
    simp only [ComplementLocation.toNatHorizontal,
      ComplementLocation.period, advanceNatHorizontalLocation,
      PeriodicThreeDM.stripDirectionStep]
    apply natHorizontalLocation_ext
    · exact horizontalRemainder.symm
    · simp

/-- Stream canonical records from the complement-counter state. -/
def sparseRouteRecordBlocksFromComplementDirections
    (color : WireColor) (before : ComplementLocation) :
    List AxisDirection → List GadgetSparseAssignmentTokens.Token
  | incoming :: outgoing :: directions =>
      let current := advanceComplementLocation before incoming
      GadgetSparseAssignmentTokens.assignmentTokens
          (current.toNatHorizontal.toCell,
            routingCellTypeFromForwardDirections incoming outgoing color) ++
        sparseRouteRecordBlocksFromComplementDirections
          color current (outgoing :: directions)
  | _ => []
termination_by directions => directions.length

/-- The complement cursor emits the exact natural-horizontal cursor word for
its represented positive period. -/
theorem sparseRouteRecordBlocksFromComplementDirections_eq
    (color : WireColor) (before : ComplementLocation)
    (directions : List AxisDirection) :
    sparseRouteRecordBlocksFromComplementDirections color before directions =
      sparseRouteRecordBlocksFromNatHorizontalDirections before.period color
        before.toNatHorizontal directions := by
  induction directions using List.twoStepInduction generalizing before with
  | nil =>
      simp [sparseRouteRecordBlocksFromComplementDirections,
        sparseRouteRecordBlocksFromNatHorizontalDirections]
  | singleton direction =>
      simp [sparseRouteRecordBlocksFromComplementDirections,
        sparseRouteRecordBlocksFromNatHorizontalDirections]
  | cons_cons incoming outgoing directions _ induction =>
      simp only [sparseRouteRecordBlocksFromComplementDirections,
        sparseRouteRecordBlocksFromNatHorizontalDirections]
      rw [← advanceComplementLocation_toNatHorizontal]
      rw [induction outgoing
        (advanceComplementLocation before incoming)]
      rw [advanceComplementLocation_period]

/-- The represented period is always positive. -/
theorem ComplementLocation.period_pos (location : ComplementLocation) :
    0 < location.period := by
  unfold ComplementLocation.period
  omega

end PeriodicCNFStripReduction
end LeanTrominoes
