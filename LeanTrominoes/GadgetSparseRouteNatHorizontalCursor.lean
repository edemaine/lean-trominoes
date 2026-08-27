/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionRasterCursor

/-! # Natural-horizontal raster route cursor

The horizontally periodic coordinate is stored as a natural unary counter;
the open vertical coordinate remains signed.  This is the arithmetic state
implemented by the route-record machine.
-/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

structure NatHorizontalLocation where
  horizontal : Nat
  vertical : Int
  deriving DecidableEq, Repr

def NatHorizontalLocation.toCell
    (location : NatHorizontalLocation) : Cell :=
  (location.horizontal, location.vertical)

def NatHorizontalLocation.ofNat
    (horizontal vertical : Nat) : NatHorizontalLocation :=
  ⟨horizontal, vertical⟩

/-- Exact horizontal remainder and signed vertical addition for one finite
strip direction. -/
def advanceNatHorizontalLocation
    (period : Nat) (location : NatHorizontalLocation)
    (direction : AxisDirection) : NatHorizontalLocation :=
  let step := PeriodicThreeDM.stripDirectionStep direction
  ⟨(((location.horizontal : Int) + step.1) % period).toNat,
    location.vertical + step.2⟩

/-- For positive period, natural-horizontal advancement is exactly the
existing signed-cell strip transition. -/
@[simp] theorem toCell_advanceNatHorizontalLocation
    (period : Nat) (positive : 0 < period)
    (location : NatHorizontalLocation) (direction : AxisDirection) :
    (advanceNatHorizontalLocation period location direction).toCell =
      PeriodicThreeDM.advanceStripLocation period location.toCell
        direction := by
  unfold advanceNatHorizontalLocation NatHorizontalLocation.toCell
    PeriodicThreeDM.advanceStripLocation
  let step := PeriodicThreeDM.stripDirectionStep direction
  have periodNe : (period : Int) ≠ 0 := by omega
  have remainderNonnegative :
      0 ≤ (((location.horizontal : Int) + step.1) % period) :=
    Int.emod_nonneg _ periodNe
  rw [Int.toNat_of_nonneg remainderNonnegative]

/-- Canonical assignment records streamed with a natural horizontal counter
and signed vertical counter. -/
def sparseRouteRecordBlocksFromNatHorizontalDirections
    (period : Nat) (color : WireColor)
    (before : NatHorizontalLocation) :
    List AxisDirection → List GadgetSparseAssignmentTokens.Token
  | incoming :: outgoing :: directions =>
      let current :=
        advanceNatHorizontalLocation period before incoming
      GadgetSparseAssignmentTokens.assignmentTokens
          (current.toCell,
            routingCellTypeFromForwardDirections incoming outgoing color) ++
        sparseRouteRecordBlocksFromNatHorizontalDirections
          period color current (outgoing :: directions)
  | _ => []
termination_by directions => directions.length

/-- The natural-horizontal and signed-cell raster cursors agree exactly for
every positive period. -/
theorem sparseRouteRecordBlocksFromNatHorizontalDirections_eq
    (period : Nat) (positive : 0 < period) (color : WireColor)
    (before : NatHorizontalLocation)
    (directions : List AxisDirection) :
    sparseRouteRecordBlocksFromNatHorizontalDirections period color
        before directions =
      sparseRouteRecordBlocksFromRasterDirections period color
        before.toCell directions := by
  induction directions using List.twoStepInduction generalizing before with
  | nil =>
      simp [sparseRouteRecordBlocksFromNatHorizontalDirections,
        sparseRouteRecordBlocksFromRasterDirections]
  | singleton direction =>
      simp [sparseRouteRecordBlocksFromNatHorizontalDirections,
        sparseRouteRecordBlocksFromRasterDirections]
  | cons_cons incoming outgoing directions _ induction =>
      simp only [sparseRouteRecordBlocksFromNatHorizontalDirections,
        sparseRouteRecordBlocksFromRasterDirections]
      rw [toCell_advanceNatHorizontalLocation period positive]
      rw [induction outgoing
        (advanceNatHorizontalLocation period before incoming)]
      rw [toCell_advanceNatHorizontalLocation period positive]

/-- Natural source coordinates embed definitionally as a cell. -/
@[simp] theorem ofNat_toCell (horizontal vertical : Nat) :
    (NatHorizontalLocation.ofNat horizontal vertical).toCell =
      ((horizontal : Int), (vertical : Int)) := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
