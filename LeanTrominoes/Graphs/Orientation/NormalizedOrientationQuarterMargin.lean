/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.NormalizedOrientationCNFPartialSoundness

/-! # One fixed margin protects every positive-quadrant decoder window -/
namespace LeanTrominoes.Gadget.NormalizedOrientation.AsCNF

theorem positions_bounds (d : Drawing) {location : Cell} (member : location ∈ positions d) :
    0 ≤ location.1 ∧ location.1 < (d.horizontalPeriod : Int) ∧
      0 ≤ location.2 ∧ location.2 < (d.verticalPeriod : Int) := by
  obtain ⟨x,hx,member⟩ := List.mem_flatMap.mp member
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp member
  have bx := List.mem_range.mp hx
  have yBound := List.mem_range.mp hy
  exact ⟨by omega,by omega,by omega,by omega⟩

def quarterBaseline (n radius : Nat) : Cell := ((n+radius+100 : Nat),(n+radius+100 : Nat))

theorem quarter_lift_deep (d : Drawing) (n radius : Nat) (point : Nat × Nat)
    {offset location : Cell} (offsetMember : offset ∈ TrominoAssignment.boxCellList radius)
    (locationMember : location ∈ positions d) :
    KeyedPeriodicComplement.ShiftedGadgetReadout.Deep n 3 (9,3)
      (lift d location (PeriodicCNF.Reflection.cell
        (Cell.add (quarterBaseline n radius) (Cell.add (point.1,point.2) offset)))) := by
  have bounds := positions_bounds d locationMember
  have offsetBounds := (TrominoAssignment.mem_boxCellList_iff _ _).1 offsetMember
  dsimp [LeanWang.InBox] at offsetBounds
  let translate := Cell.add (quarterBaseline n radius) (Cell.add ((point.1 : Int),(point.2 : Int)) offset)
  have tx : (n : Int)+100 ≤ translate.1 := by dsimp [translate,quarterBaseline,Cell.add]; omega
  have ty : (n : Int)+100 ≤ translate.2 := by dsimp [translate,quarterBaseline,Cell.add]; omega
  have hp : (1 : Int) ≤ d.horizontalPeriod := by simp only [PeriodicOrthogonalDrawing.horizontalPeriod,Nat.cast_add,Nat.cast_one]; omega
  have vp : (1 : Int) ≤ d.verticalPeriod := by simp only [PeriodicOrthogonalDrawing.verticalPeriod,Nat.cast_add,Nat.cast_one]; omega
  have horizontal : translate.1 ≤ translate.1 * (d.horizontalPeriod : Int) := by
    nlinarith [mul_nonneg (show (0 : Int) ≤ translate.1 by omega)
      (show (0 : Int) ≤ (d.horizontalPeriod : Int)-1 by omega)]
  have vertical : translate.2 + (d.verticalPeriod : Int)-1 ≤ translate.2 * (d.verticalPeriod : Int) := by
    nlinarith [mul_nonneg (show (0 : Int) ≤ translate.2-1 by omega)
      (show (0 : Int) ≤ (d.verticalPeriod : Int)-1 by omega)]
  change KeyedPeriodicComplement.ShiftedGadgetReadout.Deep n 3 (9,3)
    (lift d location (PeriodicCNF.Reflection.cell translate))
  dsimp [KeyedPeriodicComplement.ShiftedGadgetReadout.Deep,
    KeyedPeriodicComplement.PartialGadgetReadout.Deep,lift,PeriodicCNF.Reflection.cell,Cell.sub]
  simp only [neg_mul]
  constructor <;> omega

end LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
