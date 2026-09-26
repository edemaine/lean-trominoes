/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetStripBoundary

/-! # Finite coordinate formulas for normalized orientation checks -/
namespace LeanTrominoes.Gadget.PeriodicOrthogonalDrawing

private theorem residue_last (n : Nat) : residue (-1) n = Fin.last n := by
  apply Fin.ext
  have h := residue_add_period (Fin.last n) (-1)
  have coordinate : ((Fin.last n).val : Int) + (-1) * (n+1) = -1 := by simp
  rw [coordinate] at h
  exact congrArg Fin.val h

private theorem residue_zero_period (n : Nat) : residue ((n+1:Nat):Int) n = 0 := by
  have h := residue_add_period (0 : Fin (n+1)) 1
  simpa using h

theorem blankVerticalBoundary_iff_rows (d : PeriodicOrthogonalDrawing) :
    d.HasBlankVerticalBoundary ↔ ∀ x : Fin (d.horizontalPeriodPred+1),
      d.get (x,0) = .blank ∧ d.get (x,Fin.last d.verticalPeriodPred) = .blank := by
  constructor
  · intro blank x
    have h := blank (x.val:Int)
    simp only [getAt,positionAt,residue_last,verticalPeriod,residue_zero_period] at h
    have hx : residue (x.val:Int) d.horizontalPeriodPred = x := by
      simpa using residue_add_period x 0
    rw [hx] at h
    exact ⟨h.2,h.1⟩
  · intro rows x
    have h := rows (residue x d.horizontalPeriodPred)
    simpa only [getAt,positionAt,residue_last,verticalPeriod,residue_zero_period] using And.intro h.2 h.1

def neighborCoordinates (width height x y : Nat) : Side → Nat × Nat
  | .north => (x,(y+height-1)%height)
  | .east => ((x+1)%width,y)
  | .south => (x,(y+1)%height)
  | .west => ((x+width-1)%width,y)

private theorem increment_val (n : Nat) (i : Fin (n+1)) : (i+1).val = (i.val+1)%(n+1) := by
  simp [Fin.val_add,Nat.add_mod]

private theorem decrement_val (n : Nat) (i : Fin (n+1)) : (i-1).val = (i.val+(n+1)-1)%(n+1) := by
  rw [sub_eq_add_neg,Fin.val_add,Fin.coe_neg_one]
  congr 1

theorem neighbor_values (d : PeriodicOrthogonalDrawing) (p : d.Position) (side : Side) :
    ((d.neighbor p side).1.val,(d.neighbor p side).2.val) =
      neighborCoordinates d.horizontalPeriod d.verticalPeriod p.1.val p.2.val side := by
  cases side <;> simp only [neighbor,neighborCoordinates,increment_val,decrement_val,
    horizontalPeriod,verticalPeriod]

end LeanTrominoes.Gadget.PeriodicOrthogonalDrawing
