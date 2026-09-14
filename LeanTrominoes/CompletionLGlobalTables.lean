/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBrickBooleanWitness

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

def microBrick (m : Cell) : Cell := ((m.1 - m.2 / 6) / 2,m.2 / 6)
def microLocal (m : Cell) : Cell := Cell.sub m (brickMicroOrigin (microBrick m))

theorem micro_local_bounds (m : Cell) :
    0 ≤ (microLocal m).1 ∧ (microLocal m).1 < 2 ∧
    0 ≤ (microLocal m).2 ∧ (microLocal m).2 < 6 := by
  dsimp [microLocal,microBrick,brickMicroOrigin,Cell.sub]
  omega

def globalTableValue (tables : Cell → BrickValues) (m : Cell) : Bool :=
  tableValue (tables (microBrick m)) (microLocal m)

/-- Connector coordinates inside the first six rows belong to this brick. -/
theorem micro_brick_interior (location c : Cell)
    (bounds : 0 ≤ c.1 ∧ c.1 < 2 ∧ 0 ≤ c.2 ∧ c.2 < 6) :
    microBrick (Cell.add (brickMicroOrigin location) c) = location := by
  apply Prod.ext <;> dsimp [microBrick,brickMicroOrigin,Cell.add] <;> omega

theorem global_table_interior (tables : Cell → BrickValues) (location c : Cell)
    (bounds : 0 ≤ c.1 ∧ c.1 < 2 ∧ 0 ≤ c.2 ∧ c.2 < 6) :
    globalTableValue tables (Cell.add (brickMicroOrigin location) c) = tableValue (tables location) c := by
  have owner := micro_brick_interior location c bounds
  unfold globalTableValue microLocal
  rw [owner]
  have cancel : Cell.sub (Cell.add (brickMicroOrigin location) c) (brickMicroOrigin location) = c := by
    apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
  rw [cancel]

def belowBrick (location : Cell) (x : Fin 2) : Cell :=
  Cell.add location (if x.val = 0 then (-1,1) else (0,1))

def oppositeColumn (x : Fin 2) : Fin 2 := ⟨1 - x.val,by omega⟩

def TableSeams (tables : Cell → BrickValues) : Prop :=
  ∀ location x, tables location x 6 = tables (belowBrick location x) (oppositeColumn x) 0

theorem micro_bottom_coordinates (location : Cell) (x : Fin 2) :
    Cell.add (brickMicroOrigin location) (x.val,6) =
      Cell.add (brickMicroOrigin (belowBrick location x)) ((oppositeColumn x).val,0) := by
  by_cases zero : x.val = 0
  · apply Prod.ext <;> simp [belowBrick,oppositeColumn,zero,brickMicroOrigin,Cell.add]
    all_goals omega
  · have one : x.val = 1 := by omega
    apply Prod.ext <;> simp [belowBrick,oppositeColumn,one,brickMicroOrigin,Cell.add]
    all_goals omega

theorem table_value_index (v : BrickValues) (x : Fin 2) (y : Fin 7) :
    tableValue v (x.val,y.val) = v x y := by
  unfold tableValue
  congr 1 <;> apply Fin.ext <;> simp

theorem global_table_bottom (tables : Cell → BrickValues) (seams : TableSeams tables)
    (location : Cell) (x : Fin 2) :
    globalTableValue tables (Cell.add (brickMicroOrigin location) (x.val,6)) = tables location x 6 := by
  rw [micro_bottom_coordinates,global_table_interior]
  · rw [seams location x]
    simpa using table_value_index (tables (belowBrick location x)) (oppositeColumn x) 0
  · have bound := (oppositeColumn x).isLt
    exact ⟨by omega,by omega,by omega,by omega⟩

/-- Neighbor agreement extends each finite table through its shared bottom row. -/
theorem global_table_window (tables : Cell → BrickValues) (seams : TableSeams tables)
    (location c : Cell) (bounds : 0 ≤ c.1 ∧ c.1 < 2 ∧ 0 ≤ c.2 ∧ c.2 < 7) :
    globalTableValue tables (Cell.add (brickMicroOrigin location) c) = tableValue (tables location) c := by
  by_cases last : c.2 = 6
  · let x : Fin 2 := ⟨c.1.toNat,by omega⟩
    have eq : c = ((x.val : Int),6) := by
      apply Prod.ext <;> dsimp [x] <;> omega
    rw [eq,global_table_bottom tables seams]
    exact (table_value_index (tables location) x 6).symm
  · apply global_table_interior
    omega

end LeanTrominoes.CompletionPattern.LBricks
