/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDominoSolver
import LeanTrominoes.PeriodicDominoCompletion

/-! Kernel-evaluated regressions for geometric adjacency and parity doubling. -/
namespace LeanTrominoes.Domino.Examples
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- The unit-period line needs a parity cover before taking its matching quotient.
def line : BasisData 1 1 := ⟨fun _ _ => 0,fun _ _ => 1⟩
example : line.solve=true := by decide +kernel

-- One isolated cell per period cannot be tiled; two adjacent cells can.
def isolated : BasisData 1 1 := ⟨fun _ _ => 0,fun _ _ => 3⟩
def pairs : BasisData 2 1 := ⟨fun v _ => (v.val : Int),fun _ _ => 3⟩
example : isolated.solve=false := by decide +kernel
example : pairs.solve=true := by decide +kernel

-- A nonsingular skew basis, rather than an axis-aligned box.
def skew : BasisData 1 2 := ⟨fun _ _ => 0,!![1,1;0,1]⟩
example : skew.solve=true := by decide +kernel
example : skew.decodeWith skew.inverseData (fun i => if i=0 then 7 else -3)=
    some (0,fun i => if i=0 then 10 else -3) := by decide +kernel

-- Empty regions and the zero-dimensional single-cell obstruction.
def empty : BasisData 0 0 := ⟨Fin.elim0,fun i => Fin.elim0 i⟩
def point : BasisData 1 0 := ⟨fun _ => Fin.elim0,fun i => Fin.elim0 i⟩
example : empty.solve=true := by decide +kernel
example : point.solve=false := by decide +kernel

-- The semantic theorem turns the negative computation into nontilability.
example (valid : isolated.Valid) : ¬Tileable (isolated.chart valid).region := by
  intro tiled
  have accepted := (isolated.solve_correct valid).mpr tiled
  have rejected : isolated.solve=false := by decide +kernel
  simp [rejected] at accepted

end LeanTrominoes.Domino.Examples
