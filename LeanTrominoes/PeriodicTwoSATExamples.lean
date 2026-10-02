/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATLocalTime
import LeanTrominoes.PeriodicTwoSATRegression

/-! # Complete solver regressions, including empty and zero-dimensional inputs -/
namespace LeanTrominoes.PeriodicTwoSAT

example : (solveLocal ([] : Formula (Fin 0) 0)).1=true := by decide +kernel
example : (solveLocal ([none] : Formula (Fin 0) 3)).1=false := by decide +kernel

def positiveUnit : Formula (Fin 1) 0 := [some (((0,true),0),((0,true),0))]
def negativeUnit : Formula (Fin 1) 0 := [some (((0,false),0),((0,false),0))]

set_option maxHeartbeats 2000000 in
example : (solveLocal positiveUnit).1=true := by decide +kernel
set_option maxHeartbeats 2000000 in
example : (solveLocal (positiveUnit++negativeUnit)).1=false := by decide +kernel

example : (solveLocal alternation).1=true :=
  (solveLocal_correct alternation alternation_local).mpr alternation_satisfiable

end LeanTrominoes.PeriodicTwoSAT
