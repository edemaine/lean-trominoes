/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.ThreeSAT.FiniteThreeSATThree

namespace LeanTrominoes.FiniteThreeSATThree

example : (formula ([] : FiniteCNF.Formula Nat))=[] := by decide +kernel

/-- A duplicated source atom receives distinct occurrence copies and a cycle. -/
example : (formula [[(0,true),(0,false),(1,true)]]).length=4 := by decide +kernel

example : ((formula [[(0,true),(0,false),(1,true)]]).flatten.map Prod.fst).length=9 :=
  by decide +kernel

end LeanTrominoes.FiniteThreeSATThree
