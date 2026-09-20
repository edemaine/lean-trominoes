/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneCNF
import LeanTrominoes.PeriodicCNFPreimageCoRE
import LeanTrominoes.PeriodicCNFSyntaxComputability
import LeanTrominoes.PeriodicOneInThreeReductionComputability

/-! # Plane periodic exact-one SAT completeness -/
namespace LeanTrominoes.PeriodicOneInThree

theorem restricted_satisfiable_coRE {V : Type} [Primcodable V] [DecidableEq V]
    {valid : PeriodicCNF V → Prop} (hv : PrimrecPred valid) :
    LeanWang.CoREPred (fun f => valid f ∧ Satisfiable f) := by
  have upper := PeriodicCNF.restricted_preimage_coRE hv
    (PeriodicExactOneCNF.formula_primrec (V := V))
  exact upper.of_eq fun f => not_congr (and_congr_right fun _ =>
    PeriodicExactOneCNF.satisfiable_iff f)

noncomputable local instance completionSourceDecidableEq :
    DecidableEq PeriodicThreeSATThree.WangThreeSATThreeVariable := Classical.decEq _
local instance completionAuxiliaryBEq : BEq OneInThreeAux := instBEqOfDecidableEq

/-- Local 2D periodic 1-in-3SAT-3, without a planarity restriction. -/
theorem localOneInThreeSATThreeCoREComplete :
    LeanWang.CoREComplete LocalOneInThreeSATThreeHolds := by
  refine ⟨?_, localOneInThreeSATThreeCoREHard⟩
  have upper := restricted_satisfiable_coRE
    ((PeriodicCNF.isLocal_primrec (V := WangOneInThreeVariable)).and
      ((PeriodicCNF.widthAtMost_primrec 3).and (PeriodicCNF.occurrencesAtMost_primrec 3)))
  simpa only [LeanWang.CoREPred, LocalOneInThreeSATThreeHolds, and_assoc] using upper

end LeanTrominoes.PeriodicOneInThree
