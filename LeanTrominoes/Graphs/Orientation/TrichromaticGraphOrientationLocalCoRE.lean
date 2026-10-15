/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationCoRE
import LeanTrominoes.SAT.CNF.PeriodicCNFPreimageCoRE
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationGeometryComputability

/-! # Co-r.e. membership for ordinary local colored graphs -/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Computability PeriodicThreeDM.NormalizationCompiler

theorem isLocal_primrec : PrimrecPred IsLocal := by
  have edgeData : Primrec fun record : PeriodicEdge Nat × Gadget.WireColor =>
      PeriodicEdge.equivData record.1 := Primrec.of_equiv.comp Primrec.fst
  have offset := Primrec.snd.comp (Primrec.snd.comp edgeData)
  have bound : PrimrecPred fun record : PeriodicEdge Nat × Gadget.WireColor => record.1.span ≤ 1 :=
    Primrec.nat_le.comp (Primrec.nat_add.comp
      (int_natAbs_primrec.comp (Primrec.fst.comp offset))
      (int_natAbs_primrec.comp (Primrec.snd.comp offset))) (Primrec.const 1)
  exact bound.forall_mem_list.comp Primrec.snd

def LocalProblem (input : Input) : Prop := IsLocal input ∧ Problem input

theorem localProblem_coRE : LeanWang.CoREPred LocalProblem := by
  have upper := PeriodicCNF.restricted_preimage_coRE
    (isLocal_primrec.and wellFormed_primrec) formula_primrec
  apply upper.of_eq
  intro input
  apply not_congr
  simp only [LocalProblem,Problem,formula_satisfiable_iff,and_assoc]

end LeanTrominoes.TrichromaticGraphOrientation
