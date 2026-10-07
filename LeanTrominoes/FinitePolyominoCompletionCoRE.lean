/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FinitePolyominoCompletionSearch

/-! # Effective finite obstructions for finite-seed polyomino completion

The finite searches are primitive recursive in both shapes, the seed, and
the box radius. Thus plane completion is co-r.e., including when the two
shapes are fixed and only the finite seed varies.
-/

namespace LeanTrominoes.FinitePolyominoCompletion
open Computability

theorem pool_primrec : Primrec₂ pool :=
  Primrec.list_append.comp
    (PlaneTilingSearch.pool_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.snd.comp Primrec.fst)

theorem valid_primrec :
    PrimrecPred (fun a : Input × Nat × List (Placement Bool) =>
      Valid a.1 a.2.1 a.2.2) := by
  have member : PrimrecRel fun (p : Placement Bool) (ps : List (Placement Bool)) =>
      p ∈ ps := (Primrec.eq.exists_mem_list.swap).of_eq fun _ _ => by simp
  have retained : PrimrecPred (fun a : Input × Nat × List (Placement Bool) =>
      a.1.2 ⊆ a.2.2) :=
    member.forall_mem_list.comp
      (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  exact (PlaneTilingSearch.valid_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).and retained

theorem finiteSearch_primrec : PrimrecRel FiniteSearch := by
  have selected : PrimrecRel (fun (ps : List (Placement Bool)) (a : Input × Nat) =>
      Valid a.1 a.2 ps) :=
    valid_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))
  exact selected.exists_mem_list.comp
    (PlaneTilingSearch.subsets_primrec.comp pool_primrec) Primrec.id

/-- Completion from an arbitrary finite seed belongs to co-r.e. -/
theorem coRE : LeanWang.CoREPred Completable := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input radius => ¬ FiniteSearch input radius)
    finiteSearch_primrec.not.computablePred
  exact obstruction.of_eq (fun input => by
    change (∃ radius, ¬ FiniteSearch input radius) ↔ ¬ Completable input
    rw [completable_iff]
    exact not_forall.symm)

/-- The two shapes are constants; the finite seed is the complete input. -/
def fixedProblem (p q : List Cell) (seed : List (Placement Bool)) : Prop :=
  Completable ((p, q), seed)

theorem fixedProblem_coRE (p q : List Cell) : LeanWang.CoREPred (fixedProblem p q) := by
  have compiler : Primrec (fun seed : List (Placement Bool) => ((p, q), seed)) :=
    Primrec.pair (Primrec.const (p, q)) Primrec.id
  exact (LeanWang.REPred.comp coRE compiler.to_comp).of_eq (fun _ => Iff.rfl)

end LeanTrominoes.FinitePolyominoCompletion
