/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFCoRE

/-! # Co-r.e. membership through an effective CNF presentation -/
namespace LeanTrominoes.PeriodicCNF

/-- Reject invalid input presentations, then test their encoded constraints. -/
theorem restricted_preimage_coRE {A V : Type} [Primcodable A] [Primcodable V]
    [DecidableEq V] {valid : A → Prop} (hv : PrimrecPred valid)
    {encode : A → PeriodicCNF V} (he : Primrec encode) :
    LeanWang.CoREPred (fun a => valid a ∧ (encode a).Satisfiable) := by
  have check : PrimrecRel fun a r =>
      valid a ∧ FiniteSearch.Check (FiniteSearch.instantiate (encode a) r) :=
    (hv.comp Primrec.fst).and (FiniteSearch.check_primrec.comp
      (FiniteSearch.instantiate_primrec.comp (he.comp Primrec.fst) Primrec.snd))
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun a r => ¬ (valid a ∧ FiniteSearch.Check (FiniteSearch.instantiate (encode a) r)))
    check.not.computablePred
  exact obstruction.of_eq fun a => by
    rw [← not_forall]
    apply not_congr
    simp only [forall_and, forall_const, ← FiniteSearch.satisfiable_iff]

end LeanTrominoes.PeriodicCNF
