/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSeededFiniteSearch
import LeanTrominoes.SAT.CNF.PeriodicCNFCoRE

/-! # Co-r.e. membership for finite prescriptions in a fixed formula -/
namespace LeanTrominoes.PeriodicCNF
namespace FiniteSearch
variable {V : Type} [Primcodable V] [DecidableEq V]

omit [DecidableEq V] in
theorem withSeed_primrec :
    Primrec (fun a : (PeriodicCNF V × Seed V) × Nat => withSeed a.1.1 a.1.2 a.2) := by
  have singletons : Primrec (fun seed : Seed V => seed.map (fun pin => [pin])) :=
    Primrec.list_map Primrec.id
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact Primrec.list_append.comp
    (instantiate_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (singletons.comp (Primrec.snd.comp Primrec.fst))

end FiniteSearch

theorem seeded_coRE {V : Type} [Primcodable V] [DecidableEq V] :
    LeanWang.CoREPred (fun a : PeriodicCNF V × Seed V => a.1.Seeded a.2) := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun (a : PeriodicCNF V × Seed V) r =>
      ¬ FiniteSearch.Check (FiniteSearch.withSeed a.1 a.2 r))
    (FiniteSearch.check_primrec.comp FiniteSearch.withSeed_primrec).not.computablePred
  exact obstruction.of_eq fun a => by
    change (∃ r, ¬ FiniteSearch.Check (FiniteSearch.withSeed a.1 a.2 r)) ↔
      ¬ a.1.Seeded a.2
    rw [FiniteSearch.seeded_iff]
    exact not_forall.symm

theorem fixed_seeded_coRE {V : Type} [Primcodable V] [DecidableEq V]
    (f : PeriodicCNF V) : LeanWang.CoREPred (f.Seeded) := by
  have input : Primrec (fun seed : Seed V => (f,seed)) :=
    Primrec.pair (Primrec.const f) Primrec.id
  exact (LeanWang.REPred.comp seeded_coRE input.to_comp).of_eq (fun _ => Iff.rfl)

end LeanTrominoes.PeriodicCNF
