/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneCNF
import LeanTrominoes.PeriodicCNFSeededCoRE
import LeanTrominoes.PeriodicBooleanSignedDecoder

/-! # Co-r.e. membership for exact-one formulas with finite prescriptions -/
namespace LeanTrominoes.PeriodicExactOneCNF
open PeriodicCNF.SignedDecoder
variable {V : Type}

theorem seeded_iff (f : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    (formula f).Seeded seed ↔ Prescribed (PeriodicOneInThree.Satisfies f) seed := by
  apply exists_congr
  intro a
  exact and_congr (satisfies_iff f a) Iff.rfl

theorem seeded_coRE [Primcodable V] [DecidableEq V] :
    LeanWang.CoREPred (fun input : PeriodicCNF V × PeriodicCNF.Seed V =>
      Prescribed (PeriodicOneInThree.Satisfies input.1) input.2) := by
  have input : Primrec (fun p : PeriodicCNF V × PeriodicCNF.Seed V =>
      (formula p.1,p.2)) := Primrec.pair (formula_primrec.comp Primrec.fst) Primrec.snd
  exact (LeanWang.REPred.comp PeriodicCNF.seeded_coRE input.to_comp).of_eq
    (fun p => not_congr (seeded_iff p.1 p.2))

theorem fixed_seeded_coRE [Primcodable V] [DecidableEq V] (f : PeriodicCNF V) :
    LeanWang.CoREPred (Prescribed (PeriodicOneInThree.Satisfies f)) :=
  (PeriodicCNF.fixed_seeded_coRE (formula f)).of_eq
    (fun seed => not_congr (seeded_iff f seed))

end LeanTrominoes.PeriodicExactOneCNF
