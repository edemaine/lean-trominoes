/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATOrbitCoRE

/-! # Local planar SAT languages with supplied drawings -/
namespace LeanTrominoes.PeriodicPlanarSAT
variable {V : Type} [Primcodable V] [DecidableEq V]
namespace Orbit

def LocalProblem (i : Input V) : Prop := i.1.IsLocal ∧ Problem i
def LocalThreeOccurrenceProblem (i : Input V) : Prop := i.1.IsLocal ∧ ThreeOccurrenceProblem i

theorem localProblem_coRE : LeanWang.CoREPred (LocalProblem (V := V)) := by
  have upper := Unbounded.restricted_coRE
    (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and valid_primrec)
    (Primrec.snd : Primrec (fun i : Input V => i.2)) Primrec.fst
  simpa only [LeanWang.CoREPred,LocalProblem,Problem,and_assoc] using upper

theorem localThreeOccurrenceProblem_coRE : LeanWang.CoREPred (LocalThreeOccurrenceProblem (V := V)) := by
  have upper := Unbounded.restricted_coRE
    (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and
      (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and valid_primrec))
    (Primrec.snd : Primrec (fun i : Input V => i.2)) Primrec.fst
  simpa only [LeanWang.CoREPred,LocalThreeOccurrenceProblem,ThreeOccurrenceProblem,Problem,and_assoc] using upper
end Orbit
namespace Unbounded

def LocalExactOneProblem (i : Input V) : Prop := i.1.IsLocal ∧ ExactOneProblem i
def LocalExactOneThreeOccurrenceProblem (i : Input V) : Prop := i.1.IsLocal ∧ ExactOneThreeOccurrenceProblem i

theorem localExactOneProblem_coRE : LeanWang.CoREPred (LocalExactOneProblem (V := V)) := by
  have upper := restricted_coRE
    (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and valid_primrec)
    (Primrec.snd : Primrec (fun i : Input V => i.2))
    (PeriodicExactOneCNF.formula_primrec.comp Primrec.fst)
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [LocalExactOneProblem,ExactOneProblem,PeriodicExactOneCNF.satisfiable_iff,and_assoc]

theorem localExactOneThreeOccurrenceProblem_coRE :
    LeanWang.CoREPred (LocalExactOneThreeOccurrenceProblem (V := V)) := by
  have upper := restricted_coRE
    (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and
      (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and valid_primrec))
    (Primrec.snd : Primrec (fun i : Input V => i.2))
    (PeriodicExactOneCNF.formula_primrec.comp Primrec.fst)
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [LocalExactOneThreeOccurrenceProblem,ExactOneThreeOccurrenceProblem,
      ExactOneProblem,PeriodicExactOneCNF.satisfiable_iff,and_assoc]
end Unbounded
end LeanTrominoes.PeriodicPlanarSAT
