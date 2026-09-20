/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATCoRE
import LeanTrominoes.PeriodicDrawingPlanarityCoRE

/-! # Planar SAT membership without a route bounding box -/
namespace LeanTrominoes.PeriodicPlanarSAT.Unbounded
open PeriodicGridDrawing
variable {V : Type} [Primcodable V] [DecidableEq V]

def Valid (i : Input V) : Prop :=
  i.1.WidthAtMost 3 ∧ FiniteCertificate.Compatible i.1.incidenceGraph i.2

def Problem (i : Input V) : Prop :=
  Valid i ∧ i.2.IsContinuouslyPlanar ∧ i.1.Satisfiable

def ExactOneProblem (i : Input V) : Prop :=
  Valid i ∧ i.2.IsContinuouslyPlanar ∧ PeriodicOneInThree.Satisfiable i.1

theorem valid_primrec : PrimrecPred (Valid (V := V)) :=
  ((PeriodicCNF.widthAtMost_primrec 3).comp Primrec.fst).and
    (FiniteCertificate.compatible_primrec.comp
      (PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst) Primrec.snd)

theorem restricted_coRE {A : Type} [Primcodable A]
    {valid : A → Prop} (hv : PrimrecPred valid)
    {drawing : A → PeriodicGridDrawing} (hd : Primrec drawing)
    {formula : A → PeriodicCNF V} (hf : Primrec formula) :
    LeanWang.CoREPred (fun a => valid a ∧ (drawing a).IsContinuouslyPlanar ∧
      (formula a).Satisfiable) := by
  have test : PrimrecRel fun a n => valid a ∧
      PlanaritySearch.At (drawing a) (PlanaritySearch.probeAt n) ∧
      PeriodicCNF.FiniteSearch.Check (PeriodicCNF.FiniteSearch.instantiate (formula a) n) :=
    (hv.comp Primrec.fst).and
      ((PlanaritySearch.at_primrec.comp (hd.comp Primrec.fst)
        (PlanaritySearch.probeAt_primrec.comp Primrec.snd)).and
      (PeriodicCNF.FiniteSearch.check_primrec.comp
        (PeriodicCNF.FiniteSearch.instantiate_primrec.comp (hf.comp Primrec.fst) Primrec.snd)))
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun a n => ¬ (valid a ∧
      PlanaritySearch.At (drawing a) (PlanaritySearch.probeAt n) ∧
      PeriodicCNF.FiniteSearch.Check (PeriodicCNF.FiniteSearch.instantiate (formula a) n)))
    test.not.computablePred
  exact obstruction.of_eq fun a => by
    rw [← not_forall]
    apply not_congr
    simp only [forall_and,forall_const,PlanaritySearch.all_nat_iff,
      ← PeriodicCNF.FiniteSearch.satisfiable_iff]

theorem problem_coRE : LeanWang.CoREPred (Problem (V := V)) :=
  restricted_coRE valid_primrec Primrec.snd Primrec.fst

theorem exactOneProblem_coRE : LeanWang.CoREPred (ExactOneProblem (V := V)) := by
  have upper := restricted_coRE valid_primrec
    (Primrec.snd : Primrec (fun i : Input V => i.2))
    (PeriodicExactOneCNF.formula_primrec.comp Primrec.fst)
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [ExactOneProblem,PeriodicExactOneCNF.satisfiable_iff]

variable [BEq V] [LawfulBEq V]
def ExactOneThreeOccurrenceProblem (i : Input V) : Prop :=
  i.1.OccurrencesAtMost 3 ∧ ExactOneProblem i

theorem exactOneThreeOccurrenceProblem_coRE :
    LeanWang.CoREPred (ExactOneThreeOccurrenceProblem (V := V)) := by
  have upper := restricted_coRE
    (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and (valid_primrec (V := V)))
    (Primrec.snd : Primrec (fun i : Input V => i.2))
    (PeriodicExactOneCNF.formula_primrec.comp Primrec.fst)
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [ExactOneThreeOccurrenceProblem,ExactOneProblem,
      PeriodicExactOneCNF.satisfiable_iff,and_assoc]
end LeanTrominoes.PeriodicPlanarSAT.Unbounded
