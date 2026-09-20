/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraphDrawingCertificate
import LeanTrominoes.PeriodicCNFIncidenceGraphComputability
import LeanTrominoes.PeriodicCNFSyntaxComputability
import LeanTrominoes.PeriodicCNFPreimageCoRE
import LeanTrominoes.PeriodicExactOneCNF

/-! # Membership for planar SAT with checked periodic drawings -/
namespace LeanTrominoes.PeriodicPlanarSAT
open PeriodicGridDrawing.FiniteCertificate
variable {V : Type} [Primcodable V] [DecidableEq V]

abbrev Input (V : Type) := PeriodicCNF V × PeriodicGridDrawing

def Valid (i : Input V) : Prop :=
  i.1.WidthAtMost 3 ∧ PeriodicGridDrawing.FiniteCertificate.Valid i.1.incidenceGraph i.2

def Problem (i : Input V) : Prop := Valid i ∧ i.1.Satisfiable

def ExactOneProblem (i : Input V) : Prop := Valid i ∧ PeriodicOneInThree.Satisfiable i.1

theorem valid_primrec : PrimrecPred (Valid (V := V)) :=
  ((PeriodicCNF.widthAtMost_primrec 3).comp Primrec.fst).and
    (PeriodicGridDrawing.FiniteCertificate.valid_primrec.comp
      (PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst) Primrec.snd)

theorem problem_coRE : LeanWang.CoREPred (Problem (V := V)) :=
  PeriodicCNF.restricted_preimage_coRE valid_primrec Primrec.fst

theorem exactOneProblem_coRE : LeanWang.CoREPred (ExactOneProblem (V := V)) := by
  have upper := PeriodicCNF.restricted_preimage_coRE valid_primrec
    (PeriodicExactOneCNF.formula_primrec.comp (Primrec.fst : Primrec (fun i : Input V => i.1)))
  exact upper.of_eq fun i => not_congr (and_congr_right fun _ =>
    PeriodicExactOneCNF.satisfiable_iff i.1)

variable [BEq V] [LawfulBEq V]

def ThreeOccurrenceProblem (i : Input V) : Prop :=
  i.1.OccurrencesAtMost 3 ∧ Problem i

def ExactOneThreeOccurrenceProblem (i : Input V) : Prop :=
  i.1.OccurrencesAtMost 3 ∧ ExactOneProblem i

theorem threeOccurrenceProblem_coRE : LeanWang.CoREPred (ThreeOccurrenceProblem (V := V)) := by
  have upper := PeriodicCNF.restricted_preimage_coRE
    (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and (valid_primrec (V := V)))
    (Primrec.fst : Primrec (fun i : Input V => i.1))
  simpa only [LeanWang.CoREPred, ThreeOccurrenceProblem, Problem, and_assoc] using upper

theorem exactOneThreeOccurrenceProblem_coRE :
    LeanWang.CoREPred (ExactOneThreeOccurrenceProblem (V := V)) := by
  have upper := PeriodicCNF.restricted_preimage_coRE
    (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and (valid_primrec (V := V)))
    (PeriodicExactOneCNF.formula_primrec.comp (Primrec.fst : Primrec (fun i : Input V => i.1)))
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [ExactOneThreeOccurrenceProblem,ExactOneProblem,PeriodicExactOneCNF.satisfiable_iff,
      and_assoc]

end LeanTrominoes.PeriodicPlanarSAT
