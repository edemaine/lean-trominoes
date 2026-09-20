/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraphOrbitCertificate
import LeanTrominoes.PeriodicPlanarSATUnboundedCoRE

/-! # Planar SAT with arbitrary periodic vertex representatives -/
namespace LeanTrominoes.PeriodicPlanarSAT.Orbit
variable {V : Type} [Primcodable V] [DecidableEq V]

def Valid (i : Input V) : Prop :=
  i.1.WidthAtMost 3 ∧ PeriodicGridDrawing.OrbitCertificate.Compatible i.1.incidenceGraph i.2

def Problem (i : Input V) : Prop :=
  Valid i ∧ i.2.IsContinuouslyPlanar ∧ i.1.Satisfiable

def ThreeOccurrenceProblem (i : Input V) : Prop :=
  i.1.OccurrencesAtMost 3 ∧ Problem i

theorem valid_primrec : PrimrecPred (Valid (V := V)) :=
  ((PeriodicCNF.widthAtMost_primrec 3).comp Primrec.fst).and
    (PeriodicGridDrawing.OrbitCertificate.compatible_primrec.comp
      (PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst) Primrec.snd)

theorem problem_coRE : LeanWang.CoREPred (Problem (V := V)) :=
  Unbounded.restricted_coRE valid_primrec Primrec.snd Primrec.fst

theorem threeOccurrenceProblem_coRE : LeanWang.CoREPred (ThreeOccurrenceProblem (V := V)) := by
  have upper := Unbounded.restricted_coRE
    (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and (valid_primrec (V := V)))
    (Primrec.snd : Primrec (fun i : Input V => i.2)) Primrec.fst
  simpa only [LeanWang.CoREPred,ThreeOccurrenceProblem,Problem,and_assoc] using upper
end LeanTrominoes.PeriodicPlanarSAT.Orbit
