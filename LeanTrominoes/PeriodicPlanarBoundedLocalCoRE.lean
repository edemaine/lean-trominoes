/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarLocalCoRE
import LeanTrominoes.PeriodicCNFVariableSizeBounds

/-! # Local planar SAT with an intrinsic linear grid-size restriction -/
namespace LeanTrominoes

theorem PeriodicCNF.presentationSize_primrec {V : Type} [Primcodable V] :
    Primrec (@PeriodicCNF.presentationSize V) := by
  have clauses : Primrec (fun f : PeriodicCNF V => f.clauses) := PeriodicCNF.equivData_primrec
  have flattened : Primrec (fun f : PeriodicCNF V => f.clauses.flatten) :=
    Primrec.list_flatten.comp clauses
  exact Primrec.nat_add.comp (Primrec.list_length.comp clauses) (Primrec.list_length.comp flattened)

namespace PeriodicPlanarSAT
variable {V : Type} [Primcodable V] [DecidableEq V]

def GridBound (coefficient : Nat) (i : Input V) : Prop :=
  i.2.gridSize ≤ coefficient*(i.1.presentationSize+1)

omit [DecidableEq V] in
theorem gridBound_primrec (coefficient : Nat) : PrimrecPred (GridBound (V := V) coefficient) :=
  Primrec.nat_le.comp (PeriodicGridDrawing.gridSize_primrec.comp Primrec.snd)
    (Primrec.nat_mul.comp (Primrec.const coefficient)
      (Primrec.nat_add.comp (PeriodicCNF.presentationSize_primrec.comp Primrec.fst) (Primrec.const 1)))

namespace Orbit

def BoundedLocalProblem (i : Input V) : Prop := GridBound 8847360 i ∧ LocalProblem i
def BoundedLocalThreeOccurrenceProblem (i : Input V) : Prop := GridBound 8847360 i ∧ LocalThreeOccurrenceProblem i

theorem boundedLocalProblem_coRE : LeanWang.CoREPred (BoundedLocalProblem (V := V)) := by
  have upper := Unbounded.restricted_coRE
    ((gridBound_primrec 8847360).and
      (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and valid_primrec))
    (Primrec.snd : Primrec (fun i : Input V => i.2)) Primrec.fst
  simpa only [LeanWang.CoREPred,BoundedLocalProblem,LocalProblem,Problem,and_assoc] using upper

theorem boundedLocalThreeOccurrenceProblem_coRE :
    LeanWang.CoREPred (BoundedLocalThreeOccurrenceProblem (V := V)) := by
  have upper := Unbounded.restricted_coRE
    ((gridBound_primrec 8847360).and
      (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and
        (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and valid_primrec)))
    (Primrec.snd : Primrec (fun i : Input V => i.2)) Primrec.fst
  simpa only [LeanWang.CoREPred,BoundedLocalThreeOccurrenceProblem,LocalThreeOccurrenceProblem,
    ThreeOccurrenceProblem,Problem,and_assoc] using upper
end Orbit
namespace Unbounded

def BoundedLocalExactOneProblem (i : Input V) : Prop := GridBound 637009920 i ∧ LocalExactOneProblem i
def BoundedLocalExactOneThreeOccurrenceProblem (i : Input V) : Prop :=
  GridBound 637009920 i ∧ LocalExactOneThreeOccurrenceProblem i

theorem boundedLocalExactOneProblem_coRE : LeanWang.CoREPred (BoundedLocalExactOneProblem (V := V)) := by
  have upper := restricted_coRE
    ((gridBound_primrec 637009920).and
      (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and valid_primrec))
    (Primrec.snd : Primrec (fun i : Input V => i.2))
    (PeriodicExactOneCNF.formula_primrec.comp Primrec.fst)
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [BoundedLocalExactOneProblem,LocalExactOneProblem,ExactOneProblem,
      PeriodicExactOneCNF.satisfiable_iff,and_assoc]

theorem boundedLocalExactOneThreeOccurrenceProblem_coRE :
    LeanWang.CoREPred (BoundedLocalExactOneThreeOccurrenceProblem (V := V)) := by
  have upper := restricted_coRE
    ((gridBound_primrec 637009920).and
      (((PeriodicCNF.isLocal_primrec (V := V)).comp Primrec.fst).and
        (((PeriodicCNF.occurrencesAtMost_primrec 3).comp Primrec.fst).and valid_primrec)))
    (Primrec.snd : Primrec (fun i : Input V => i.2))
    (PeriodicExactOneCNF.formula_primrec.comp Primrec.fst)
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [BoundedLocalExactOneThreeOccurrenceProblem,LocalExactOneThreeOccurrenceProblem,
      ExactOneThreeOccurrenceProblem,ExactOneProblem,PeriodicExactOneCNF.satisfiable_iff,and_assoc]
end Unbounded
end PeriodicPlanarSAT
end LeanTrominoes
