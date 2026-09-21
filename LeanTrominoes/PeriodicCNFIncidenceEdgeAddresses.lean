/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceClauseRanks
import LeanTrominoes.PeriodicGraph

/-! # Incidence edges ordered by their literal addresses -/
namespace LeanTrominoes.PeriodicCNF.IncidenceFields
open FlatScanner BoundedArithmetic

def edgeEntries (start clauseIndex : Nat) : List (PeriodicClause Nat) → List (Nat × PeriodicEdge (CNFVertex Nat))
  | [] => []
  | c::cs => (literalEntries (start+1) c).map (fun e => (e.1,incidenceEdge clauseIndex (clauseAnchor c) e.2)) ++
      edgeEntries (start+1+4*c.length) (clauseIndex+1) cs

theorem edgeEntries_addresses (start clauseIndex : Nat) (cs : List (PeriodicClause Nat)) :
    (edgeEntries start clauseIndex cs).map Prod.fst = (allLiteralEntries start cs).map Prod.fst := by
  induction cs generalizing start clauseIndex with
  | nil => rfl
  | cons c cs ih => simp [edgeEntries,allLiteralEntries,List.map_map,Function.comp_def,ih]

theorem literalEntries_values (start : Nat) (ls : List (PeriodicLiteral Nat)) :
    (literalEntries start ls).map Prod.snd = ls := by
  induction ls generalizing start with
  | nil => rfl
  | cons l ls ih => simp [literalEntries,ih]

theorem edgeEntries_values (start clauseIndex : Nat) (cs : List (PeriodicClause Nat)) :
    (edgeEntries start clauseIndex cs).map Prod.snd =
      (cs.zipIdx clauseIndex).flatMap (fun e => clauseIncidenceEdges e.2 e.1) := by
  induction cs generalizing start clauseIndex with
  | nil => rfl
  | cons c cs ih =>
    simp only [edgeEntries,List.map_append,List.map_map,Function.comp_def,List.zipIdx_cons,List.flatMap_cons,ih,clauseIncidenceEdges]
    congr 1
    exact (List.map_map ..).symm.trans (congrArg (List.map (incidenceEdge clauseIndex (clauseAnchor c))) (literalEntries_values _ _))

theorem edgeEntries_by_clauses (start clauseIndex : Nat) (cs : List (PeriodicClause Nat)) :
    edgeEntries start clauseIndex cs = ((clauseEntries start cs).zipIdx clauseIndex).flatMap
      (fun e => (literalEntries (e.1.1+1) e.1.2).map
        (fun l => (l.1,incidenceEdge e.2 (clauseAnchor e.1.2) l.2))) := by
  induction cs generalizing start clauseIndex with
  | nil => rfl
  | cons c cs ih => simp [edgeEntries,clauseEntries,List.zipIdx_cons,ih]

theorem edgeEntries_formula_values (f : PeriodicCNF Nat) :
    (edgeEntries 1 0 f.clauses).map Prod.snd = f.incidenceGraph.edges := edgeEntries_values 1 0 f.clauses

theorem edgeEntries_rank (f : PeriodicCNF Nat) (i : Nat) (hi : i<(edgeEntries 1 0 f.clauses).length) :
    Count.count literalMarkExpr (FieldSavitch.suffix f) ((edgeEntries 1 0 f.clauses)[i]).1 = i := by
  rw [literal_rank_count]
  have equal : ((allLiteralEntries 1 f.clauses).filter fun e => decide (e.1 < ((edgeEntries 1 0 f.clauses)[i]).1)).length =
      ((edgeEntries 1 0 f.clauses).filter fun e => decide (e.1 < ((edgeEntries 1 0 f.clauses)[i]).1)).length := by
    have h := congrArg (fun l : List Nat => (l.filter fun p => decide (p<((edgeEntries 1 0 f.clauses)[i]).1)).length)
      (edgeEntries_addresses 1 0 f.clauses)
    simpa only [List.filter_map,List.length_map,Function.comp_def] using h.symm
  rw [equal]
  apply SortedAddressRank.before_get_length _ _ i hi
  rw [edgeEntries_addresses]
  exact allLiteralEntries_sorted _ _

end LeanTrominoes.PeriodicCNF.IncidenceFields
