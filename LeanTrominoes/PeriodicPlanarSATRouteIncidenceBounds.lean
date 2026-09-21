/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceEdgeAddressMembers
import LeanTrominoes.PeriodicCNFIncidenceVertexIndices
import LeanTrominoes.PeriodicPlanarSATIncidenceCounts

/-! # Every endpoint query lies inside the supplied incidence arrays -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open PeriodicCNF PeriodicCNF.FlatScanner PeriodicCNF.IncidenceFields BoundedArithmetic

theorem clauseRank_bound (f : PeriodicCNF Nat) (h : Nat) (c : PeriodicClause Nat)
    (hc : (h,c)∈clauseEntries 1 f.clauses) :
    Count.count clauseMarkExpr (FieldSavitch.suffix f) h < f.clauses.length := by
  have info := List.mem_zipIdx (clause_tagged_member f h c hc)
  simpa only [Nat.zero_add,clauseEntries_length] using info.2.1

theorem literal_atom_member (f : PeriodicCNF Nat) (h : Nat) (c : PeriodicClause Nat)
    (hc : (h,c)∈clauseEntries 1 f.clauses) (k : Nat) (hk : k<c.length) :
    c[k].atom∈f.variableOccurrences.dedup := by
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  exact ⟨c,(clauseEntries_members 1 f.clauses c).mp ⟨h,hc⟩,
    List.mem_map.mpr ⟨c[k],List.getElem_mem hk,rfl⟩⟩

theorem literalRank_bound (input : Input Nat) (valid : IncidenceCounts.Valid input)
    (h : Nat) (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses)
    (k : Nat) (hk : k<c.length) :
    Count.count literalMarkExpr (FieldSavitch.suffix input.1) (h+1+4*k) < input.2.edgeRoutes.length := by
  have member := (edgeEntries_mem_iff input.1
    (h+1+4*k,incidenceEdge (Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h) (clauseAnchor c) c[k])).mpr
    ⟨h,c,hc,k,hk,rfl⟩
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp member
  have rank := edgeEntries_rank input.1 i hi
  rw [eq] at rank
  rw [rank,valid.2]
  have lengths := congrArg List.length (edgeEntries_formula_values input.1)
  simp only [List.length_map] at lengths
  omega

theorem sourceRank_bound (input : Input Nat) (valid : IncidenceCounts.Valid input)
    (h : Nat) (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses) :
    input.1.variableOccurrences.dedup.length+Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h < input.2.vertexPositions.length := by
  rw [valid.1]
  have bound := clauseRank_bound input.1 h c hc
  simp only [incidenceGraph,incidenceVariableVertices,incidenceClauseVertices,List.length_append,List.length_map,List.length_range]
  omega

theorem targetRank_bound (input : Input Nat) (valid : IncidenceCounts.Valid input)
    (a : Nat) (ha : a∈input.1.variableOccurrences.dedup) :
    input.1.variableOccurrences.dedup.idxOf a < input.2.vertexPositions.length := by
  rw [valid.1]
  have bound := List.idxOf_lt_length_iff.mpr ha
  simp only [incidenceGraph,incidenceVariableVertices,incidenceClauseVertices,List.length_append,List.length_map,List.length_range]
  omega

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
