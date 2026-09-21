/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteVariableLoop
import LeanTrominoes.PeriodicPlanarSATRouteIncidenceBounds
import LeanTrominoes.PeriodicPlanarSATRouteAddressObligation

/-! # The literal loop checks the corresponding incidence route -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr
open RouteInput PeriodicCNF PeriodicCNF.FlatScanner PeriodicCNF.IncidenceFields PeriodicCNFFlatEncoding

def literalCheck (input : Input Nat) (h : Nat) (c : PeriodicClause Nat) (k : Nat) (hk : k<c.length) : Prop :=
  let edge := incidenceEdge (Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h) (clauseAnchor c) c[k]
  let route := input.2.edgeRoute (Count.count literalMarkExpr (FieldSavitch.suffix input.1) (h+1+4*k))
  route.head? = some (input.2.vertexPosition input.1.incidenceGraph edge.source) ∧
    route.getLast? = some (Cell.add (input.2.vertexPosition input.1.incidenceGraph edge.target)
      (input.2.periodTranslation edge.offset))

theorem edgeRank_value (input : Input Nat) (k ci h v : Nat) :
    edgeRank.value ([k,ci,h,v]++context input) = Count.count literalMarkExpr (FieldSavitch.suffix input.1) (h+1+4*k) := by
  change Count.count (formulaQuery 4 literalMarkExpr) ([k,ci,h,v]++context input) (h+1+4*k) = _
  simpa only [List.length_cons,List.length_nil,Nat.reduceAdd] using formulaQuery_count literalMarkExpr input [k,ci,h,v] (h+1+4*k)

theorem literalBody_truth (input : Input Nat) (valid : IncidenceCounts.Valid input)
    (h : Nat) (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses) (k : Nat) (hk : k<c.length) :
    literalBody.value ([k,Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h,h,input.1.variableOccurrences.dedup.length]++context input) ≠ 0 ↔
      literalCheck input h c k hk := by
  let ci := Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h
  let e := Count.count literalMarkExpr (FieldSavitch.suffix input.1) (h+1+4*k)
  let v := input.1.variableOccurrences.dedup.length
  have he := literalRank_bound input valid h c hc k hk
  have hs := sourceRank_bound input valid h c hc
  have ha := literal_atom_member input.1 h c hc k hk
  have ht := targetRank_bound input valid c[k].atom ha
  change representatives.value (edgeRank.value ([k,ci,h,v]++context input)::([k,ci,h,v]++context input)) ≠ 0 ↔ _
  rw [edgeRank_value]
  have checked := representatives_truth input e k ci h v he hs c hc hk ha ht
  change representatives.value ([e,k,ci,h,v]++context input) ≠ 0 ↔ _
  rw [checked]
  unfold literalCheck PeriodicGridDrawing.edgeRoute PeriodicGridDrawing.vertexPosition
  simp only [incidenceEdge,incidenceGraph_clause_vertexIndex input.1 (Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h) (clauseRank_bound input.1 h c hc),
    incidenceGraph_variable_vertexIndex input.1 c[k].atom ha]
  rw [List.getD_eq_getElem _ _ he,List.getD_eq_getElem _ _ hs,List.getD_eq_getElem _ _ ht]

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
