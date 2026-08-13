/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFGaugeComputability
import LeanTrominoes.PeriodicGridDrawingComputability
import LeanTrominoes.PeriodicThreeSATThreeComputability

/-!
# Computability of periodic CNF incidence graphs

The finite bipartite incidence graph of a periodic CNF presentation is
primitive recursive.  This module supplies the constructor/accessor lemmas
for its tagged vertices and proves primitive recursiveness of the complete
vertex and edge enumeration.  It is the graph-level entry point for the
computability proof of retained planarization.
-/

noncomputable section

namespace LeanTrominoes

namespace CNFVertex

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@CNFVertex.equivData Variable) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@CNFVertex.equivData Variable).symm :=
  Primrec.of_equiv_symm

theorem variable_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@CNFVertex.variable Variable) :=
  equivData_symm_primrec.comp Primrec.sumInl

theorem clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@CNFVertex.clause Variable) :=
  equivData_symm_primrec.comp Primrec.sumInr

end CNFVertex

namespace PeriodicCNF

theorem variableOccurrences_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PeriodicCNF.variableOccurrences :
      PeriodicCNF Variable → List Variable) := by
  have row : Primrec₂ fun (_source : PeriodicCNF Variable)
      (clause : PeriodicClause Variable) =>
      clause.map PeriodicLiteral.atom := by
    exact Primrec.list_map Primrec.snd
      (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd).to₂
  exact Primrec.list_flatMap PeriodicCNF.equivData_primrec row

theorem incidenceEdge_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : (Nat × Cell) × PeriodicLiteral Variable =>
      incidenceEdge input.1.1 input.1.2 input.2 := by
  have source : Primrec fun input :
      (Nat × Cell) × PeriodicLiteral Variable =>
      (CNFVertex.clause input.1.1 : CNFVertex Variable) :=
    (CNFVertex.clause_primrec (Variable := Variable)).comp
      (Primrec.fst.comp Primrec.fst)
  have target : Primrec fun input :
      (Nat × Cell) × PeriodicLiteral Variable =>
      CNFVertex.variable input.2.atom :=
    CNFVertex.variable_primrec.comp
      (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd)
  have offset : Primrec fun input :
      (Nat × Cell) × PeriodicLiteral Variable =>
      Cell.sub input.2.offset input.1.2 :=
    Computability.cell_sub_primrec.comp
      (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact ((PeriodicEdge.equivData_symm_primrec
      (Vertex := CNFVertex Variable)).comp
    (Primrec.pair source (Primrec.pair target offset))).of_eq
      fun _ => rfl

theorem clauseIncidenceEdges_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec₂ (clauseIncidenceEdges :
      Nat → PeriodicClause Variable →
        List (PeriodicEdge (CNFVertex Variable))) := by
  change Primrec fun input : Nat × PeriodicClause Variable =>
    clauseIncidenceEdges input.1 input.2
  have one : Primrec₂ fun
      (input : Nat × PeriodicClause Variable)
      (literal : PeriodicLiteral Variable) =>
      incidenceEdge input.1 (clauseAnchor input.2) literal := by
    exact incidenceEdge_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (PeriodicCNF.clauseAnchor_primrec.comp
            (Primrec.snd.comp Primrec.fst)))
        Primrec.snd)
  exact (Primrec.list_map Primrec.snd one).of_eq fun _ => rfl

theorem incidenceVariableVertices_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (incidenceVariableVertices :
      PeriodicCNF Variable → List (CNFVertex Variable)) := by
  have atoms : Primrec fun formula : PeriodicCNF Variable =>
      formula.variableOccurrences.dedup :=
    PeriodicThreeSATThree.dedup_primrec.comp
      variableOccurrences_primrec
  exact Primrec.list_map atoms
    (CNFVertex.variable_primrec.comp Primrec.snd).to₂

theorem incidenceClauseVertices_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (incidenceClauseVertices :
      PeriodicCNF Variable → List (CNFVertex Variable)) := by
  have indices : Primrec fun formula : PeriodicCNF Variable =>
      List.range formula.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicCNF.equivData_primrec)
  exact Primrec.list_map indices
    (CNFVertex.clause_primrec.comp Primrec.snd).to₂

theorem incidenceGraph_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (incidenceGraph :
      PeriodicCNF Variable → PeriodicGraph (CNFVertex Variable)) := by
  have vertices : Primrec fun formula : PeriodicCNF Variable =>
      incidenceVariableVertices formula ++
        incidenceClauseVertices formula :=
    Primrec.list_append.comp
      incidenceVariableVertices_primrec
      incidenceClauseVertices_primrec
  have taggedClauses : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicCNF.equivData_primrec
  have edges : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses.zipIdx.flatMap fun tagged =>
        clauseIncidenceEdges tagged.2 tagged.1 := by
    apply Primrec.list_flatMap taggedClauses
    exact (clauseIncidenceEdges_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)).to₂
  exact (PeriodicGraph.equivData_symm_primrec.comp
    (Primrec.pair vertices edges)).of_eq fun _ => rfl

theorem incidenceGraph_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (incidenceGraph :
      PeriodicCNF Variable → PeriodicGraph (CNFVertex Variable)) :=
  incidenceGraph_primrec.to_comp

end PeriodicCNF

end LeanTrominoes
