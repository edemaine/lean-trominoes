/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingConstruction

/-!
# Size of a periodic-CNF incidence graph

The orthocrossing grid size depends only on the number of finite incidence
vertices and edges.  This file bounds both by the clause and literal counts
of the input presentation.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Number of literal occurrences in a finite periodic-CNF presentation. -/
def presentationLiteralCount {Variable : Type*}
    (formula : PeriodicCNF Variable) : Nat :=
  formula.clauses.flatten.length

/-- Clause entries plus literal entries in the finite presentation. -/
def presentationSize {Variable : Type*}
    (formula : PeriodicCNF Variable) : Nat :=
  formula.clauses.length + presentationLiteralCount formula

theorem presentationLiteralCount_le_mul_of_width
    {Variable : Type*} (formula : PeriodicCNF Variable) (width : Nat)
    (widthBound : formula.WidthAtMost width) :
    presentationLiteralCount formula ≤ formula.clauses.length * width := by
  rcases formula with ⟨clauses⟩
  induction clauses with
  | nil => simp [presentationLiteralCount]
  | cons clause clauses induction =>
      have head : clause.length ≤ width := widthBound clause (by simp)
      have tail : (PeriodicCNF.mk clauses).WidthAtMost width := by
        intro member memberMem
        exact widthBound member (by simp [memberMem])
      have tailBound := induction tail
      simp only [presentationLiteralCount, List.flatten_cons,
        List.length_append, List.length_cons]
      change clauses.flatten.length ≤ clauses.length * width at tailBound
      rw [Nat.add_mul, one_mul]
      omega

@[simp] theorem variableOccurrences_length
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    formula.variableOccurrences.length =
      presentationLiteralCount formula := by
  simp [PeriodicCNF.variableOccurrences, presentationLiteralCount]

@[simp] theorem incidenceGraph_edges_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    formula.incidenceGraph.edges.length =
      presentationLiteralCount formula := by
  simp [PeriodicCNF.incidenceGraph, PeriodicCNF.clauseIncidenceEdges,
    presentationLiteralCount]
  calc
    (List.map (fun item => item.1.length) formula.clauses.zipIdx).sum =
        (List.map List.length
          (formula.clauses.zipIdx.map Prod.fst)).sum := by
      apply congrArg List.sum
      rw [List.map_map]
      apply List.map_congr_left
      intro item itemMember
      rfl
    _ = (List.map List.length formula.clauses).sum := by
      rw [List.zipIdx_map_fst]

theorem incidenceGraph_vertices_length_le
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    formula.incidenceGraph.vertices.length ≤
      presentationLiteralCount formula + formula.clauses.length := by
  simp only [PeriodicCNF.incidenceGraph, List.length_append,
    PeriodicCNF.incidenceVariableVertices,
    PeriodicCNF.incidenceClauseVertices, List.length_map,
    List.length_range]
  simpa only [variableOccurrences_length] using
    Nat.add_le_add_right
      (List.Sublist.length_le
        (List.dedup_sublist formula.variableOccurrences))
      formula.clauses.length

/-- The generic orthocrossing grid is linear in the finite CNF presentation. -/
theorem drawingGridSize_incidenceGraph_le
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicOrthocrossing.drawingGridSize formula.incidenceGraph ≤
      16 * (2 * presentationLiteralCount formula +
        formula.clauses.length + 1) := by
  unfold PeriodicOrthocrossing.drawingGridSize
  have vertices := incidenceGraph_vertices_length_le formula
  rw [incidenceGraph_edges_length]
  omega

theorem drawingGridSize_incidenceGraph_le_presentationSize
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicOrthocrossing.drawingGridSize formula.incidenceGraph ≤
      16 * (2 * presentationSize formula + 1) := by
  exact (drawingGridSize_incidenceGraph_le formula).trans (by
    unfold presentationSize
    omega)

end PeriodicCNF
end LeanTrominoes
