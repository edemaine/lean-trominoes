/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceEdgeAddresses
import LeanTrominoes.PeriodicGridDrawing

/-! # Replacing incidence-edge indices with native literal-address ranks -/
namespace LeanTrominoes.PeriodicPlanarSAT
open PeriodicCNF.IncidenceFields BoundedArithmetic

def AddressRoutesMatch (f : PeriodicCNF Nat) (d : PeriodicGridDrawing) : Prop :=
  ∀ entry ∈ edgeEntries 1 0 f.clauses,
    let route := d.edgeRoute (Count.count literalMarkExpr (PeriodicCNF.FieldSavitch.suffix f) entry.1)
    route.head? = some (d.vertexPosition f.incidenceGraph entry.2.source) ∧
      route.getLast? = some (Cell.add (d.vertexPosition f.incidenceGraph entry.2.target)
        (d.periodTranslation entry.2.offset))

theorem addressRoutesMatch_iff (f : PeriodicCNF Nat) (d : PeriodicGridDrawing) :
    AddressRoutesMatch f d ↔ d.RoutesMatch f.incidenceGraph := by
  have lengths : (edgeEntries 1 0 f.clauses).length = f.incidenceGraph.edges.length := by
    have h := congrArg List.length (edgeEntries_formula_values f)
    simpa only [List.length_map] using h
  have atIndex (i : Nat) (hi : i<(edgeEntries 1 0 f.clauses).length) :
      ((edgeEntries 1 0 f.clauses)[i]).2 = f.incidenceGraph.edges[i]'(by omega) := by
    have h := congrArg (fun l : List (PeriodicEdge (CNFVertex Nat)) => l[i]?) (edgeEntries_formula_values f)
    simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
      List.getElem?_eq_getElem (show i<f.incidenceGraph.edges.length by omega),Option.some.injEq] using h
  constructor
  · intro check tagged member
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp member
    have bound : i<f.incidenceGraph.edges.length := by simpa using hi
    have entryBound : i<(edgeEntries 1 0 f.clauses).length := by omega
    have checked := check _ (List.getElem_mem entryBound)
    dsimp only at checked
    rw [edgeEntries_rank f i entryBound,atIndex i entryBound] at checked
    rw [List.getElem_zipIdx] at eq
    simpa only [Nat.zero_add,← eq] using checked
  · intro check entry member
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp member
    have bound : i<f.incidenceGraph.edges.length := by omega
    have tagged : (f.incidenceGraph.edges[i],i) ∈ f.incidenceGraph.edges.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem bound]
    have checked := check _ tagged
    dsimp only at checked
    rw [← atIndex i hi] at checked
    dsimp only
    rw [← eq,edgeEntries_rank f i hi]
    exact checked

end LeanTrominoes.PeriodicPlanarSAT
