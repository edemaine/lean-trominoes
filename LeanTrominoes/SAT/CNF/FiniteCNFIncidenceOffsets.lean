/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteCNFZeroOffsets
import LeanTrominoes.SAT.CNF.Incidence
import LeanTrominoes.SAT.CNF.PeriodicCNFIncidenceMetadataData

/-! # Incidence edges of finite formulas have zero displacement -/
namespace LeanTrominoes.FiniteCNF

theorem clauseAnchor_zero {V : Type*} (clause : PeriodicClause V)
    (zero : ∀ literal∈clause, literal.offset=(0,0)) : PeriodicCNF.clauseAnchor clause=(0,0) := by
  cases clause with
  | nil => rfl
  | cons literal rest => exact zero literal (by simp)

theorem incidenceGraph_zero {V : Type*} [DecidableEq V] (formula : PeriodicCNF V)
    (zero : ZeroOffsets formula) : ∀ edge∈formula.incidenceGraph.edges, edge.offset=(0,0) := by
  intro edge member
  obtain ⟨tagged,taggedMem,member⟩ := List.mem_flatMap.mp member
  obtain ⟨literal,literalMem,edgeEq⟩ := List.mem_map.mp member
  subst edge
  have clauseMem := List.fst_mem_of_mem_zipIdx taggedMem
  simp [PeriodicCNF.incidenceEdge,zero tagged.1 clauseMem literal literalMem,
    clauseAnchor_zero tagged.1 (zero tagged.1 clauseMem),Cell.sub]

end LeanTrominoes.FiniteCNF
