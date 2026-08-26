/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedRecordBlocks

/-! # Local route-triple blocks of direct sparse assignment records -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- The predecessor, current point, and successor determining one internal
route cell. -/
structure SparseRouteTriple where
  before : Cell
  current : Cell
  after : Cell
  deriving DecidableEq, Repr

/-- Consecutive triples of route points, in the same order as the route's
internal cells. -/
def sparseRouteTriples : List Cell → List SparseRouteTriple
  | before :: current :: after :: rest =>
      ⟨before, current, after⟩ ::
        sparseRouteTriples (current :: after :: rest)
  | _ => []
termination_by points => points.length

/-- The strip assignment determined by one consecutive route triple. -/
def sparseRouteTripleAssignment (period : Nat) (color : WireColor)
    (triple : SparseRouteTriple) :
    Cell × OrthogonalCellType :=
  (PeriodicThreeDM.stripRasterLocation period triple.current,
    PeriodicThreeDM.routingCellTypeAt
      triple.before triple.current triple.after color)

/-- The one canonical assignment record determined by a route triple. -/
def sparseRouteTripleRecordBlock (period : Nat) (color : WireColor)
    (triple : SparseRouteTriple) :
    List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentTokens
    (sparseRouteTripleAssignment period color triple)

theorem stripRouteInteriorAssignments_eq_map_triples
    (period : Nat) (color : WireColor) (route : List Cell) :
    PeriodicThreeDM.stripRouteInteriorAssignments period color route =
      (sparseRouteTriples route).map
        (sparseRouteTripleAssignment period color) := by
  fun_induction PeriodicThreeDM.stripRouteInteriorAssignments
      period color route with
  | case1 before current after rest induction =>
      simp [sparseRouteTriples, sparseRouteTripleAssignment, induction]
  | case2 points noTriple =>
      cases points with
      | nil => simp [sparseRouteTriples]
      | cons before tail =>
          cases tail with
          | nil => simp [sparseRouteTriples]
          | cons current tail =>
              cases tail with
              | nil => simp [sparseRouteTriples]
              | cons after rest =>
                  exact (noTriple before current after rest rfl).elim

/-- An edge's record block is a concatenation of independent one-cell blocks
indexed by consecutive triples of its final normalized route. -/
theorem sparseRouteRecordBlock_eq_tripleBlocks
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (edge : PeriodicThreeDM.ContractedEdge) :
    sparseRouteRecordBlock input edge =
      (sparseRouteTriples
        (PeriodicThreeDM.NormalizationCompiler.finalNormalizationRoute
          input edge)).flatMap
        (sparseRouteTripleRecordBlock
          (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod
            input)
          edge.color) := by
  unfold sparseRouteRecordBlock
  rw [stripRouteInteriorAssignments_eq_map_triples]
  exact GadgetSparseAssignmentTokens.assignmentsTokens_map _ _

theorem sparseRouteRecordBlocks_eq_tripleBlocks
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (edges : List PeriodicThreeDM.ContractedEdge) :
    edges.flatMap (sparseRouteRecordBlock input) =
      edges.flatMap fun edge =>
        (sparseRouteTriples
          (PeriodicThreeDM.NormalizationCompiler.finalNormalizationRoute
            input edge)).flatMap
          (sparseRouteTripleRecordBlock
            (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod
              input)
            edge.color) := by
  induction edges with
  | nil => rfl
  | cons edge edges induction =>
      simp only [List.flatMap_cons]
      rw [sparseRouteRecordBlock_eq_tripleBlocks, induction]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Named proof-free target for the route compiler: contracted edges in their
canonical order, with one canonical record block for each consecutive triple
of the edge's final normalized route. -/
noncomputable def directSparseComputedRouteTripleRecordsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAssignmentTokens.Token :=
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  input.problem.contractedEdges.flatMap fun edge =>
    (sparseRouteTriples
      (PeriodicThreeDM.NormalizationCompiler.finalNormalizationRoute
        input edge)).flatMap
      (sparseRouteTripleRecordBlock
        (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod
          input)
        edge.color)

/-- The direct route-record suffix is an edge-major, route-triple-minor flat
map of local canonical record blocks. -/
theorem directSparseComputedRouteRecordsOfSymbols_eq_tripleBlocks
    (symbols : List encoding.Γ) :
    directSparseComputedRouteRecordsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedEdges.flatMap fun edge =>
        (sparseRouteTriples
          (PeriodicThreeDM.NormalizationCompiler.finalNormalizationRoute
            input edge)).flatMap
          (sparseRouteTripleRecordBlock
            (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod
              input)
            edge.color) := by
  rw [directSparseComputedRouteRecordsOfSymbols_eq_blocks]
  exact sparseRouteRecordBlocks_eq_tripleBlocks _ _

/-- The named local-triple target is exactly the canonical route-record
suffix required by the sparse assignment compiler. -/
theorem directSparseComputedRouteRecordsOfSymbols_eq_tripleRecords
    (symbols : List encoding.Γ) :
    directSparseComputedRouteRecordsOfSymbols decider symbols =
      directSparseComputedRouteTripleRecordsOfSymbols decider symbols := by
  rw [directSparseComputedRouteRecordsOfSymbols_eq_tripleBlocks]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
