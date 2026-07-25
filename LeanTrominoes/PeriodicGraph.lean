import LeanTrominoes.PeriodicOccurrences
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sigma

/-!
# Finite presentations of periodic graphs

This file introduces the graph representation used by the planarization
part of the hardness reduction.  A protoedge stores its source protovertex,
its target protovertex, and the lattice offset of the target relative to the
source.  Translating both endpoints by any lattice vector gives an edge in
the infinite periodic lift.

The incidence graph of a periodic CNF formula is also constructed.  A clause
orbit gets one protovertex, and every literal occurrence becomes an edge to
the corresponding variable orbit.  Clause offsets are normalized relative
to the first literal, which does not change the infinite translated formula.
-/

namespace LeanTrominoes

/-- One undirected protoedge.  At lattice translate `z`, it joins
`(source, z)` to `(target, z + offset)`. -/
structure PeriodicEdge (Vertex : Type*) where
  source : Vertex
  target : Vertex
  offset : Cell
  deriving DecidableEq, Repr

namespace PeriodicEdge

/-- Product representation used by the standard computability encoding. -/
def equivData {Vertex : Type*} :
    PeriodicEdge Vertex ≃ Vertex × Vertex × Cell where
  toFun edge := (edge.source, edge.target, edge.offset)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv edge := by cases edge; rfl
  right_inv data := by rcases data with ⟨source, target, offset⟩; rfl

noncomputable instance {Vertex : Type*} [Primcodable Vertex] :
    Primcodable (PeriodicEdge Vertex) :=
  Primcodable.ofEquiv (Vertex × Vertex × Cell) equivData

/-- Manhattan length of the translation between the two endpoint cells. -/
def span {Vertex : Type*} (edge : PeriodicEdge Vertex) : Nat :=
  edge.offset.1.natAbs + edge.offset.2.natAbs

/-- The two endpoint protovertices, with a loop deliberately counted twice. -/
def incidences {Vertex : Type*} (edge : PeriodicEdge Vertex) : List Vertex :=
  [edge.source, edge.target]

/-- Whether two lifted vertices are the endpoints of one translate of this
protoedge.  The disjunction makes the undirected symmetry explicit. -/
def Connects {Vertex : Type*} (edge : PeriodicEdge Vertex)
    (first second : Vertex × Cell) : Prop :=
  (∃ translate,
      first = (edge.source, translate) ∧
      second = (edge.target, Cell.add translate edge.offset)) ∨
    ∃ translate,
      second = (edge.source, translate) ∧
      first = (edge.target, Cell.add translate edge.offset)

theorem connects_symm {Vertex : Type*}
    {edge : PeriodicEdge Vertex} {first second : Vertex × Cell}
    (connects : edge.Connects first second) :
    edge.Connects second first :=
  connects.elim Or.inr Or.inl

end PeriodicEdge

/-- A finite presentation of an infinite graph invariant under every
translation in `ℤ²`. -/
structure PeriodicGraph (Vertex : Type*) where
  vertices : List Vertex
  edges : List (PeriodicEdge Vertex)
  deriving DecidableEq, Repr

namespace PeriodicGraph

/-- Pair-of-lists representation used by the computability encoding. -/
def equivData {Vertex : Type*} :
    PeriodicGraph Vertex ≃ List Vertex × List (PeriodicEdge Vertex) where
  toFun graph := (graph.vertices, graph.edges)
  invFun data := ⟨data.1, data.2⟩
  left_inv graph := by cases graph; rfl
  right_inv _ := rfl

noncomputable instance {Vertex : Type*} [Primcodable Vertex] :
    Primcodable (PeriodicGraph Vertex) :=
  Primcodable.ofEquiv (List Vertex × List (PeriodicEdge Vertex)) equivData

/-- Every listed edge names listed endpoints, and the protovertex list has no
duplicates. -/
def IsWellFormed {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : Prop :=
  graph.vertices.Nodup ∧
    ∀ edge ∈ graph.edges,
      edge.source ∈ graph.vertices ∧ edge.target ∈ graph.vertices

/-- The paper's locality condition for a graph presentation. -/
def IsLocal {Vertex : Type*} (graph : PeriodicGraph Vertex) : Prop :=
  ∀ edge ∈ graph.edges, edge.span ≤ 1

/-- All edge-end occurrences in the finite presentation. -/
def incidences {Vertex : Type*} (graph : PeriodicGraph Vertex) : List Vertex :=
  graph.edges.flatMap PeriodicEdge.incidences

/-- Every protovertex has at most `bound` incident edge ends.  A loop
contributes two, matching graph-theoretic degree. -/
def DegreeAtMost {Vertex : Type*} [BEq Vertex] [LawfulBEq Vertex]
    (bound : Nat) (graph : PeriodicGraph Vertex) : Prop :=
  ∀ vertex, graph.incidences.count vertex ≤ bound

/-- Adjacency in the infinite periodic lift. -/
def Adjacent {Vertex : Type*} (graph : PeriodicGraph Vertex)
    (first second : Vertex × Cell) : Prop :=
  ∃ edge ∈ graph.edges, edge.Connects first second

theorem adjacent_symm {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {first second : Vertex × Cell}
    (adjacent : graph.Adjacent first second) :
    graph.Adjacent second first := by
  rcases adjacent with ⟨edge, edge_mem, connects⟩
  exact ⟨edge, edge_mem, PeriodicEdge.connects_symm connects⟩

end PeriodicGraph

/-! ## Incidence graph of periodic CNF -/

/-- The two colors of vertices in a CNF incidence graph. -/
inductive CNFVertex (Variable : Type*)
  | variable (atom : Variable)
  | clause (index : Nat)
  deriving DecidableEq, Repr

namespace CNFVertex

/-- Sum representation used by the computability encoding. -/
def equivData {Variable : Type*} :
    CNFVertex Variable ≃ Sum Variable Nat where
  toFun
    | .variable atom => .inl atom
    | .clause index => .inr index
  invFun
    | .inl atom => .variable atom
    | .inr index => .clause index
  left_inv vertex := by cases vertex <;> rfl
  right_inv data := by cases data <;> rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (CNFVertex Variable) :=
  Primcodable.ofEquiv (Sum Variable Nat) equivData

end CNFVertex

namespace PeriodicCNF

/-- A clause orbit is placed at the first literal's offset.  Empty clauses
have no incidence edges, so their arbitrary anchor is irrelevant. -/
def clauseAnchor {Variable : Type*}
    (clause : PeriodicClause Variable) : Cell :=
  (clause.head?.map PeriodicLiteral.offset).getD (0, 0)

/-- The incidence edge belonging to one literal occurrence. -/
def incidenceEdge {Variable : Type*}
    (clauseIndex : Nat) (anchor : Cell)
    (literal : PeriodicLiteral Variable) :
    PeriodicEdge (CNFVertex Variable) where
  source := .clause clauseIndex
  target := .variable literal.atom
  offset := Cell.sub literal.offset anchor

/-- All incidence edges of one protoclauses. -/
def clauseIncidenceEdges {Variable : Type*}
    (clauseIndex : Nat) (clause : PeriodicClause Variable) :
    List (PeriodicEdge (CNFVertex Variable)) :=
  clause.map (incidenceEdge clauseIndex (clauseAnchor clause))

/-- Variable protovertices that actually occur, in first-occurrence order. -/
def incidenceVariableVertices {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List (CNFVertex Variable) :=
  formula.variableOccurrences.dedup.map CNFVertex.variable

/-- One clause protovertex for each entry of the finite presentation. -/
def incidenceClauseVertices {Variable : Type*}
    (formula : PeriodicCNF Variable) : List (CNFVertex Variable) :=
  (List.range formula.clauses.length).map CNFVertex.clause

/-- The finite periodic incidence graph of a periodic CNF formula. -/
def incidenceGraph {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : PeriodicGraph (CNFVertex Variable) where
  vertices :=
    incidenceVariableVertices formula ++ incidenceClauseVertices formula
  edges :=
    formula.clauses.zipIdx.flatMap fun (clause, clauseIndex) =>
      clauseIncidenceEdges clauseIndex clause

theorem incidenceVariableVertices_nodup {Variable : Type*}
    [DecidableEq Variable] (formula : PeriodicCNF Variable) :
    (incidenceVariableVertices formula).Nodup := by
  apply (List.nodup_dedup formula.variableOccurrences).map
  intro first second equality
  cases equality
  rfl

theorem incidenceClauseVertices_nodup {Variable : Type*}
    (formula : PeriodicCNF Variable) :
    (incidenceClauseVertices formula).Nodup := by
  exact (List.nodup_range :
    (List.range formula.clauses.length).Nodup).map
    (fun first second equality => by cases equality; rfl)

theorem incidenceVertices_disjoint {Variable : Type*}
    [DecidableEq Variable] (formula : PeriodicCNF Variable) :
    ∀ variableVertex ∈ incidenceVariableVertices formula,
      ∀ clauseVertex ∈ incidenceClauseVertices formula,
        variableVertex ≠ clauseVertex := by
  intro variableVertex variable_mem clauseVertex clause_mem equal
  simp only [incidenceVariableVertices, List.mem_map] at variable_mem
  simp only [incidenceClauseVertices, List.mem_map] at clause_mem
  rcases variable_mem with ⟨atom, atom_mem, rfl⟩
  rcases clause_mem with ⟨index, index_mem, rfl⟩
  cases equal

/-- The incidence construction lists every endpoint exactly in its
variable-or-clause half of the bipartition. -/
theorem incidenceGraph_isWellFormed {Variable : Type*}
    [DecidableEq Variable] (formula : PeriodicCNF Variable) :
    (incidenceGraph formula).IsWellFormed := by
  constructor
  · change
      (incidenceVariableVertices formula ++
        incidenceClauseVertices formula).Nodup
    rw [List.nodup_append]
    exact ⟨incidenceVariableVertices_nodup formula,
      incidenceClauseVertices_nodup formula,
      incidenceVertices_disjoint formula⟩
  · intro edge edge_mem
    simp only [incidenceGraph, List.mem_flatMap] at edge_mem
    rcases edge_mem with ⟨taggedClause, taggedClause_mem, edge_mem⟩
    simp only [clauseIncidenceEdges, List.mem_map] at edge_mem
    rcases edge_mem with ⟨literal, literal_mem, rfl⟩
    constructor
    · apply List.mem_append_right
      simp only [incidenceClauseVertices, List.mem_map]
      exact ⟨taggedClause.2,
        List.mem_range.mpr (List.snd_lt_of_mem_zipIdx taggedClause_mem), rfl⟩
    · apply List.mem_append_left
      simp only [incidenceVariableVertices, List.mem_map]
      refine ⟨literal.atom, List.mem_dedup.mpr ?_, rfl⟩
      unfold variableOccurrences
      apply List.mem_flatMap.mpr
      refine ⟨taggedClause.1,
        List.fst_mem_of_mem_zipIdx taggedClause_mem, ?_⟩
      exact List.mem_map.mpr ⟨literal, literal_mem, rfl⟩

theorem incidenceEdge_span_cons {Variable : Type*}
    (clauseIndex : Nat) (first literal : PeriodicLiteral Variable)
    (rest : List (PeriodicLiteral Variable)) :
    (incidenceEdge clauseIndex (clauseAnchor (first :: rest)) literal).span =
      PeriodicClause.offsetDistance first literal := by
  simp only [incidenceEdge, clauseAnchor, List.head?_cons, Option.map_some,
    Option.getD_some, PeriodicEdge.span, Cell.sub,
    PeriodicClause.offsetDistance]
  have horizontal :
      literal.offset.1 - first.offset.1 =
        -(first.offset.1 - literal.offset.1) := by omega
  have vertical :
      literal.offset.2 - first.offset.2 =
        -(first.offset.2 - literal.offset.2) := by omega
  rw [horizontal, vertical, Int.natAbs_neg, Int.natAbs_neg]

/-- Formula locality implies locality of its normalized incidence graph. -/
theorem incidenceGraph_isLocal {Variable : Type*}
    [DecidableEq Variable] {formula : PeriodicCNF Variable}
    (hLocal : formula.IsLocal) :
    (incidenceGraph formula).IsLocal := by
  intro edge edge_mem
  simp only [incidenceGraph, List.mem_flatMap] at edge_mem
  rcases edge_mem with ⟨taggedClause, taggedClause_mem, edge_mem⟩
  have clauseLocal :=
    hLocal taggedClause.1 (List.fst_mem_of_mem_zipIdx taggedClause_mem)
  simp only [clauseIncidenceEdges, List.mem_map] at edge_mem
  rcases edge_mem with ⟨literal, literal_mem, rfl⟩
  cases clause_eq : taggedClause.1 with
  | nil =>
      simp [clause_eq] at literal_mem
  | cons first rest =>
      rw [clause_eq] at clauseLocal literal_mem
      rw [incidenceEdge_span_cons]
      exact clauseLocal first (by simp) literal literal_mem

theorem clauseIncidenceEdges_variable_count_of_anchor {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex : Nat) (anchor : Cell)
    (clause : PeriodicClause Variable)
    (atom : Variable) :
    ((clause.map (incidenceEdge clauseIndex anchor)).flatMap
        PeriodicEdge.incidences).count (.variable atom) =
      (clause.map PeriodicLiteral.atom).count atom := by
  induction clause with
  | nil => simp
  | cons literal rest induction =>
      by_cases same : literal.atom = atom
      · subst atom
        simp [PeriodicEdge.incidences, incidenceEdge, induction]
      · simp [PeriodicEdge.incidences, incidenceEdge, same, induction]

theorem clauseIncidenceEdges_variable_count {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (atom : Variable) :
    ((clauseIncidenceEdges clauseIndex clause).flatMap
        PeriodicEdge.incidences).count (.variable atom) =
      (clause.map PeriodicLiteral.atom).count atom :=
  clauseIncidenceEdges_variable_count_of_anchor
    clauseIndex (clauseAnchor clause) clause atom

theorem taggedIncidenceEdges_variable_count {Variable : Type*}
    [DecidableEq Variable]
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (atom : Variable) :
    (taggedClauses.flatMap (fun tagged =>
        clauseIncidenceEdges tagged.2 tagged.1) |>.flatMap
          PeriodicEdge.incidences).count (.variable atom) =
      (taggedClauses.flatMap fun tagged =>
        tagged.1.map PeriodicLiteral.atom).count atom := by
  induction taggedClauses with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.flatMap_cons]
      rw [List.flatMap_append, List.count_append]
      rw [clauseIncidenceEdges_variable_count tagged.2 tagged.1 atom,
        induction]
      rw [List.count_append]

theorem zipIdx_flatMap_fst {α β : Type*}
    (function : α → List β) (values : List α) (start : Nat) :
    (values.zipIdx start).flatMap (fun tagged => function tagged.1) =
      values.flatMap function := by
  rw [← List.flatMap_map]
  simp

theorem incidenceGraph_variable_degree {Variable : Type*}
    [DecidableEq Variable] (formula : PeriodicCNF Variable)
    (atom : Variable) :
    (incidenceGraph formula).incidences.count (.variable atom) =
      formula.variableOccurrences.count atom := by
  rw [show (incidenceGraph formula).incidences =
    (formula.clauses.zipIdx.flatMap fun tagged =>
      clauseIncidenceEdges tagged.2 tagged.1).flatMap
        PeriodicEdge.incidences by rfl]
  rw [taggedIncidenceEdges_variable_count]
  rw [zipIdx_flatMap_fst]
  rfl

theorem clauseIncidenceEdges_clause_count_of_anchor {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex wantedIndex : Nat) (anchor : Cell)
    (clause : PeriodicClause Variable) :
    ((clause.map (incidenceEdge clauseIndex anchor)).flatMap
        PeriodicEdge.incidences).count (.clause wantedIndex) =
      if clauseIndex = wantedIndex then clause.length else 0 := by
  induction clause with
  | nil => simp
  | cons literal rest induction =>
      by_cases same : clauseIndex = wantedIndex
      · subst wantedIndex
        simp [PeriodicEdge.incidences, incidenceEdge, induction]
      · simp [PeriodicEdge.incidences, incidenceEdge, same, induction]

theorem clauseIncidenceEdges_clause_count {Variable : Type*}
    [DecidableEq Variable]
    (clauseIndex wantedIndex : Nat)
    (clause : PeriodicClause Variable) :
    ((clauseIncidenceEdges clauseIndex clause).flatMap
        PeriodicEdge.incidences).count (.clause wantedIndex) =
      if clauseIndex = wantedIndex then clause.length else 0 :=
  clauseIncidenceEdges_clause_count_of_anchor
    clauseIndex wantedIndex (clauseAnchor clause) clause

theorem taggedIncidenceEdges_clause_count {Variable : Type*}
    [DecidableEq Variable]
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (wantedIndex : Nat) :
    (taggedClauses.flatMap (fun tagged =>
        clauseIncidenceEdges tagged.2 tagged.1) |>.flatMap
          PeriodicEdge.incidences).count (.clause wantedIndex) =
      (taggedClauses.map fun tagged =>
        if tagged.2 = wantedIndex then tagged.1.length else 0).sum := by
  induction taggedClauses with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.flatMap_cons]
      rw [List.flatMap_append, List.count_append]
      rw [clauseIncidenceEdges_clause_count, induction]
      rfl

theorem clauseWeight_sum_eq_zero_of_not_mem {Variable : Type*}
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (wantedIndex : Nat)
    (absent : wantedIndex ∉ taggedClauses.map Prod.snd) :
    (taggedClauses.map fun tagged =>
      if tagged.2 = wantedIndex then tagged.1.length else 0).sum = 0 := by
  induction taggedClauses with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      have different : tagged.2 ≠ wantedIndex := by
        intro equal
        exact absent.1 equal.symm
      simp [different, induction absent.2]

theorem clauseWeight_sum_le_of_nodup {Variable : Type*}
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (wantedIndex bound : Nat)
    (indicesNodup : (taggedClauses.map Prod.snd).Nodup)
    (width : ∀ tagged ∈ taggedClauses, tagged.1.length ≤ bound) :
    (taggedClauses.map fun tagged =>
      if tagged.2 = wantedIndex then tagged.1.length else 0).sum ≤ bound := by
  induction taggedClauses with
  | nil => simp
  | cons tagged rest induction =>
      simp only [List.map_cons] at indicesNodup
      rw [List.nodup_cons] at indicesNodup
      by_cases same : tagged.2 = wantedIndex
      · have absent : wantedIndex ∉ rest.map Prod.snd := by
          rw [← same]
          exact indicesNodup.1
        simp only [List.map_cons, List.sum_cons, if_pos same]
        rw [clauseWeight_sum_eq_zero_of_not_mem rest wantedIndex absent,
          add_zero]
        exact width tagged (by simp)
      · simp only [List.map_cons, List.sum_cons, if_neg same, zero_add]
        exact induction indicesNodup.2
          (fun later later_mem => width later (by simp [later_mem]))

/-- Clause-vertex degree is bounded by the corresponding formula-width
bound. -/
theorem incidenceGraph_clause_degree_le {Variable : Type*}
    [DecidableEq Variable] {formula : PeriodicCNF Variable}
    {bound : Nat} (width : formula.WidthAtMost bound)
    (clauseIndex : Nat) :
    (incidenceGraph formula).incidences.count (.clause clauseIndex) ≤
      bound := by
  rw [show (incidenceGraph formula).incidences =
    (formula.clauses.zipIdx.flatMap fun tagged =>
      clauseIncidenceEdges tagged.2 tagged.1).flatMap
        PeriodicEdge.incidences by rfl]
  rw [taggedIncidenceEdges_clause_count]
  apply clauseWeight_sum_le_of_nodup
  · exact List.nodup_zipIdx_map_snd formula.clauses
  · intro tagged tagged_mem
    exact width tagged.1 (List.fst_mem_of_mem_zipIdx tagged_mem)

/-- Width and occurrence bounds become the ordinary maximum-degree bound on
the periodic incidence graph. -/
theorem incidenceGraph_degreeAtMost {Variable : Type*}
    [DecidableEq Variable] {formula : PeriodicCNF Variable}
    {bound : Nat} (width : formula.WidthAtMost bound)
    (occurrences : formula.OccurrencesAtMost bound) :
    (incidenceGraph formula).DegreeAtMost bound := by
  intro vertex
  cases vertex with
  | «variable» atom =>
      rw [incidenceGraph_variable_degree]
      exact occurrences atom
  | clause clauseIndex =>
      exact incidenceGraph_clause_degree_le width clauseIndex

end PeriodicCNF

end LeanTrominoes
