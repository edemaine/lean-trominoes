/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFInjectiveRenaming
import LeanTrominoes.PeriodicCNFIncidenceVertexIndices
import LeanTrominoes.PeriodicGraphOrbitCertificate

/-! # An injective atom renaming preserves the same stored incidence drawing -/
namespace LeanTrominoes.PeriodicCNF
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def renameVertex (g : V → W) : CNFVertex V → CNFVertex W
  | .variable a => .variable (g a)
  | .clause i => .clause i

def renameEdge (g : V → W) (e : PeriodicEdge (CNFVertex V)) : PeriodicEdge (CNFVertex W) :=
  ⟨renameVertex g e.source,renameVertex g e.target,e.offset⟩

omit [DecidableEq V] [DecidableEq W] in
theorem renameVertex_injective (g : V → W) (hg : Function.Injective g) : Function.Injective (renameVertex g) := by
  intro a b eq
  cases a <;> cases b <;> simp only [renameVertex,CNFVertex.variable.injEq,CNFVertex.clause.injEq] at eq ⊢
  · exact hg eq
  · cases eq
  · cases eq
  · exact eq

theorem incidence_vertices_rename (g : V → W) (hg : Function.Injective g) (f : PeriodicCNF V) :
    (f.rename g).incidenceGraph.vertices = f.incidenceGraph.vertices.map (renameVertex g) := by
  have clauses : (f.rename g).clauses.length=f.clauses.length := by simp [rename]
  simp only [incidenceGraph,incidenceVariableVertices,incidenceClauseVertices,variableOccurrences_rename,
    List.dedup_map_of_injective hg,clauses,List.map_append,List.map_map,Function.comp_def]
  rfl

theorem incidence_edges_rename (g : V → W) (f : PeriodicCNF V) :
    (f.rename g).incidenceGraph.edges = f.incidenceGraph.edges.map (renameEdge g) := by
  have anchor (c : PeriodicClause V) : clauseAnchor (renameClause g c)=clauseAnchor c := by cases c <;> rfl
  simp only [incidenceGraph,rename,List.zipIdx_map,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro e _
  simp only [clauseIncidenceEdges,renameClause,List.map_map,Function.comp_def,Prod.map_fst,Prod.map_snd,id_eq]
  apply List.map_congr_left
  intro l _
  change incidenceEdge e.2 (clauseAnchor (renameClause g e.1)) (l.rename g) = renameEdge g (incidenceEdge e.2 (clauseAnchor e.1) l)
  rw [anchor]
  rfl

theorem vertexPosition_rename (g : V → W) (hg : Function.Injective g) (f : PeriodicCNF V)
    (d : PeriodicGridDrawing) (v : CNFVertex V) :
    d.vertexPosition (f.rename g).incidenceGraph (renameVertex g v)=d.vertexPosition f.incidenceGraph v := by
  unfold PeriodicGridDrawing.vertexPosition
  rw [incidence_vertices_rename g hg,List.idxOf_map_of_injective _ (renameVertex_injective g hg)]

theorem routesMatch_rename (g : V → W) (hg : Function.Injective g) (f : PeriodicCNF V) (d : PeriodicGridDrawing) :
    d.RoutesMatch (f.rename g).incidenceGraph ↔ d.RoutesMatch f.incidenceGraph := by
  simp only [PeriodicGridDrawing.RoutesMatch,incidence_edges_rename,List.zipIdx_map,List.mem_map,
    forall_exists_index,and_imp]
  constructor
  · intro checked e he
    have h := checked _ e he rfl
    simpa only [Prod.map_fst,Prod.map_snd,id_eq,renameEdge,vertexPosition_rename g hg] using h
  · intro checked _ e he rfl
    simpa only [Prod.map_fst,Prod.map_snd,id_eq,renameEdge,vertexPosition_rename g hg] using checked e he

theorem orbitCompatible_rename (g : V → W) (hg : Function.Injective g) (f : PeriodicCNF V) (d : PeriodicGridDrawing) :
    PeriodicGridDrawing.OrbitCertificate.Compatible (f.rename g).incidenceGraph d ↔
      PeriodicGridDrawing.OrbitCertificate.Compatible f.incidenceGraph d := by
  simp only [PeriodicGridDrawing.OrbitCertificate.Compatible,incidence_vertices_rename g hg,
    incidence_edges_rename,List.length_map,routesMatch_rename g hg]

theorem finiteCompatible_rename (g : V → W) (hg : Function.Injective g) (f : PeriodicCNF V) (d : PeriodicGridDrawing) :
    PeriodicGridDrawing.FiniteCertificate.Compatible (f.rename g).incidenceGraph d ↔
      PeriodicGridDrawing.FiniteCertificate.Compatible f.incidenceGraph d := by
  simp only [PeriodicGridDrawing.FiniteCertificate.Compatible,incidence_vertices_rename g hg,
    incidence_edges_rename,List.length_map,routesMatch_rename g hg]

end LeanTrominoes.PeriodicCNF
