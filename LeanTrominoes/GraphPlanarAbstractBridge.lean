/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GraphConstraintsAbstractBridge
import LeanTrominoes.GraphDrawingAbstractBridge
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricNatCompleteness
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricCompleteness

/-! # Formula incidence drawings and their exact binary encoding -/
namespace LeanTrominoes.GraphPlanarAbstractBridge
open GraphConstraintsAbstractBridge
abbrev Drawing := GraphAbstractBridge.Data.Drawing
abbrev IncidenceVertex := Sum ℕ ℕ

def clauseAnchor (clause : List Literal) : Cell :=
  (clause.head?.map Literal.offset).getD (0,0)

def atoms (f : Formula) : List ℕ := (f.flatMap fun c => c.map Literal.atom).dedup

def incidenceGraph (f : Formula) : GraphAbstractBridge.Data.Graph IncidenceVertex 2 :=
  ((atoms f).map Sum.inl ++ (List.range f.length).map Sum.inr,
    f.zipIdx.flatMap fun tagged => tagged.1.map fun literal =>
      (Sum.inr tagged.2,Sum.inl literal.atom,
        ![literal.offset.1-(clauseAnchor tagged.1).1,
          literal.offset.2-(clauseAnchor tagged.1).2]))

def routesMatch (f : Formula) (d : Drawing) : Prop :=
  ∀ e ∈ (incidenceGraph f).edges.zipIdx,
    (d.edgeRoute e.2).head? = some (d.vertexPosition (incidenceGraph f) e.1.source) ∧
    (d.edgeRoute e.2).getLast? = some
      ((d.vertexPosition (incidenceGraph f) e.1.target).1+(d.gridSize : ℤ)*(e.1.offset 0),
       (d.vertexPosition (incidenceGraph f) e.1.target).2+(d.gridSize : ℤ)*(e.1.offset 1))

def orbitCompatible (f : Formula) (d : Drawing) : Prop :=
  d.vertexPositions.length=(incidenceGraph f).vertices.length ∧
    d.edgeRoutes.length=(incidenceGraph f).edges.length ∧
    (d.vertexPositions.map (fun p => (p.1%(d.gridSize : ℤ),p.2%(d.gridSize : ℤ)))).Nodup ∧
    routesMatch f d

def finiteCompatible (f : Formula) (d : Drawing) : Prop :=
  d.vertexPositions.length=(incidenceGraph f).vertices.length ∧
    d.edgeRoutes.length=(incidenceGraph f).edges.length ∧ d.vertexPositions.Nodup ∧
    (∀ p ∈ d.vertexPositions, 0 < p.1 ∧ p.1 < d.gridSize ∧ 0 < p.2 ∧ p.2 < d.gridSize) ∧
    routesMatch f d

def gridBound (coefficient : ℕ) (f : Formula) (d : Drawing) : Prop :=
  d.gridSize ≤ coefficient*(f.length+f.flatten.length+1)

def vertex : IncidenceVertex ≃ CNFVertex ℕ := CNFVertex.equivData.symm

def edge (e : GraphAbstractBridge.Data.Edge IncidenceVertex 2) : PeriodicEdge (CNFVertex ℕ) :=
  ⟨vertex e.source,vertex e.target,(e.offset 0,e.offset 1)⟩

theorem native_vertices (f : Formula) :
    (formulaEquiv f).incidenceGraph.vertices=(incidenceGraph f).vertices.map vertex := by
  simp [PeriodicCNF.incidenceGraph,PeriodicCNF.incidenceVariableVertices,
    PeriodicCNF.incidenceClauseVertices,PeriodicCNF.variableOccurrences,formulaEquiv_clauses,
    incidenceGraph,atoms,GraphAbstractBridge.Data.Graph.vertices,Formula.clauses,
    List.flatMap_map,List.map_map,Function.comp_def,literalEquiv_atom,vertex,CNFVertex.equivData]

theorem native_anchor (clause : List Literal) :
    PeriodicCNF.clauseAnchor (clause.map literalEquiv)=clauseAnchor clause := by
  cases clause <;> rfl

theorem native_edges (f : Formula) :
    (formulaEquiv f).incidenceGraph.edges=(incidenceGraph f).edges.map edge := by
  simp only [PeriodicCNF.incidenceGraph,formulaEquiv_clauses,List.zipIdx_map,
    List.flatMap_map,incidenceGraph,GraphAbstractBridge.Data.Graph.edges,List.map_flatMap,
    Formula.clauses]
  apply List.flatMap_congr
  intro tagged member
  simp only [PeriodicCNF.clauseIncidenceEdges,Prod.map_fst,Prod.map_snd,id_eq,List.map_map]
  apply List.map_congr_left
  intro literal inside
  simp [PeriodicCNF.incidenceEdge,native_anchor,edge,vertex,CNFVertex.equivData,
    literalEquiv_atom,literalEquiv_offset,GraphAbstractBridge.Data.Edge.source,
    GraphAbstractBridge.Data.Edge.target,GraphAbstractBridge.Data.Edge.offset,Cell.sub]

theorem native_vertexPosition (f : Formula) (d : Drawing) (v : IncidenceVertex) :
    (GraphAbstractBridge.Correspondence.drawing d).vertexPosition
      (formulaEquiv f).incidenceGraph (vertex v)=d.vertexPosition (incidenceGraph f) v := by
  unfold PeriodicGridDrawing.vertexPosition GraphAbstractBridge.Data.Drawing.vertexPosition
  rw [native_vertices,List.idxOf_map_of_injective _ vertex.injective]
  rfl

theorem routesMatch_iff (f : Formula) (d : Drawing) :
    routesMatch f d ↔ (GraphAbstractBridge.Correspondence.drawing d).RoutesMatch (formulaEquiv f).incidenceGraph := by
  simp only [routesMatch,PeriodicGridDrawing.RoutesMatch,native_edges,List.zipIdx_map,
    List.forall_mem_map,Function.comp_def,Prod.map_fst,Prod.map_snd,id_eq,
    edge,native_vertexPosition,PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add]
  rfl

theorem orbitCompatible_iff (f : Formula) (d : Drawing) :
    orbitCompatible f d ↔ PeriodicGridDrawing.OrbitCertificate.Compatible
      (formulaEquiv f).incidenceGraph (GraphAbstractBridge.Correspondence.drawing d) := by
  simp only [orbitCompatible,PeriodicGridDrawing.OrbitCertificate.Compatible,native_vertices,native_edges,
    List.length_map,←routesMatch_iff]
  rfl

theorem finiteCompatible_iff (f : Formula) (d : Drawing) :
    finiteCompatible f d ↔ PeriodicGridDrawing.FiniteCertificate.Compatible
      (formulaEquiv f).incidenceGraph (GraphAbstractBridge.Correspondence.drawing d) := by
  simp only [finiteCompatible,PeriodicGridDrawing.FiniteCertificate.Compatible,native_vertices,native_edges,
    List.length_map,←routesMatch_iff]
  rfl

theorem gridBound_iff (coefficient : ℕ) (f : Formula) (d : Drawing) :
    gridBound coefficient f d ↔ PeriodicPlanarSAT.GridBound coefficient
      (formulaEquiv f,GraphAbstractBridge.Correspondence.drawing d) := by
  simp only [gridBound,PeriodicPlanarSAT.GridBound,PeriodicCNF.presentationSize,PeriodicCNF.presentationLiteralCount,
    formulaEquiv_clauses,Formula.clauses,List.length_map,List.length_flatMap,List.length_flatten,List.map_map,Function.comp_def]
  rfl


abbrev PlanarInput := Formula × Drawing

def inputEquiv : PlanarInput ≃ PeriodicPlanarSAT.Input ℕ :=
  Equiv.prodCongr formulaEquiv GraphDrawingAbstractBridge.drawing

theorem inputEquiv_computable : Computable inputEquiv :=
  (formulaEquiv_computable.comp Computable.fst).pair
    (GraphDrawingAbstractBridge.drawing_equiv_computable.comp Computable.snd)

theorem inputEquiv_symm_computable : Computable inputEquiv.symm :=
  (formulaEquiv_symm_computable.comp Computable.fst).pair
    (GraphDrawingAbstractBridge.drawing_equiv_symm_computable.comp Computable.snd)

def encoding (i : PlanarInput) : List ComplexityAbstract.Symbol :=
  ComplexityAbstract.binaryFields ((GraphDrawingAbstractBridge.Data.drawingFields i.2).length::
    (GraphDrawingAbstractBridge.Data.drawingFields i.2 ++ (i.1.length::i.1.flatMap clauseFields)))

theorem encoding_eq (i : PlanarInput) :
    encoding i = PeriodicPlanarSAT.FlatEncoding.finEncoding.encode (inputEquiv i) := by
  change ComplexityAbstract.binaryFields _ = PeriodicCNFFlatEncoding.encodeNatFields _
  rw [PeriodicCNFFlatEncoding.encodeNatFields_eq_trList]
  change Turing.PartrecToTM2.trList _ = Turing.PartrecToTM2.trList _
  congr 1
  simp only [PeriodicPlanarSAT.FlatEncoding.fields,inputEquiv,Equiv.prodCongr_apply,
    GraphDrawingAbstractBridge.drawingFields_eq,PeriodicCNFFlatEncoding.formulaFields,
    Prod.map_fst,Prod.map_snd,PeriodicPlanarSAT.FlatEncoding.drawingFields,
    formulaEquiv_clauses,List.length_map,List.flatMap_map,clauseFields_eq]

def PlanarSAT (i : PlanarInput) : Prop :=
  Satisfiable i.1 ∧ gridBound 8847360 i.1 i.2 ∧ LocalFormula i.1 ∧
    WidthAtMost 3 i.1 ∧ orbitCompatible i.1 i.2 ∧ GraphDrawingAbstractBridge.Data.DrawingGeometry i.2

def PlanarExactOne (i : PlanarInput) : Prop :=
  ExactlyOneSatisfiable i.1 ∧ gridBound 637009920 i.1 i.2 ∧ LocalFormula i.1 ∧
    WidthAtMost 3 i.1 ∧ finiteCompatible i.1 i.2 ∧ GraphDrawingAbstractBridge.Data.DrawingGeometry i.2

def PlanarLineSAT (i : PlanarInput) : Prop := PlanarSAT i ∧ OneDimensional i.1
def PlanarLineExactOne (i : PlanarInput) : Prop := PlanarExactOne i ∧ OneDimensional i.1

macro "planar_conversion" : tactic => `(tactic| (
  simp only [PlanarSAT,PlanarExactOne,PlanarLineSAT,PlanarLineExactOne,
    satisfiable_iff,exactOne_iff,local_iff,width_iff,occurrences_iff,line_iff,
    gridBound_iff,orbitCompatible_iff,finiteCompatible_iff,GraphDrawingAbstractBridge.geometry_iff,
    inputEquiv,Equiv.prodCongr_apply,PeriodicPlanarSAT.Geometric,
    PeriodicPlanarSAT.StrongGeometry,PeriodicGridDrawing.IsRibbonReady]
  graph_abstract_logic))

theorem ordinary_iff (i : PlanarInput) : PlanarSAT i ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Orbit.BoundedLocalProblem (inputEquiv i) := by
  planar_conversion

theorem ordinaryThree_iff (i : PlanarInput) : (PlanarSAT i ∧ OccurrencesAtMost 3 i.1) ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Orbit.BoundedLocalThreeOccurrenceProblem (inputEquiv i) := by
  planar_conversion

theorem exactOne_iff (i : PlanarInput) : PlanarExactOne i ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem (inputEquiv i) := by
  planar_conversion

theorem exactOneThree_iff (i : PlanarInput) : (PlanarExactOne i ∧ OccurrencesAtMost 3 i.1) ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneThreeOccurrenceProblem (inputEquiv i) := by
  planar_conversion


private theorem coRE_transfer (p : PlanarInput → Prop) (q : PeriodicPlanarSAT.Input ℕ → Prop)
    (correct : ∀ i, p i ↔ q (inputEquiv i)) (complete : LeanWang.CoREComplete q) :
    LeanWang.CoREComplete p :=
  ComplexityAbstractBridge.coRE_recode inputEquiv inputEquiv_computable inputEquiv_symm_computable
    p q correct complete

theorem planar_plane_sat : LeanWang.CoREComplete PlanarSAT :=
  coRE_transfer _ _ ordinary_iff PeriodicPlanarSAT.GeometricNat.ordinary

theorem planar_plane_three_occurrences : LeanWang.CoREComplete
    (fun i => PlanarSAT i ∧ OccurrencesAtMost 3 i.1) :=
  coRE_transfer _ _ ordinaryThree_iff PeriodicPlanarSAT.GeometricNat.ordinaryThree

theorem planar_plane_exact_one : LeanWang.CoREComplete PlanarExactOne :=
  coRE_transfer _ _ exactOne_iff PeriodicPlanarSAT.GeometricNat.exactOne

theorem planar_plane_exact_one_three : LeanWang.CoREComplete
    (fun i => PlanarExactOne i ∧ OccurrencesAtMost 3 i.1) :=
  coRE_transfer _ _ exactOneThree_iff PeriodicPlanarSAT.GeometricNat.exactOneThree


theorem lineOrdinary_iff (i : PlanarInput) : PlanarLineSAT i ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Orbit.LocalOneDimensionalProblem (inputEquiv i) := by
  planar_conversion

theorem lineOrdinaryThree_iff (i : PlanarInput) : (PlanarLineSAT i ∧ OccurrencesAtMost 3 i.1) ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Orbit.LocalOneDimensionalThreeOccurrenceProblem (inputEquiv i) := by
  planar_conversion

theorem lineExactOne_iff (i : PlanarInput) : PlanarLineExactOne i ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem (inputEquiv i) := by
  planar_conversion

theorem lineExactOneThree_iff (i : PlanarInput) : (PlanarLineExactOne i ∧ OccurrencesAtMost 3 i.1) ↔
    PeriodicPlanarSAT.Geometric PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem (inputEquiv i) := by
  planar_conversion


private theorem pspace_transfer (p : PlanarInput → Prop) (q : PeriodicPlanarSAT.Input ℕ → Prop)
    (correct : ∀ i, p i ↔ q (inputEquiv i))
    (complete : Complexity.PSPACEComplete PeriodicPlanarSAT.FlatEncoding.finEncoding q) :
    ComplexityAbstract.PSPACEComplete encoding p :=
  ComplexityAbstractBridge.pspaceComplete_recode encoding PeriodicPlanarSAT.FlatEncoding.finEncoding.encode
    inputEquiv (Equiv.refl _)
    (by intro i; change (encoding i).map id = _; rw [List.map_id]; exact encoding_eq i)
    p q correct ((ComplexityAbstractBridge.pspaceComplete_iff _ _).mpr complete)

theorem planar_line_sat : ComplexityAbstract.PSPACEComplete encoding PlanarLineSAT :=
  pspace_transfer _ _ lineOrdinary_iff PeriodicPlanarSAT.geometricOrdinary_PSPACEComplete

theorem planar_line_three_occurrences : ComplexityAbstract.PSPACEComplete encoding
    (fun i => PlanarLineSAT i ∧ OccurrencesAtMost 3 i.1) :=
  pspace_transfer _ _ lineOrdinaryThree_iff PeriodicPlanarSAT.geometricOrdinaryThree_PSPACEComplete

theorem planar_line_exact_one : ComplexityAbstract.PSPACEComplete encoding PlanarLineExactOne :=
  pspace_transfer _ _ lineExactOne_iff PeriodicPlanarSAT.geometricExactOne_PSPACEComplete

theorem planar_line_exact_one_three : ComplexityAbstract.PSPACEComplete encoding
    (fun i => PlanarLineExactOne i ∧ OccurrencesAtMost 3 i.1) :=
  pspace_transfer _ _ lineExactOneThree_iff PeriodicPlanarSAT.geometricExactOneThree_PSPACEComplete

end LeanTrominoes.GraphPlanarAbstractBridge
