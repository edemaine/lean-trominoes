/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GraphAbstractBridge
import LeanTrominoes.GraphDrawingAbstractBridge

/-! # Public periodic 3DM data and exact complexity transfers -/
namespace LeanTrominoes.GraphThreeDMAbstractBridge
abbrev Cell := ℤ × ℤ
abbrev Reference := ℕ × Cell
abbrev Triple := Reference × Reference × Reference
abbrev Problem := ℕ × ℕ × ℕ × List Triple

def reference (t : Triple) (color : Fin 3) : Reference :=
  if color=0 then t.1 else if color=1 then t.2.1 else t.2.2

def elementCount (p : Problem) (color : Fin 3) : ℕ :=
  if color=0 then p.1 else if color=1 then p.2.1 else p.2.2.1

def triples (p : Problem) : List Triple := p.2.2.2

def incidences (p : Problem) (color : Fin 3) (atom : ℕ) : List (ℕ × Cell) :=
  (List.range (triples p).length).filterMap fun j =>
    let r := reference ((triples p).getD j ((0,(0,0)),(0,(0,0)),(0,(0,0)))) color
    if r.1=atom then some (j,r.2) else none

def Matches (p : Problem) : Prop :=
  ∃ selected : ℕ → Cell → Bool, ∀ color atom, atom<elementCount p color → ∀ z : Cell,
    ((incidences p color atom).map fun i => selected i.1 (z.1-i.2.1,z.2-i.2.2)).count true=1

def WellFormed (p : Problem) : Prop :=
  ∀ t∈triples p, ∀ color, (reference t color).1<elementCount p color

def DegreeTwoOrThree (p : Problem) : Prop :=
  ∀ color atom, atom<elementCount p color → (incidences p color atom).length∈([2,3] : List ℕ)

def Local (p : Problem) : Prop :=
  ∀ t∈triples p, ∀ color, (reference t color).2.1.natAbs+(reference t color).2.2.natAbs≤1

def OneDimensional (p : Problem) : Prop :=
  ∀ t∈triples p, ∀ color, (reference t color).2.2=0

def Line (p : Problem) : Prop := Matches p ∧ WellFormed p ∧ DegreeTwoOrThree p ∧ OneDimensional p ∧ Local p

def referenceFields (r : Reference) : List ℕ := [r.1,Encodable.encode r.2.1,Encodable.encode r.2.2]
def tripleFields (t : Triple) : List ℕ := referenceFields t.1++referenceFields t.2.1++referenceFields t.2.2

def fields (p : Problem) : List ℕ := p.1::p.2.1::p.2.2.1::(triples p).length::(triples p).flatMap tripleFields

def encoding (p : Problem) : List ComplexityAbstract.Symbol := ComplexityAbstract.binaryFields (fields p)


abbrev Vertex := ℕ ⊕ (Fin 3 × ℕ)
def incidenceVertices (p : Problem) : List Vertex :=
  (List.range (triples p).length).map Sum.inl++(List.finRange 3).flatMap fun c =>
    (List.range (elementCount p c)).map fun atom => Sum.inr (c,atom)
def incidenceGraph (p : Problem) : GraphAbstractBridge.Data.Graph Vertex 2 :=
  (incidenceVertices p,(triples p).zipIdx.flatMap fun t => (List.finRange 3).map fun c =>
    (Sum.inl t.2,Sum.inr (c,(reference t.1 c).1),fun i : Fin 2 => if i=0 then (reference t.1 c).2.1 else (reference t.1 c).2.2))
abbrev Input := Problem × GraphAbstractBridge.Data.Drawing

def DrawingCompatible (p : Problem) (d : GraphAbstractBridge.Data.Drawing) : Prop :=
  GraphAbstractBridge.Data.Compatible (incidenceGraph p) d

def Plane (input : Input) : Prop := Matches input.1 ∧ Local input.1 ∧ WellFormed input.1 ∧ DegreeTwoOrThree input.1 ∧
  DrawingCompatible input.1 input.2 ∧ GraphDrawingAbstractBridge.Data.DrawingGeometry input.2 ∧ GraphDrawingAbstractBridge.Data.DrawingHalo input.2

def PlanarLine (input : Input) : Prop := Line input.1 ∧ DrawingCompatible input.1 input.2 ∧
  GraphDrawingAbstractBridge.Data.DrawingGeometry input.2 ∧ GraphDrawingAbstractBridge.Data.DrawingHalo input.2

def planarFields (input : Input) : List ℕ := (GraphDrawingAbstractBridge.Data.drawingFields input.2).length::
  (GraphDrawingAbstractBridge.Data.drawingFields input.2++fields input.1)
def planarEncoding (input : Input) : List ComplexityAbstract.Symbol := ComplexityAbstract.binaryFields (planarFields input)

def referenceEquiv : Reference ≃ PeriodicThreeDMReference := PeriodicThreeDMReference.equivData.symm

def tripleEquiv : Triple ≃ PeriodicThreeDMTriple :=
  (Equiv.prodCongr referenceEquiv (Equiv.prodCongr referenceEquiv referenceEquiv)).trans PeriodicThreeDMTriple.equivData.symm

def problemEquiv : Problem ≃ PeriodicThreeDM :=
  (Equiv.prodCongr (Equiv.refl ℕ) (Equiv.prodCongr (Equiv.refl ℕ)
    (Equiv.prodCongr (Equiv.refl ℕ) (Equiv.listEquivOfEquiv tripleEquiv)))).trans PeriodicThreeDM.equivData.symm

def colorEquiv : Fin 3 ≃ Gadget.WireColor where
  toFun c := if c=0 then .red else if c=1 then .green else .blue
  invFun c := match c with | .red => 0 | .green => 1 | .blue => 2
  left_inv c := by fin_cases c <;> decide
  right_inv c := by cases c <;> decide

@[simp] theorem reference_eq (t : Triple) (c : Fin 3) :
    ((tripleEquiv t).reference (colorEquiv c)).atom=(reference t c).1 ∧
    ((tripleEquiv t).reference (colorEquiv c)).offset=(reference t c).2 := by
  fin_cases c <;> simp [tripleEquiv,referenceEquiv,reference,colorEquiv,PeriodicThreeDMTriple.equivData,PeriodicThreeDMReference.equivData,PeriodicThreeDMTriple.reference]
@[simp] theorem count_eq (p : Problem) (c : Fin 3) : (problemEquiv p).elementCount (colorEquiv c)=elementCount p c := by
  fin_cases c <;> simp [problemEquiv,PeriodicThreeDM.equivData,PeriodicThreeDM.elementCount,elementCount,colorEquiv]
@[simp] theorem triples_eq (p : Problem) : (problemEquiv p).triples=(triples p).map tripleEquiv := rfl

private theorem triple_get (p : Problem) (j : ℕ) :
    ((problemEquiv p).triples.getD j default)=tripleEquiv ((triples p).getD j ((0,(0,0)),(0,(0,0)),(0,(0,0)))) := by
  rw [triples_eq,show (default : PeriodicThreeDMTriple)=tripleEquiv ((0,(0,0)),(0,(0,0)),(0,(0,0))) by rfl]
  simp only [List.getD_map]

theorem incidences_eq (p : Problem) (c : Fin 3) (atom : ℕ) :
    (problemEquiv p).incidences (colorEquiv c) atom=
      (incidences p c atom).map (fun i => (⟨i.1,i.2⟩ : PeriodicThreeDM.Incidence)) := by
  simp only [PeriodicThreeDM.incidences,triples_eq,List.length_map,incidences,List.map_filterMap]
  apply List.filterMap_congr
  intro j hj
  have get := triple_get p j
  simp only [triples_eq] at get
  rw [get]
  simp only [(reference_eq _ c).1,(reference_eq _ c).2,Function.comp_def,Option.map_ite,Option.map_some,Option.map_none]

 theorem matches_iff (p : Problem) : Matches p ↔ (problemEquiv p).Satisfiable := by
  simp only [Matches,PeriodicThreeDM.Satisfiable,PeriodicThreeDM.Satisfies,PeriodicThreeDM.CoversElements,
    PeriodicThreeDM.incidentValues,PeriodicThreeDM.liftAssignment,PeriodicOneInThree.ExactlyOne,Cell.sub]
  apply exists_congr
  intro selected
  constructor
  · intro satisfied c atom bound z
    obtain ⟨color,rfl⟩ := colorEquiv.surjective c
    simpa only [count_eq,incidences_eq,List.map_map,Function.comp_def] using satisfied color atom (by simpa using bound) z
  · intro satisfied color atom bound z
    simpa only [incidences_eq,List.map_map,Function.comp_def] using satisfied (colorEquiv color) atom (by simpa using bound) z

 theorem wellFormed_iff (p : Problem) : WellFormed p ↔ (problemEquiv p).IsWellFormed := by
  simp only [WellFormed,PeriodicThreeDM.IsWellFormed,triples_eq,List.forall_mem_map]
  constructor
  · intro h t ht c
    obtain ⟨color,rfl⟩ := colorEquiv.surjective c
    simpa only [(reference_eq t color).1,count_eq] using h t ht color
  · intro h t ht c
    simpa only [(reference_eq t c).1,count_eq] using h t ht (colorEquiv c)

 theorem degree_iff (p : Problem) : DegreeTwoOrThree p ↔ (problemEquiv p).DegreeTwoOrThree := by
  simp only [DegreeTwoOrThree,PeriodicThreeDM.DegreeTwoOrThree,PeriodicThreeDM.degree]
  constructor
  · intro h c atom bound
    obtain ⟨color,rfl⟩ := colorEquiv.surjective c
    simpa only [incidences_eq,List.length_map] using h color atom (by simpa using bound)
  · intro h c atom bound
    simpa only [incidences_eq,List.length_map] using h (colorEquiv c) atom (by simpa using bound)

 theorem local_iff (p : Problem) : Local p ↔ (problemEquiv p).IsLocal := by
  simp only [Local,PeriodicThreeDM.IsLocal,triples_eq,List.forall_mem_map]
  constructor
  · intro h t ht c
    obtain ⟨color,rfl⟩ := colorEquiv.surjective c
    simpa only [(reference_eq t color).2] using h t ht color
  · intro h t ht c
    simpa only [(reference_eq t c).2] using h t ht (colorEquiv c)

 theorem oneDimensional_iff (p : Problem) : OneDimensional p ↔ (problemEquiv p).IsOneDimensional := by
  simp only [OneDimensional,PeriodicThreeDM.IsOneDimensional,triples_eq,List.forall_mem_map]
  constructor
  · intro h t ht c
    obtain ⟨color,rfl⟩ := colorEquiv.surjective c
    simpa only [(reference_eq t color).2] using h t ht color
  · intro h t ht c
    simpa only [(reference_eq t c).2] using h t ht (colorEquiv c)

 theorem line_iff (p : Problem) : Line p ↔ GraphAbstractBridge.Data.ThreeDMLine (problemEquiv p) := by
  rw [Line,matches_iff,wellFormed_iff,degree_iff,oneDimensional_iff,local_iff]
  rfl

 theorem fields_eq (p : Problem) : fields p=PeriodicThreeDM.FlatEncoding.fields (problemEquiv p) := by
  unfold fields PeriodicThreeDM.FlatEncoding.fields
  rw [triples_eq,List.length_map,List.flatMap_map]
  change p.1::p.2.1::p.2.2.1::_=p.1::p.2.1::p.2.2.1::_
  congr 4

 theorem encoding_eq (p : Problem) : encoding p=PeriodicThreeDM.FlatEncoding.finEncoding.encode (problemEquiv p) := by
  change ComplexityAbstract.binaryFields (fields p)=PeriodicCNFFlatEncoding.encodeNatFields _
  rw [PeriodicCNFFlatEncoding.encodeNatFields_eq_trList,fields_eq]
  rfl

 theorem three_dm_line : ComplexityAbstract.PSPACEComplete encoding Line :=
  ComplexityAbstractBridge.pspaceComplete_recode encoding PeriodicThreeDM.FlatEncoding.finEncoding.encode problemEquiv (Equiv.refl _)
    (fun p => by change (encoding p).map id=_; rw [List.map_id]; exact encoding_eq p) _ _ line_iff GraphAbstractBridge.Data.three_dm_line


theorem referenceEquiv_primrec : Primrec referenceEquiv := PeriodicThreeDMReference.equivData_symm_primrec
 theorem referenceEquiv_symm_primrec : Primrec referenceEquiv.symm := PeriodicThreeDMReference.equivData_primrec
 theorem tripleEquiv_primrec : Primrec tripleEquiv := by
  exact PeriodicThreeDMTriple.equivData_symm_primrec.comp
    ((referenceEquiv_primrec.comp Primrec.fst).pair
      ((referenceEquiv_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
        (referenceEquiv_primrec.comp (Primrec.snd.comp Primrec.snd))))
 theorem tripleEquiv_symm_primrec : Primrec tripleEquiv.symm := by
  exact ((referenceEquiv_symm_primrec.comp Primrec.fst).pair
      ((referenceEquiv_symm_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
        (referenceEquiv_symm_primrec.comp (Primrec.snd.comp Primrec.snd)))).comp PeriodicThreeDMTriple.equivData_primrec
 theorem problemEquiv_primrec : Primrec problemEquiv := by
  have listMap := Primrec.list_map Primrec.id (tripleEquiv_primrec.comp Primrec.snd).to₂
  exact PeriodicThreeDM.equivData_symm_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        (listMap.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
 theorem problemEquiv_symm_primrec : Primrec problemEquiv.symm := by
  have listMap := Primrec.list_map Primrec.id (tripleEquiv_symm_primrec.comp Primrec.snd).to₂
  exact (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        (listMap.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))).comp PeriodicThreeDM.equivData_primrec

def inputEquiv : Input ≃ PeriodicThreeDM.NormalizationCompiler.Input :=
  (Equiv.prodCongr problemEquiv GraphAbstractBridge.Correspondence.drawing).trans
    PeriodicThreeDM.NormalizationCompiler.Input.equivData.symm
 theorem inputEquiv_computable : Computable inputEquiv :=
  (PeriodicThreeDM.NormalizationCompiler.Input.equivData_symm_primrec.comp
    ((problemEquiv_primrec.comp Primrec.fst).pair
      (PeriodicGridDrawing.equivData_symm_primrec.comp Primrec.snd))).to_comp
 theorem inputEquiv_symm_computable : Computable inputEquiv.symm :=
  (((problemEquiv_symm_primrec.comp Primrec.fst).pair
      (PeriodicGridDrawing.equivData_primrec.comp Primrec.snd)).comp
    PeriodicThreeDM.NormalizationCompiler.Input.equivData_primrec).to_comp


def vertexEquiv : Vertex ≃ PeriodicThreeDMVertex where
  toFun v := match v with | .inl j => .triple j | .inr (c,a) => .element (colorEquiv c) a
  invFun v := match v with | .triple j => .inl j | .element c a => .inr (colorEquiv.symm c,a)
  left_inv v := by cases v with | inl j => rfl | inr pair => simp
  right_inv v := by cases v <;> simp

@[simp] theorem redCount_eq (p : Problem) : (problemEquiv p).redCount=p.1 := rfl
@[simp] theorem greenCount_eq (p : Problem) : (problemEquiv p).greenCount=p.2.1 := rfl
@[simp] theorem blueCount_eq (p : Problem) : (problemEquiv p).blueCount=p.2.2.1 := rfl

theorem graph_eq (p : Problem) : (problemEquiv p).incidenceGraph=
    GraphDrawingAbstractBridge.relabel vertexEquiv (GraphAbstractBridge.Correspondence.graph Vertex (incidenceGraph p)) := by
  have colors : List.finRange 3=[0,1,2] := by decide
  apply (PeriodicGraph.equivData (Vertex:=PeriodicThreeDMVertex)).injective
  apply Prod.ext
  · simp [PeriodicGraph.equivData,PeriodicThreeDM.incidenceGraph,PeriodicThreeDM.tripleVertices,PeriodicThreeDM.elementVertices,
      PeriodicThreeDM.coloredElementVertices,PeriodicThreeDM.elementCount,triples_eq,
      GraphDrawingAbstractBridge.relabel,GraphAbstractBridge.Correspondence.graph_vertices,
      incidenceGraph,incidenceVertices,colors,List.map_append,List.map_flatMap,List.map_map,
      Function.comp_def,vertexEquiv,colorEquiv,elementCount]
  · simp [PeriodicGraph.equivData,PeriodicThreeDM.incidenceGraph,PeriodicThreeDM.tripleIncidenceEdges,
      PeriodicThreeDM.incidenceColors,PeriodicThreeDM.incidenceEdge,triples_eq,
      GraphDrawingAbstractBridge.relabel,GraphAbstractBridge.Correspondence.graph_edges,
      GraphAbstractBridge.Correspondence.edge,incidenceGraph,colors,List.zipIdx_map,
      List.map_flatMap,List.map_map,Function.comp_def,vertexEquiv,colorEquiv,reference,
      tripleEquiv,referenceEquiv,PeriodicThreeDMTriple.equivData,PeriodicThreeDMReference.equivData,
      PeriodicThreeDMTriple.reference,Prod.map,id_eq]
    rw [List.flatMap_map]
    rfl

theorem drawingCompatible_iff (p : Problem) (d : GraphAbstractBridge.Data.Drawing) :
    DrawingCompatible p d ↔ (GraphAbstractBridge.Correspondence.drawing d).IsCompatible (problemEquiv p).incidenceGraph := by
  rw [graph_eq,GraphDrawingAbstractBridge.compatible_relabel]
  exact (GraphAbstractBridge.Correspondence.compatible (incidenceGraph p) d).symm

theorem drawingCertificate_iff (p : Problem) (d : GraphAbstractBridge.Data.Drawing) (wf : WellFormed p) :
    (DrawingCompatible p d ∧ GraphDrawingAbstractBridge.Data.DrawingGeometry d ∧ GraphDrawingAbstractBridge.Data.DrawingHalo d) ↔
      PeriodicThreeDM.FiniteDrawingCertificate.verifies (problemEquiv p) (GraphAbstractBridge.Correspondence.drawing d)=true := by
  rw [drawingCompatible_iff,GraphDrawingAbstractBridge.geometry_iff,GraphDrawingAbstractBridge.halo_iff]
  constructor
  · rintro ⟨compatible,⟨orthogonal,continuous,contacts⟩,halo⟩
    exact PeriodicThreeDM.FiniteDrawingCertificate.verifies_complete compatible orthogonal halo continuous contacts
  · intro checked
    have raw := checked
    simp only [PeriodicThreeDM.FiniteDrawingCertificate.verifies,Bool.and_eq_true] at raw
    have compatible := PeriodicThreeDM.FiniteDrawingCertificate.compatibleCheck_spec ((wellFormed_iff p).mp wf) raw.1
    have orthogonal := PeriodicThreeDM.FiniteDrawingCertificate.orthogonalCheck_spec raw.2.1
    have halo := PeriodicThreeDM.FiniteDrawingCertificate.endpointBoundsCheck_spec raw.2.2.1
    have continuous := PeriodicGridDrawing.isContinuouslyPlanar_of_expandedFinite halo compatible.2.2.2.2.1
      raw.2.2.2.1 raw.2.2.2.2.1 raw.2.2.2.2.2.1
    have lengths : ∀ route∈(GraphAbstractBridge.Correspondence.drawing d).edgeRoutes, 2≤route.length := by
      intro route member
      exact PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless _ _ compatible
        (problemEquiv p).incidenceGraph_edgesAreLoopless member
    have bounds := PeriodicGridDrawing.routePointsInExpandedSquare_of_segmentEndpoints halo lengths
    have contacts := PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_expandedFinite bounds raw.2.2.2.2.2.2
    exact ⟨compatible,⟨orthogonal,continuous,contacts⟩,halo⟩

theorem plane_iff (input : Input) : Plane input ↔ GraphAbstractBridge.Data.ThreeDMPlane (inputEquiv input) := by
  constructor
  · rintro ⟨hmatches,hloc,wf,degree,geometry⟩
    exact ⟨(matches_iff _).mp hmatches,(local_iff _).mp hloc,(wellFormed_iff _).mp wf,(degree_iff _).mp degree,
      (drawingCertificate_iff _ _ wf).mp geometry⟩
  · rintro ⟨hmatches,hloc,wf,degree,certificate⟩
    have publicWF := (wellFormed_iff _).mpr wf
    exact ⟨(matches_iff _).mpr hmatches,(local_iff _).mpr hloc,publicWF,(degree_iff _).mpr degree,
      (drawingCertificate_iff _ _ publicWF).mpr certificate⟩

theorem planarLine_iff (input : Input) : PlanarLine input ↔
    GraphAbstractBridge.Data.ThreeDMLine (inputEquiv input).problem ∧
      PeriodicThreeDM.FiniteDrawingCertificate.verifies (inputEquiv input).problem (inputEquiv input).drawing=true := by
  constructor
  · rintro ⟨line,geometry⟩
    exact ⟨(line_iff _).mp line,(drawingCertificate_iff _ _ line.2.1).mp geometry⟩
  · rintro ⟨line,certificate⟩
    have publicLine := (line_iff _).mpr line
    exact ⟨publicLine,(drawingCertificate_iff _ _ publicLine.2.1).mpr certificate⟩

theorem planarEncoding_eq (input : Input) : planarEncoding input=PeriodicThreeDM.FlatEncoding.Planar.finEncoding.encode (inputEquiv input) := by
  change ComplexityAbstract.binaryFields (planarFields input)=PeriodicCNFFlatEncoding.encodeNatFields _
  rw [PeriodicCNFFlatEncoding.encodeNatFields_eq_trList]
  change Turing.PartrecToTM2.trList _=Turing.PartrecToTM2.trList _
  congr 1
  simp only [planarFields,PeriodicThreeDM.FlatEncoding.Planar.fields]
  rw [GraphDrawingAbstractBridge.drawingFields_eq,fields_eq]
  rfl

theorem three_dm_plane : LeanWang.CoREComplete Plane :=
  ComplexityAbstractBridge.coRE_recode inputEquiv inputEquiv_computable inputEquiv_symm_computable
    Plane GraphAbstractBridge.Data.ThreeDMPlane plane_iff GraphAbstractBridge.Data.three_dm_plane

theorem three_dm_planar_line : ComplexityAbstract.PSPACEComplete planarEncoding PlanarLine :=
  ComplexityAbstractBridge.pspaceComplete_recode planarEncoding PeriodicThreeDM.FlatEncoding.Planar.finEncoding.encode inputEquiv (Equiv.refl _)
    (fun input => by change (planarEncoding input).map id=_; rw [List.map_id]; exact planarEncoding_eq input)
    _ _ planarLine_iff GraphAbstractBridge.Data.three_dm_planar_line

end LeanTrominoes.GraphThreeDMAbstractBridge