/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GraphAbstractBridge

/-! # Explicit colored graph inputs for the orientation abstract -/
namespace LeanTrominoes.GraphOrientationAbstractBridge
abbrev Cell := ℤ × ℤ
/-- A colored graph lists vertex kinds and edge records
`((source,target,offset),color)`, with colors numbered 0, 1, 2.
`true` marks a trichromatic vertex. The other vertices are monochromatic.
At translate z an edge joins (source,z) to (target,z+offset). -/
abbrev OrientationInput := List Bool × List ((ℕ × ℕ × Cell) × Fin 3)
abbrev OrientationLiteral := ℕ × Cell × Bool

/-- The two ends of an edge read the same direction bit with opposite signs.
The target reads it at the source translate, hence the negated offset.
Loops contribute both ends. The final component records the edge color. -/
def orientationEnds (i : OrientationInput) (v : ℕ) :
    List (ℕ × OrientationLiteral × Fin 3) :=
  (i.2.zipIdx.flatMap fun (e,k) =>
    [(e.1.1,(k,(0,0),false),e.2),
     (e.1.2.1,(k,(-e.1.2.2.1,-e.1.2.2.2),true),e.2)]).filter
    (fun incidence => incidence.1 = v)
def orientationIncoming (i : OrientationInput) (v : ℕ) : List OrientationLiteral :=
  (orientationEnds i v).map (fun incidence => incidence.2.1)
def orientationColors (i : OrientationInput) (v : ℕ) : List (Fin 3) :=
  (orientationEnds i v).map (fun incidence => incidence.2.2)

/-- Every edge endpoint is in range and every vertex has three ends.
Trichromatic vertices have one end of each color; monochromatic vertices
have three ends of a single color. -/
def OrientationWellFormed (i : OrientationInput) : Prop :=
  (∀ e ∈ i.2, e.1.1 < i.1.length ∧ e.1.2.1 < i.1.length) ∧
    ∀ v < i.1.length, (orientationColors i v).length = 3 ∧
      if i.1.getD v false then ∀ color : Fin 3, (orientationColors i v).count color = 1
      else ∃ color : Fin 3, ∀ c ∈ orientationColors i v, c = color

/-- A valid orientation has indegree one at monochromatic vertices and
indegree zero or three at trichromatic vertices. Directions are chosen
independently at every translate. -/
def IsOrientation (i : OrientationInput) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) v, v < i.1.length → if i.1.getD v false then
    (∀ l ∈ orientationIncoming i v, ∀ r ∈ orientationIncoming i v,
      (a l.1 (z.1+l.2.1.1,z.2+l.2.1.2) = l.2.2) ↔
        (a r.1 (z.1+r.2.1.1,z.2+r.2.1.2) = r.2.2))
  else ((orientationIncoming i v).map fun l =>
    a l.1 (z.1+l.2.1.1,z.2+l.2.1.2) == l.2.2).count true = 1
def Orientable (i : OrientationInput) : Prop := ∃ a, IsOrientation i a
def OrientationProblem (i : OrientationInput) : Prop := Orientable i ∧ OrientationWellFormed i
def OrientationLocal (i : OrientationInput) : Prop :=
  OrientationProblem i ∧ ∀ e ∈ i.2, e.1.2.2.1.natAbs+e.1.2.2.2.natAbs ≤ 1
def OrientationLine (i : OrientationInput) : Prop :=
  OrientationLocal i ∧ ∀ e ∈ i.2, e.1.2.2.2 = 0
def OrientationFinite (i : OrientationInput) : Prop :=
  (∃ a : ℕ → Bool, IsOrientation i (fun e _ => a e)) ∧
    OrientationWellFormed i ∧ ∀ e ∈ i.2, e.1.2.2 = (0,0)

/-- The binary encoding lists the vertex and edge counts, vertex-kind bits,
and five fields per edge: endpoints, encoded signed coordinates, and color. -/
def orientationEncoding (i : OrientationInput) : List ComplexityAbstract.Symbol :=
  ComplexityAbstract.binaryFields (i.1.length :: i.2.length ::
    (i.1.map Bool.toNat ++ i.2.flatMap fun e =>
      [e.1.1,e.1.2.1,Encodable.encode e.1.2.2.1,Encodable.encode e.1.2.2.2,e.2.val]))


open _root_.Computability

def colorEquiv : Fin 3 ≃ Gadget.WireColor where
  toFun c := if c.val=0 then .red else if c.val=1 then .green else .blue
  invFun c := match c with | .red => 0 | .green => 1 | .blue => 2
  left_inv c := by fin_cases c <;> rfl
  right_inv c := by cases c <;> rfl

def edgeEquiv : ((ℕ × ℕ × Cell) × Fin 3) ≃ (PeriodicEdge ℕ × Gadget.WireColor) :=
  Equiv.prodCongr PeriodicEdge.equivData.symm colorEquiv

def inputEquiv : OrientationInput ≃ TrichromaticGraphOrientation.Input :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.listEquivOfEquiv edgeEquiv)

@[simp] theorem inputEquiv_fst (i : OrientationInput) : (inputEquiv i).1=i.1 := rfl

theorem inputEquiv_computable : Computable inputEquiv := by
  have edge : Primrec edgeEquiv := Primrec.pair
    (Primrec.of_equiv_symm.comp Primrec.fst)
    ((Primrec.dom_finite colorEquiv).comp Primrec.snd)
  exact (Primrec.pair Primrec.fst
    (Primrec.list_map Primrec.snd (edge.comp Primrec.snd).to₂)).to_comp

theorem inputEquiv_symm_computable : Computable inputEquiv.symm := by
  have edge : Primrec edgeEquiv.symm := Primrec.pair
    (Primrec.of_equiv.comp Primrec.fst)
    ((Primrec.dom_finite colorEquiv.symm).comp Primrec.snd)
  exact (Primrec.pair Primrec.fst
    (Primrec.list_map Primrec.snd (edge.comp Primrec.snd).to₂)).to_comp

@[simp] theorem colorField_eq (c : Fin 3) :
    TrichromaticGraphOrientation.FlatEncoding.colorField (colorEquiv c)=c.val := by
  fin_cases c <;> rfl

theorem encoding_eq (i : OrientationInput) :
    orientationEncoding i=TrichromaticGraphOrientation.FlatEncoding.finEncoding.encode (inputEquiv i) := by
  simp [orientationEncoding,ComplexityAbstract.binaryFields,inputEquiv,edgeEquiv,
    Equiv.listEquivOfEquiv,PeriodicEdge.equivData,
    TrichromaticGraphOrientation.FlatEncoding.finEncoding,
    PeriodicCNFFlatEncoding.finEncodingOfFields,
    TrichromaticGraphOrientation.FlatEncoding.fields,
    TrichromaticGraphOrientation.FlatEncoding.edgeFields,
    List.flatMap_map,PeriodicCNFFlatEncoding.encodeNatFields_eq_trList]


def literalEquiv : OrientationLiteral ≃ PeriodicLiteral ℕ := PeriodicLiteral.equivData.symm

def endMap (e : ℕ × OrientationLiteral × Fin 3) : TrichromaticGraphOrientation.End :=
  (e.1,literalEquiv e.2.1,colorEquiv e.2.2)

theorem ends_eq (i : OrientationInput) (v : ℕ) :
    TrichromaticGraphOrientation.endsAt (inputEquiv i) v = (orientationEnds i v).map endMap := by
  have mapEnds (tagged : ((ℕ × ℕ × Cell) × Fin 3) × ℕ) :
      TrichromaticGraphOrientation.edgeEnds (edgeEquiv tagged.1,tagged.2) =
        [(tagged.1.1.1,(tagged.2,(0,0),false),tagged.1.2),
         (tagged.1.1.2.1,(tagged.2,(-tagged.1.1.2.2.1,-tagged.1.1.2.2.2),true),tagged.1.2)].map endMap := by
    simp [TrichromaticGraphOrientation.edgeEnds,edgeEquiv,PeriodicEdge.equivData,
      endMap,literalEquiv,PeriodicLiteral.equivData,Cell.sub]
  change (((i.2.map edgeEquiv).zipIdx.flatMap TrichromaticGraphOrientation.edgeEnds).filter
    (fun incidence => incidence.1=v)) = _
  rw [List.zipIdx_map,List.flatMap_map]
  change ((i.2.zipIdx.flatMap fun tagged =>
    TrichromaticGraphOrientation.edgeEnds (edgeEquiv tagged.1,tagged.2)).filter
    (fun incidence => incidence.1=v)) = _
  simp only [mapEnds]
  rw [← List.map_flatMap,List.filter_map]
  rfl

theorem incoming_eq (i : OrientationInput) (v : ℕ) :
    TrichromaticGraphOrientation.incoming (inputEquiv i) v =
      (orientationIncoming i v).map literalEquiv := by
  simp [TrichromaticGraphOrientation.incoming,orientationIncoming,ends_eq,List.map_map,endMap]

theorem colors_eq (i : OrientationInput) (v : ℕ) :
    TrichromaticGraphOrientation.colors (inputEquiv i) v =
      (orientationColors i v).map colorEquiv := by
  simp [TrichromaticGraphOrientation.colors,orientationColors,ends_eq,List.map_map,endMap]

theorem wellformed_iff (i : OrientationInput) :
    OrientationWellFormed i ↔ TrichromaticGraphOrientation.IsWellFormed (inputEquiv i) := by
  simp only [OrientationWellFormed,TrichromaticGraphOrientation.IsWellFormed,
    colors_eq,List.length_map,inputEquiv_fst]
  change ((∀ e ∈ i.2, e.1.1 < i.1.length ∧ e.1.2.1 < i.1.length) ∧ _) ↔
    ((∀ e ∈ i.2.map edgeEquiv, e.1.source < i.1.length ∧ e.1.target < i.1.length) ∧ _)
  simp only [List.forall_mem_map]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro v
  apply imp_congr_right
  intro _
  apply and_congr Iff.rfl
  split
  · constructor
    · intro h c
      obtain ⟨a,rfl⟩ := colorEquiv.surjective c
      simpa only [List.count_map_of_injective _ _ colorEquiv.injective] using h a
    · intro h c
      simpa only [List.count_map_of_injective _ _ colorEquiv.injective] using h (colorEquiv c)
  · constructor
    · rintro ⟨c,h⟩
      exact ⟨colorEquiv c,fun a member => congrArg colorEquiv (h a member)⟩
    · rintro ⟨c,h⟩
      obtain ⟨a,rfl⟩ := colorEquiv.surjective c
      exact ⟨a,fun b member => colorEquiv.injective (h b member)⟩

theorem orientation_iff (i : OrientationInput) (a : ℕ → Cell → Bool) :
    IsOrientation i a ↔ GraphAbstractBridge.Data.IsOrientation (inputEquiv i) a := by
  simp only [IsOrientation,GraphAbstractBridge.Data.IsOrientation,incoming_eq,
    inputEquiv_fst,List.forall_mem_map,List.map_map]
  rfl

theorem local_iff (i : OrientationInput) :
    OrientationLocal i ↔ GraphAbstractBridge.Data.OrientationLocal (inputEquiv i) := by
  simp only [OrientationLocal,OrientationProblem,Orientable,
    GraphAbstractBridge.Data.OrientationLocal,GraphAbstractBridge.Data.OrientationProblem,
    GraphAbstractBridge.Data.Orientable,orientation_iff,wellformed_iff]
  change (_ ∧ ∀ e ∈ i.2, _) ↔ (_ ∧ ∀ e ∈ i.2.map edgeEquiv, _)
  simp only [List.forall_mem_map]
  rfl

theorem line_iff (i : OrientationInput) :
    OrientationLine i ↔ GraphAbstractBridge.Data.OrientationLine (inputEquiv i) := by
  simp only [OrientationLine,GraphAbstractBridge.Data.OrientationLine,local_iff]
  change (_ ∧ ∀ e ∈ i.2, _) ↔ (_ ∧ ∀ e ∈ i.2.map edgeEquiv, _)
  simp only [List.forall_mem_map]
  rfl

theorem finite_iff (i : OrientationInput) :
    OrientationFinite i ↔ GraphAbstractBridge.Data.OrientationFinite (inputEquiv i) := by
  simp only [OrientationFinite,GraphAbstractBridge.Data.OrientationFinite,
    orientation_iff,wellformed_iff]
  change (_ ∧ _ ∧ ∀ e ∈ i.2, _) ↔ (_ ∧ _ ∧ ∀ e ∈ i.2.map edgeEquiv, _)
  simp only [List.forall_mem_map]
  rfl

theorem orientation_plane : LeanWang.CoREComplete OrientationLocal :=
  ComplexityAbstractBridge.coRE_recode inputEquiv inputEquiv_computable inputEquiv_symm_computable
    _ _ local_iff GraphAbstractBridge.Data.orientation_plane

theorem orientation_line : ComplexityAbstract.PSPACEComplete orientationEncoding OrientationLine :=
  ComplexityAbstractBridge.pspaceComplete_recode _ _ inputEquiv (Equiv.refl _)
    (fun i => by change (orientationEncoding i).map id=_; rw [List.map_id]; exact encoding_eq i)
    _ _ line_iff GraphAbstractBridge.Data.orientation_line

theorem orientation_finite : ComplexityAbstract.NPComplete orientationEncoding OrientationFinite :=
  ComplexityAbstractBridge.npComplete_recode _ _ inputEquiv (Equiv.refl _)
    (fun i => by change (orientationEncoding i).map id=_; rw [List.map_id]; exact encoding_eq i)
    _ _ finite_iff GraphAbstractBridge.Data.orientation_finite

end LeanTrominoes.GraphOrientationAbstractBridge
