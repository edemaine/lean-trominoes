import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.PeriodicThreeSATThreeComputability

/-!
# Computability of the normalized periodic 3DM drawing compiler

This file proves primitive recursiveness of the data-only compiler.  The
proof follows the executable pipeline: enumerate incidences, contract
degree-two elements, normalize the retained routes, and rasterize the final
finite torus.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open PeriodicOrthocrossing
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-! ## Primitive-recursive 3DM enumeration -/

/-- Small explicit code used to branch on the three wire colors without
expanding equality on their generic finite encoding. -/
def wireColorCode : WireColor → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

theorem wireColorCode_primrec : Primrec wireColorCode :=
  Primrec.dom_finite wireColorCode

theorem triple_reference_primrec :
    Primrec₂ PeriodicThreeDMTriple.reference := by
  change Primrec fun input : PeriodicThreeDMTriple × WireColor =>
    input.1.reference input.2
  let is (code : Nat) : PrimrecPred (fun input :
      PeriodicThreeDMTriple × WireColor =>
        wireColorCode input.2 = code) :=
    Primrec.eq.comp
      (wireColorCode_primrec.comp Primrec.snd) (Primrec.const code)
  exact (Primrec.ite (is 0)
    (PeriodicThreeDMTriple.red_primrec.comp Primrec.fst)
    (Primrec.ite (is 1)
      (PeriodicThreeDMTriple.green_primrec.comp Primrec.fst)
      (PeriodicThreeDMTriple.blue_primrec.comp Primrec.fst))).of_eq
        fun input => by cases input.2 <;> rfl

theorem elementCount_primrec :
    Primrec₂ PeriodicThreeDM.elementCount := by
  change Primrec fun input : PeriodicThreeDM × WireColor =>
    input.1.elementCount input.2
  let is (code : Nat) : PrimrecPred (fun input :
      PeriodicThreeDM × WireColor => wireColorCode input.2 = code) :=
    Primrec.eq.comp
      (wireColorCode_primrec.comp Primrec.snd) (Primrec.const code)
  exact (Primrec.ite (is 0)
    (PeriodicThreeDM.redCount_primrec.comp Primrec.fst)
    (Primrec.ite (is 1)
      (PeriodicThreeDM.greenCount_primrec.comp Primrec.fst)
      (PeriodicThreeDM.blueCount_primrec.comp Primrec.fst))).of_eq
        fun input => by cases input.2 <;> rfl

theorem incidence_mk_primrec :
    Primrec₂ fun (index : Nat) (offset : Cell) =>
      (Incidence.mk index offset) := by
  exact (Incidence.equivData_symm_primrec.comp
    (Primrec.pair Primrec.fst Primrec.snd)).to₂

theorem incidenceTag_mk_primrec :
    Primrec₂ fun (index : Nat) (color : WireColor) =>
      (IncidenceTag.mk index color) := by
  exact (IncidenceTag.equivData_symm_primrec.comp
    (Primrec.pair Primrec.fst Primrec.snd)).to₂

theorem incidences_primrec :
    Primrec fun input : (PeriodicThreeDM × WireColor) × Nat =>
      input.1.1.incidences input.1.2 input.2 := by
  let indices : Primrec (fun input :
      (PeriodicThreeDM × WireColor) × Nat =>
        List.range input.1.1.triples.length) :=
    Primrec.list_range.comp
      (Primrec.list_length.comp
        (PeriodicThreeDM.triples_primrec.comp
          (Primrec.fst.comp Primrec.fst)))
  have select : Primrec₂ fun
      (input : (PeriodicThreeDM × WireColor) × Nat)
      (tripleIndex : Nat) =>
      let reference :=
        (input.1.1.triples.getD tripleIndex default).reference input.1.2
      if reference.atom = input.2 then
        some (Incidence.mk tripleIndex reference.offset)
      else none := by
    change Primrec fun combined :
        ((PeriodicThreeDM × WireColor) × Nat) × Nat =>
      let reference :=
        (combined.1.1.1.triples.getD combined.2 default).reference
          combined.1.1.2
      if reference.atom = combined.1.2 then
        some (Incidence.mk combined.2 reference.offset)
      else none
    let triple : Primrec (fun combined :
        ((PeriodicThreeDM × WireColor) × Nat) × Nat =>
        combined.1.1.1.triples.getD combined.2 default) :=
      (Primrec.list_getD default).comp
        (PeriodicThreeDM.triples_primrec.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd
    let reference : Primrec (fun combined :
        ((PeriodicThreeDM × WireColor) × Nat) × Nat =>
        (combined.1.1.1.triples.getD combined.2 default).reference
          combined.1.1.2) :=
      triple_reference_primrec.comp triple
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    let same : PrimrecPred (fun combined :
        ((PeriodicThreeDM × WireColor) × Nat) × Nat =>
        ((combined.1.1.1.triples.getD combined.2 default).reference
          combined.1.1.2).atom = combined.1.2) :=
      Primrec.eq.comp
        (PeriodicThreeDMReference.atom_primrec.comp reference)
        (Primrec.snd.comp Primrec.fst)
    let selected : Primrec (fun combined :
        ((PeriodicThreeDM × WireColor) × Nat) × Nat =>
        some (Incidence.mk combined.2
          ((combined.1.1.1.triples.getD combined.2 default).reference
            combined.1.1.2).offset)) :=
      Primrec.option_some.comp
        (incidence_mk_primrec.comp
          Primrec.snd
          (PeriodicThreeDMReference.offset_primrec.comp reference))
    exact Primrec.ite same selected (Primrec.const none)
  exact (Primrec.listFilterMap indices select).of_eq fun _ => rfl

theorem degree_primrec :
    Primrec fun input : (PeriodicThreeDM × WireColor) × Nat =>
      input.1.1.degree input.1.2 input.2 :=
  Primrec.list_length.comp incidences_primrec

theorem periodicThreeDMVertex_triple_primrec :
    Primrec PeriodicThreeDMVertex.triple := by
  exact PeriodicThreeDMVertex.equivData_symm_primrec.comp
    Primrec.sumInl

theorem periodicThreeDMVertex_element_primrec :
    Primrec₂ PeriodicThreeDMVertex.element := by
  exact (PeriodicThreeDMVertex.equivData_symm_primrec.comp
    (Primrec.sumInr.comp
      (Primrec.pair Primrec.fst Primrec.snd))).to₂

theorem contractedEdge_through_primrec :
    Primrec fun input :
        (WireColor × Nat) × (Incidence × Incidence) =>
      ContractedEdge.through input.1.1 input.1.2
        input.2.1 input.2.2 := by
  exact ContractedEdge.equivData_symm_primrec.comp
    (Primrec.sumInr.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          Primrec.snd)))

theorem contractedEdge_retained_primrec :
    Primrec fun input : (WireColor × Nat) × Incidence =>
      ContractedEdge.retained input.1.1 input.1.2 input.2 := by
  exact ContractedEdge.equivData_symm_primrec.comp
    (Primrec.sumInl.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          Primrec.snd)))

/-- The two relevant exact incidence-list shapes, factored from contraction. -/
def defaultIncidence : Incidence := ⟨0, (0, 0)⟩

def contractedEdgesOfIncidences (color : WireColor) (atom : Nat) :
    List Incidence → List ContractedEdge
  | [first, second] => [.through color atom first second]
  | [first, second, third] =>
      [.retained color atom first, .retained color atom second,
        .retained color atom third]
  | _ => []

theorem contractedEdgesOfIncidences_primrec :
    Primrec fun input : (WireColor × Nat) × List Incidence =>
      contractedEdgesOfIncidences input.1.1 input.1.2 input.2 := by
  let length : Primrec (fun input :
      (WireColor × Nat) × List Incidence => input.2.length) :=
    Primrec.list_length.comp Primrec.snd
  let itemAt (index : Nat) : Primrec (fun input :
      (WireColor × Nat) × List Incidence =>
        input.2.getD index defaultIncidence) :=
    (Primrec.list_getD defaultIncidence).comp Primrec.snd
      (Primrec.const index)
  let retained (index : Nat) : Primrec (fun input :
      (WireColor × Nat) × List Incidence =>
        ContractedEdge.retained input.1.1 input.1.2
          (input.2.getD index defaultIncidence)) :=
    contractedEdge_retained_primrec.comp
      (Primrec.pair Primrec.fst (itemAt index))
  let through : Primrec (fun input :
      (WireColor × Nat) × List Incidence =>
        ContractedEdge.through input.1.1 input.1.2
          (input.2.getD 0 defaultIncidence)
          (input.2.getD 1 defaultIncidence)) :=
    contractedEdge_through_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.pair (itemAt 0) (itemAt 1)))
  have pairOutput : Primrec (fun input :
      (WireColor × Nat) × List Incidence =>
        [ContractedEdge.through input.1.1 input.1.2
          (input.2.getD 0 defaultIncidence)
          (input.2.getD 1 defaultIncidence)]) :=
    Primrec.list_cons.comp through (Primrec.const [])
  have tripleOutput : Primrec (fun input :
      (WireColor × Nat) × List Incidence =>
        [ContractedEdge.retained input.1.1 input.1.2
            (input.2.getD 0 defaultIncidence),
          ContractedEdge.retained input.1.1 input.1.2
            (input.2.getD 1 defaultIncidence),
          ContractedEdge.retained input.1.1 input.1.2
            (input.2.getD 2 defaultIncidence)]) :=
    Primrec.list_cons.comp (retained 0)
      (Primrec.list_cons.comp (retained 1)
        (Primrec.list_cons.comp (retained 2) (Primrec.const [])))
  refine (Primrec.ite (Primrec.eq.comp length (Primrec.const 2))
    pairOutput
    (Primrec.ite (Primrec.eq.comp length (Primrec.const 3))
      tripleOutput (Primrec.const []))).of_eq ?_
  intro input
  rcases input with ⟨⟨color, atom⟩, incidences⟩
  rcases incidences with _ | ⟨first, incidences⟩
  · rfl
  rcases incidences with _ | ⟨second, incidences⟩
  · rfl
  rcases incidences with _ | ⟨third, incidences⟩
  · rfl
  rcases incidences with _ | ⟨fourth, incidences⟩
  · rfl
  rcases incidences with _ | ⟨fifth, incidences⟩ <;> rfl

theorem contractedEdgesForElement_primrec :
    Primrec fun input : (PeriodicThreeDM × WireColor) × Nat =>
      input.1.1.contractedEdgesForElement input.1.2 input.2 := by
  exact (contractedEdgesOfIncidences_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst)
        Primrec.snd)
      incidences_primrec)).of_eq fun input => by
        simp only [contractedEdgesForElement]
        generalize input.1.1.incidences input.1.2 input.2 = incidences
        rcases incidences with _ | ⟨first, incidences⟩
        · rfl
        rcases incidences with _ | ⟨second, incidences⟩
        · rfl
        rcases incidences with _ | ⟨third, incidences⟩
        · rfl
        rcases incidences with _ | ⟨fourth, incidences⟩ <;> rfl

theorem contractedEdgesForColor_primrec :
    Primrec fun input : PeriodicThreeDM × WireColor =>
      input.1.contractedEdgesForColor input.2 := by
  have atoms : Primrec (fun input : PeriodicThreeDM × WireColor =>
      List.range (input.1.elementCount input.2)) :=
    Primrec.list_range.comp elementCount_primrec
  exact Primrec.list_flatMap atoms
    (contractedEdgesForElement_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)).to₂

theorem contractedEdges_primrec :
    Primrec PeriodicThreeDM.contractedEdges := by
  exact Primrec.list_flatMap (Primrec.const incidenceColors)
    (contractedEdgesForColor_primrec.comp
      (Primrec.pair (Primrec.fst) Primrec.snd)).to₂

theorem contractedElementVerticesForColor_primrec :
    Primrec fun input : PeriodicThreeDM × WireColor =>
      input.1.contractedElementVerticesForColor input.2 := by
  have atoms : Primrec (fun input : PeriodicThreeDM × WireColor =>
      List.range (input.1.elementCount input.2)) :=
    Primrec.list_range.comp elementCount_primrec
  have degreeThree : PrimrecPred (fun combined :
      (PeriodicThreeDM × WireColor) × Nat =>
      combined.1.1.degree combined.1.2 combined.2 = 3) :=
    Primrec.eq.comp degree_primrec (Primrec.const 3)
  have selected : Primrec₂ fun
      (input : PeriodicThreeDM × WireColor) (atom : Nat) =>
      if input.1.degree input.2 atom = 3 then
        some (.element input.2 atom : PeriodicThreeDMVertex)
      else none :=
    Primrec.ite degreeThree
      (Primrec.option_some.comp
        (periodicThreeDMVertex_element_primrec.comp
          (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (Primrec.const none)
  refine (Primrec.listFilterMap atoms selected).of_eq ?_
  intro input
  unfold contractedElementVerticesForColor
  generalize List.range (input.1.elementCount input.2) = values
  induction values with
  | nil => rfl
  | cons atom rest induction =>
      by_cases degree : input.1.degree input.2 atom = 3 <;>
        simp [degree, induction]

theorem contractedElementVertices_primrec :
    Primrec PeriodicThreeDM.contractedElementVertices := by
  exact Primrec.list_flatMap (Primrec.const incidenceColors)
    (contractedElementVerticesForColor_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)).to₂

theorem tripleVertices_primrec :
    Primrec PeriodicThreeDM.tripleVertices := by
  have indices : Primrec (fun problem : PeriodicThreeDM =>
      List.range problem.triples.length) :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicThreeDM.triples_primrec)
  exact Primrec.list_map indices
    (periodicThreeDMVertex_triple_primrec.comp Primrec.snd).to₂

theorem contractedGraphVertices_primrec :
    Primrec fun problem : PeriodicThreeDM =>
      problem.contractedGraph.vertices := by
  exact (Primrec.list_append.comp tripleVertices_primrec
    contractedElementVertices_primrec).of_eq fun _ => rfl

theorem coloredElementVertices_primrec :
    Primrec fun input : PeriodicThreeDM × WireColor =>
      input.1.coloredElementVertices input.2 := by
  have atoms : Primrec (fun input : PeriodicThreeDM × WireColor =>
      List.range (input.1.elementCount input.2)) :=
    Primrec.list_range.comp elementCount_primrec
  exact Primrec.list_map atoms
    (periodicThreeDMVertex_element_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

theorem elementVertices_primrec :
    Primrec PeriodicThreeDM.elementVertices := by
  have red := coloredElementVertices_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const WireColor.red))
  have green := coloredElementVertices_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const WireColor.green))
  have blue := coloredElementVertices_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const WireColor.blue))
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp red green) blue).of_eq fun _ => rfl

theorem incidenceGraphVertices_primrec :
    Primrec fun problem : PeriodicThreeDM =>
      problem.incidenceGraph.vertices := by
  exact (Primrec.list_append.comp tripleVertices_primrec
    elementVertices_primrec).of_eq fun _ => rfl

theorem tripleIncidenceTags_primrec :
    Primrec PeriodicThreeDM.tripleIncidenceTags := by
  exact Primrec.list_map (Primrec.const incidenceColors)
    (incidenceTag_mk_primrec.comp Primrec.fst Primrec.snd).to₂

theorem incidenceTags_primrec :
    Primrec PeriodicThreeDM.incidenceTags := by
  have indices : Primrec (fun problem : PeriodicThreeDM =>
      List.range problem.triples.length) :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicThreeDM.triples_primrec)
  exact (Primrec.list_flatMap indices
    (tripleIncidenceTags_primrec.comp Primrec.snd).to₂).of_eq
      fun problem => (incidenceTags_eq_range_flatMap problem).symm

theorem incidenceRouteIndex_primrec :
    Primrec₂ PeriodicThreeDM.incidenceRouteIndex := by
  exact Primrec.list_idxOf.comp
    Primrec.snd (incidenceTags_primrec.comp Primrec.fst)

/-! ## Contracted drawing lookup -/

theorem edgeRoute_primrec :
    Primrec₂ PeriodicGridDrawing.edgeRoute := by
  exact (Primrec.list_getD []).comp
    (PeriodicGridDrawing.edgeRoutes_primrec.comp Primrec.fst)
    Primrec.snd

theorem vertexPosition_primrec :
    Primrec fun input :
        (List PeriodicThreeDMVertex × PeriodicGridDrawing) ×
          PeriodicThreeDMVertex =>
      input.1.2.vertexPositions.getD
        (input.1.1.idxOf input.2) (0, 0) := by
  exact (Primrec.list_getD (0, 0)).comp
    (PeriodicGridDrawing.vertexPositions_primrec.comp
      (Primrec.snd.comp Primrec.fst))
    (Primrec.list_idxOf.comp
      Primrec.snd (Primrec.fst.comp Primrec.fst))

theorem incidenceRoute_primrec : Primrec₂ incidenceRoute := by
  exact edgeRoute_primrec.comp
    (Input.drawing_primrec.comp Primrec.fst)
    (incidenceRouteIndex_primrec.comp
      (Input.problem_primrec.comp Primrec.fst) Primrec.snd)

theorem periodTranslation_primrec :
    Primrec₂ PeriodicGridDrawing.periodTranslation := by
  exact cell_scale_primrec.comp
    (int_ofNat_primrec.comp
      (PeriodicGridDrawing.gridSize_primrec.comp Primrec.fst))
    Primrec.snd

theorem translatePolyline_primrec :
    Primrec fun input : Cell × List Cell =>
      translatePolyline input.1 input.2 := by
  exact Primrec.list_map Primrec.snd
    (cell_add_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem joinPolylines_primrec :
    Primrec₂ (joinPolylines : List Cell → List Cell → List Cell) := by
  exact (Primrec.list_append.comp Primrec.fst
    (Primrec.list_tail.comp Primrec.snd)).to₂

theorem reversedIncidenceRouteAt_primrec :
    Primrec fun input : ((Input × WireColor) × Incidence) × Incidence =>
      reversedIncidenceRouteAt input.1.1.1 input.1.1.2
        input.1.2 input.2 := by
  let compilerInput : Primrec (fun input :
      ((Input × WireColor) × Incidence) × Incidence => input.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have offsetDifference : Primrec (fun input :
      ((Input × WireColor) × Incidence) × Incidence =>
        Cell.sub input.1.2.offset input.2.offset) :=
    cell_sub_primrec.comp
      (Incidence.offset_primrec.comp
        (Primrec.snd.comp Primrec.fst))
      (Incidence.offset_primrec.comp Primrec.snd)
  have translation : Primrec (fun input :
      ((Input × WireColor) × Incidence) × Incidence =>
        input.1.1.1.drawing.periodTranslation
          (Cell.sub input.1.2.offset input.2.offset)) :=
    periodTranslation_primrec.comp
      (Input.drawing_primrec.comp compilerInput)
      offsetDifference
  have tag : Primrec (fun input :
      ((Input × WireColor) × Incidence) × Incidence =>
        (IncidenceTag.mk input.2.tripleIndex input.1.1.2)) :=
    incidenceTag_mk_primrec.comp
      (Incidence.tripleIndex_primrec.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have route : Primrec (fun input :
      ((Input × WireColor) × Incidence) × Incidence =>
        incidenceRoute input.1.1.1
          (IncidenceTag.mk input.2.tripleIndex input.1.1.2)) :=
    incidenceRoute_primrec.comp compilerInput tag
  refine (Primrec.list_reverse.comp
    (translatePolyline_primrec.comp
      (Primrec.pair translation route))).of_eq ?_
  intro input
  rfl

theorem contractedEdgeRoute_primrec :
    Primrec₂ contractedEdgeRoute := by
  let Combined := Input × ContractedEdge
  have edgeData : Primrec (fun input : Combined =>
      ContractedEdge.equivData input.2) :=
    ContractedEdge.equivData_primrec.comp Primrec.snd
  have retained : Primrec₂ fun (input : Combined)
      (data : WireColor × Nat × Incidence) =>
      incidenceRoute input.1
        ⟨data.2.2.tripleIndex, data.1⟩ := by
    have tag : Primrec (fun combined : Combined ×
        (WireColor × Nat × Incidence) =>
          IncidenceTag.mk combined.2.2.2.tripleIndex combined.2.1) :=
      incidenceTag_mk_primrec.comp
        (Incidence.tripleIndex_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.snd)
    exact (incidenceRoute_primrec.comp
      (Primrec.fst.comp Primrec.fst) tag).to₂
  have through : Primrec₂ fun (input : Combined)
      (data : WireColor × Nat × Incidence × Incidence) =>
      joinPolylines
        (incidenceRoute input.1
          ⟨data.2.2.1.tripleIndex, data.1⟩)
        (reversedIncidenceRouteAt input.1 data.1
          data.2.2.1 data.2.2.2) := by
    let HandlerInput := Combined ×
      (WireColor × Nat × Incidence × Incidence)
    have sourceTag : Primrec (fun combined : HandlerInput =>
        IncidenceTag.mk combined.2.2.2.1.tripleIndex combined.2.1) :=
      incidenceTag_mk_primrec.comp
        (Incidence.tripleIndex_primrec.comp
          (Primrec.fst.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.fst.comp Primrec.snd)
    have sourceRoute : Primrec (fun combined : HandlerInput =>
        incidenceRoute combined.1.1
          (IncidenceTag.mk combined.2.2.2.1.tripleIndex
            combined.2.1)) :=
      incidenceRoute_primrec.comp
        (Primrec.fst.comp Primrec.fst) sourceTag
    have targetRoute : Primrec (fun combined : HandlerInput =>
        reversedIncidenceRouteAt combined.1.1 combined.2.1
          combined.2.2.2.1 combined.2.2.2.2) :=
      (reversedIncidenceRouteAt_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair
              (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp Primrec.snd))
            (Primrec.fst.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).of_eq
        fun _ => rfl
    exact (joinPolylines_primrec.comp sourceRoute targetRoute).to₂
  exact (Primrec.sumCasesOn edgeData retained through).of_eq fun input => by
    rcases input with ⟨compilerInput, edge⟩
    cases edge <;> rfl

theorem contractedVertexPositions_primrec :
    Primrec contractedVertexPositions := by
  have tagged : Primrec fun input : Input =>
      input.problem.contractedGraph.vertices.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (contractedGraphVertices_primrec.comp Input.problem_primrec)
  have position : Primrec₂ fun (input : Input)
      (taggedVertex : PeriodicThreeDMVertex × Nat) =>
      input.drawing.vertexPositions.getD
        (input.problem.incidenceGraph.vertices.idxOf taggedVertex.1)
        (0, 0) := by
    exact (vertexPosition_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (incidenceGraphVertices_primrec.comp
            (Input.problem_primrec.comp Primrec.fst))
          (Input.drawing_primrec.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))).to₂
  exact Primrec.list_map tagged position

theorem contractedDrawing_primrec : Primrec contractedDrawing := by
  have routes : Primrec (fun input : Input =>
      input.problem.contractedEdges.zipIdx.map fun tagged =>
        contractedEdgeRoute input tagged.1) := by
    have tagged : Primrec fun input : Input =>
        input.problem.contractedEdges.zipIdx :=
      PeriodicThreeSATThree.zipIdx_primrec.comp
        (contractedEdges_primrec.comp Input.problem_primrec)
    exact Primrec.list_map tagged
      (contractedEdgeRoute_primrec.comp
        Primrec.fst (Primrec.fst.comp Primrec.snd)).to₂
  have data : Primrec (fun input : Input =>
      (input.drawing.gridSizePred,
        contractedVertexPositions input,
        input.problem.contractedEdges.zipIdx.map fun tagged =>
          contractedEdgeRoute input tagged.1)) :=
    Primrec.pair
      (PeriodicGridDrawing.gridSizePred_primrec.comp Input.drawing_primrec)
      (Primrec.pair contractedVertexPositions_primrec routes)
  exact (PeriodicGridDrawing.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
