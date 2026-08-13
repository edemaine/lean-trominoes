/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-! ## Contracted endpoint fans -/

theorem axisDirection_between_primrec : Primrec₂ AxisDirection.between := by
  change Primrec fun input : Cell × Cell =>
    AxisDirection.between input.1 input.2
  let firstX : Primrec (fun input : Cell × Cell => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  let firstY : Primrec (fun input : Cell × Cell => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  let secondX : Primrec (fun input : Cell × Cell => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  let secondY : Primrec (fun input : Cell × Cell => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  let sameX := Primrec.eq.comp firstX secondX
  let sameY := Primrec.eq.comp firstY secondY
  let east := int_lt_primrec.comp firstX secondX
  let west := int_lt_primrec.comp secondX firstX
  let north := int_lt_primrec.comp firstY secondY
  let south := int_lt_primrec.comp secondY firstY
  exact (Primrec.ite sameY
    (Primrec.ite east (Primrec.const .east)
      (Primrec.ite west (Primrec.const .west)
        (Primrec.const .invalid)))
    (Primrec.ite sameX
      (Primrec.ite north (Primrec.const .north)
        (Primrec.ite south (Primrec.const .south)
          (Primrec.const .invalid)))
      (Primrec.const .invalid))).of_eq fun _ => rfl

theorem axisDirection_opposite_primrec :
    Primrec AxisDirection.opposite :=
  Primrec.dom_finite AxisDirection.opposite

theorem polylineFirstDirection_primrec :
    Primrec AxisDirection.polylineFirstDirection := by
  let enough : PrimrecPred fun points : List Cell => 2 ≤ points.length :=
    Primrec.nat_le.comp (Primrec.const 2) Primrec.list_length
  let itemAt (index : Nat) : Primrec (fun points : List Cell =>
      points.getD index (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp Primrec.id (Primrec.const index)
  refine (Primrec.ite enough
    (axisDirection_between_primrec.comp (itemAt 0) (itemAt 1))
    (Primrec.const .invalid)).of_eq ?_
  intro points
  rcases points with _ | ⟨first, points⟩
  · rfl
  rcases points with _ | ⟨second, points⟩ <;> rfl

theorem polylineLastDirection_primrec :
    Primrec AxisDirection.polylineLastDirection := by
  exact (axisDirection_opposite_primrec.comp
    (polylineFirstDirection_primrec.comp Primrec.list_reverse)).of_eq
      fun _ => rfl

theorem vertexSide_ofDirection_primrec :
    Primrec VertexSide.ofDirection :=
  Primrec.dom_finite VertexSide.ofDirection

theorem periodicEdge_mk_primrec :
    Primrec fun input :
        (PeriodicThreeDMVertex × PeriodicThreeDMVertex) × Cell =>
      (PeriodicEdge.mk input.1.1 input.1.2 input.2) := by
  have inverse : Primrec
      (@PeriodicEdge.equivData PeriodicThreeDMVertex).symm :=
    Primrec.of_equiv_symm
  exact inverse.comp
    (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem contractedEdge_toPeriodicEdge_primrec :
    Primrec ContractedEdge.toPeriodicEdge := by
  have edgeData := ContractedEdge.equivData_primrec
  have retained : Primrec₂ fun (_edge : ContractedEdge)
      (data : WireColor × Nat × Incidence) =>
      (PeriodicEdge.mk
        (PeriodicThreeDMVertex.triple data.2.2.tripleIndex)
        (PeriodicThreeDMVertex.element data.1 data.2.1)
        data.2.2.offset) := by
    exact (periodicEdge_mk_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (periodicThreeDMVertex_triple_primrec.comp
            (Incidence.tripleIndex_primrec.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (periodicThreeDMVertex_element_primrec.comp
            (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        (Incidence.offset_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).to₂
  have through : Primrec₂ fun (_edge : ContractedEdge)
      (data : WireColor × Nat × Incidence × Incidence) =>
      (PeriodicEdge.mk
        (PeriodicThreeDMVertex.triple data.2.2.1.tripleIndex)
        (PeriodicThreeDMVertex.triple data.2.2.2.tripleIndex)
        (Cell.sub data.2.2.1.offset data.2.2.2.offset)) := by
    exact (periodicEdge_mk_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (periodicThreeDMVertex_triple_primrec.comp
            (Incidence.tripleIndex_primrec.comp
              (Primrec.fst.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
          (periodicThreeDMVertex_triple_primrec.comp
            (Incidence.tripleIndex_primrec.comp
              (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
        (cell_sub_primrec.comp
          (Incidence.offset_primrec.comp
            (Primrec.fst.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (Incidence.offset_primrec.comp
            (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))).to₂
  exact (Primrec.sumCasesOn edgeData retained through).of_eq fun edge => by
    cases edge <;> rfl

theorem periodicEdge_source_primrec :
    Primrec (PeriodicEdge.source :
      PeriodicEdge PeriodicThreeDMVertex → PeriodicThreeDMVertex) := by
  have forward : Primrec
      (@PeriodicEdge.equivData PeriodicThreeDMVertex) :=
    Primrec.of_equiv
  exact (Primrec.fst.comp forward).of_eq fun _ => rfl

theorem periodicEdge_target_primrec :
    Primrec (PeriodicEdge.target :
      PeriodicEdge PeriodicThreeDMVertex → PeriodicThreeDMVertex) := by
  have forward : Primrec
      (@PeriodicEdge.equivData PeriodicThreeDMVertex) :=
    Primrec.of_equiv
  exact ((Primrec.fst.comp Primrec.snd).comp forward).of_eq fun _ => rfl

theorem contractedEdge_color_primrec : Primrec ContractedEdge.color := by
  have edgeData := ContractedEdge.equivData_primrec
  exact (Primrec.sumCasesOn edgeData
    (Primrec.fst.comp Primrec.snd).to₂
    (Primrec.fst.comp Primrec.snd).to₂).of_eq fun edge => by
      cases edge <;> rfl

theorem contractedEndpoint_source_primrec :
    Primrec ContractedEndpoint.source :=
  ContractedEndpoint.equivData_symm_primrec.comp Primrec.sumInl

theorem contractedEndpoint_target_primrec :
    Primrec ContractedEndpoint.target :=
  ContractedEndpoint.equivData_symm_primrec.comp Primrec.sumInr

theorem contractedEndpoint_edge_primrec :
    Primrec ContractedEndpoint.edge := by
  exact (Primrec.sumCasesOn ContractedEndpoint.equivData_primrec
    Primrec.snd.to₂ Primrec.snd.to₂).of_eq fun endpoint => by
      cases endpoint <;> rfl

theorem contractedEndpoint_isSource_primrec :
    Primrec ContractedEndpoint.isSource := by
  exact (Primrec.sumCasesOn ContractedEndpoint.equivData_primrec
    (Primrec.const true).to₂ (Primrec.const false).to₂).of_eq
      fun endpoint => by cases endpoint <;> rfl

theorem contractedEndpoint_vertex_primrec :
    Primrec ContractedEndpoint.vertex := by
  have edge := contractedEndpoint_edge_primrec
  have periodicEdge := contractedEdge_toPeriodicEdge_primrec.comp edge
  let sourceEndpoint : PrimrecPred fun endpoint : ContractedEndpoint =>
      endpoint.isSource = true := by
    exact Primrec.eq.comp
      contractedEndpoint_isSource_primrec
      (Primrec.const true)
  exact (Primrec.ite sourceEndpoint
    (periodicEdge_source_primrec.comp periodicEdge)
    (periodicEdge_target_primrec.comp periodicEdge)).of_eq fun endpoint => by
      cases endpoint <;> rfl

theorem contractedEndpoint_color_primrec :
    Primrec ContractedEndpoint.color :=
  contractedEdge_color_primrec.comp contractedEndpoint_edge_primrec

theorem contractedEndpoints_primrec :
    Primrec PeriodicThreeDM.contractedEndpoints := by
  exact Primrec.list_flatMap contractedEdges_primrec
    (Primrec.list_cons.comp
      (contractedEndpoint_source_primrec.comp Primrec.snd)
      (Primrec.list_cons.comp
        (contractedEndpoint_target_primrec.comp Primrec.snd)
        (Primrec.const []))).to₂

theorem contractedEndpointsAt_primrec :
    Primrec fun input : PeriodicThreeDM × PeriodicThreeDMVertex =>
      input.1.contractedEndpointsAt input.2 := by
  have same : PrimrecRel fun (endpoint : ContractedEndpoint)
      (vertex : PeriodicThreeDMVertex) => endpoint.vertex = vertex :=
    Primrec.eq.comp₂
      (contractedEndpoint_vertex_primrec.comp₂ Primrec₂.left)
      Primrec₂.right
  exact same.listFilter.comp
    (contractedEndpoints_primrec.comp Primrec.fst)
    Primrec.snd

def defaultContractedEndpoint : ContractedEndpoint :=
  .source (.retained .red 0 defaultIncidence)

theorem endpointTripleAt_primrec :
    Primrec fun input : PeriodicThreeDM × PeriodicThreeDMVertex =>
      input.1.endpointTripleAt input.2 := by
  have endpoints := contractedEndpointsAt_primrec
  let itemAt (index : Nat) : Primrec (fun input :
      PeriodicThreeDM × PeriodicThreeDMVertex =>
        (input.1.contractedEndpointsAt input.2).getD index
          defaultContractedEndpoint) :=
    (Primrec.list_getD defaultContractedEndpoint).comp endpoints
      (Primrec.const index)
  have exactlyThree : PrimrecPred fun input :
      PeriodicThreeDM × PeriodicThreeDMVertex =>
      (input.1.contractedEndpointsAt input.2).length = 3 :=
    Primrec.eq.comp (Primrec.list_length.comp endpoints)
      (Primrec.const 3)
  have selected : Primrec (fun input :
      PeriodicThreeDM × PeriodicThreeDMVertex =>
      some ((input.1.contractedEndpointsAt input.2).getD 0
          defaultContractedEndpoint,
        (input.1.contractedEndpointsAt input.2).getD 1
          defaultContractedEndpoint,
        (input.1.contractedEndpointsAt input.2).getD 2
          defaultContractedEndpoint)) :=
    Primrec.option_some.comp
      (Primrec.pair (itemAt 0)
        (Primrec.pair (itemAt 1) (itemAt 2)))
  refine (Primrec.ite exactlyThree selected
    (Primrec.const none)).of_eq ?_
  intro input
  unfold endpointTripleAt
  generalize input.1.contractedEndpointsAt input.2 = endpoints
  rcases endpoints with _ | ⟨first, endpoints⟩
  · rfl
  rcases endpoints with _ | ⟨second, endpoints⟩
  · rfl
  rcases endpoints with _ | ⟨third, endpoints⟩
  · rfl
  rcases endpoints with _ | ⟨fourth, endpoints⟩ <;> rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
