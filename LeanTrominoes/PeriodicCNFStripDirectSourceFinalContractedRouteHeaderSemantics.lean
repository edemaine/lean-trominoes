/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteAlphabetAlignedZipCompiler
import LeanTrominoes.PeriodicCNFStripIncidenceHeaderAssembler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSelectedIncidenceEndpointSummarySemantics

/-! # The finite endpoint assembler emits the exact geometric route headers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM
open PeriodicThreeDM.NormalizationDirectionRequest

/-- Suppressing an element joins the two actual triple endpoint headers. -/
theorem throughHeader_horizontal (source : PeriodicCNF Nat) (color : WireColor)
    (atom : Nat) (first second : Incidence) :
    IncidenceHeaderAssembler.throughHeader
      (horizontalIncidenceEndpointSummary source ⟨first.tripleIndex, color⟩)
      (horizontalIncidenceEndpointSummary source ⟨second.tripleIndex, color⟩) =
      horizontalAssembledRouteRequestHeader source (.through color atom first second) := by
  unfold IncidenceHeaderAssembler.throughHeader horizontalAssembledRouteRequestHeader
    horizontalAssembledSourceEndpointHeaderData horizontalAssembledTargetEndpointHeaderData
  simp only [ContractedEdge.sourceIncidence, ContractedEdge.color]
  rw [horizontalIncidenceEndpointSummary_tripleEndpointData,
    horizontalIncidenceEndpointSummary_tripleEndpointData]

/-- A retained element's complete fan is reconstructed from the three
 terminal directions in its original incidence order. -/
theorem retainedHeader_horizontal (source : PeriodicCNF Nat) (color : WireColor)
    (atom : Nat) (first second third incidence : Incidence)
    (incidencesEq : (horizontalThreeDMProblemComputed source).incidences color atom =
      [first, second, third]) :
    IncidenceHeaderAssembler.retainedHeader
      (IncidenceHeaderAssembler.retainedFan
        (horizontalIncidenceEndpointSummary source ⟨first.tripleIndex, color⟩)
        (horizontalIncidenceEndpointSummary source ⟨second.tripleIndex, color⟩)
        (horizontalIncidenceEndpointSummary source ⟨third.tripleIndex, color⟩))
      (horizontalIncidenceEndpointSummary source ⟨incidence.tripleIndex, color⟩) =
      horizontalAssembledRouteRequestHeader source (.retained color atom incidence) := by
  have semanticIncidences : (problem source).incidences color atom = [first, second, third] := by
    rw [← horizontalThreeDMProblemComputed_eq_problem]
    exact incidencesEq
  have fanEq :
      IncidenceHeaderAssembler.retainedFan
        (horizontalIncidenceEndpointSummary source ⟨first.tripleIndex, color⟩)
        (horizontalIncidenceEndpointSummary source ⟨second.tripleIndex, color⟩)
        (horizontalIncidenceEndpointSummary source ⟨third.tripleIndex, color⟩) =
      horizontalAssembledRetainedElementTripleData source color atom := by
    unfold IncidenceHeaderAssembler.retainedFan horizontalAssembledRetainedElementTripleData
    rw [semanticIncidences]
    rw [horizontalIncidenceEndpointSummary_retainedSideColor,
      horizontalIncidenceEndpointSummary_retainedSideColor,
      horizontalIncidenceEndpointSummary_retainedSideColor]
  unfold IncidenceHeaderAssembler.retainedHeader horizontalAssembledRouteRequestHeader
    horizontalAssembledSourceEndpointHeaderData horizontalAssembledTargetEndpointHeaderData
    horizontalAssembledRetainedElementEndpointHeaderData
  simp only [ContractedEdge.sourceIncidence, ContractedEdge.color]
  rw [horizontalIncidenceEndpointSummary_tripleEndpointData, fanEq,
    horizontalIncidenceEndpointSummary_retainedSideColor]

private theorem headerOutput_elementPairs (source : PeriodicCNF Nat)
    (pairs : List (WireColor × Nat))
    (valid : ∀ pair ∈ pairs,
      (horizontalThreeDMProblemComputed source).degree pair.1 pair.2 = 2 ∨
      (horizontalThreeDMProblemComputed source).degree pair.1 pair.2 = 3) :
    IncidenceHeaderAssembler.output
      ((CountedContractedIncidence.roles
        (pairs.map (fun pair => (horizontalThreeDMProblemComputed source).degree pair.1 pair.2))).zip
        (pairs.flatMap (horizontalIncidenceEndpointSummariesForElement source))) =
      pairs.flatMap (fun pair =>
        ((horizontalThreeDMProblemComputed source).contractedEdgesForElement pair.1 pair.2).map
          (horizontalAssembledRouteRequestHeader source)) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      have headValid := valid pair (by simp)
      have tailValid : ∀ other ∈ pairs,
          (horizontalThreeDMProblemComputed source).degree other.1 other.2 = 2 ∨
          (horizontalThreeDMProblemComputed source).degree other.1 other.2 = 3 := by
        intro other member
        exact valid other (by simp [member])
      rcases headValid with degreeEq | degreeEq
      · have degree := degreeEq
        unfold PeriodicThreeDM.degree at degree
        obtain ⟨first, second, incidencesEq⟩ := List.length_eq_two.mp degree
        simp only [List.map_cons, List.flatMap_cons]
        rw [degreeEq, CountedContractedIncidence.roles_cons_two]
        simp only [horizontalIncidenceEndpointSummariesForElement, incidencesEq,
          List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.zip_cons_cons,
          PeriodicThreeDM.contractedEdgesForElement]
        rw [IncidenceHeaderAssembler.output_through_cons, induction tailValid,
          throughHeader_horizontal source pair.1 pair.2 first second]
        simp only [PeriodicThreeDM.contractedEdgesForElement]
      · have degree := degreeEq
        unfold PeriodicThreeDM.degree at degree
        obtain ⟨first, second, third, incidencesEq⟩ := List.length_eq_three.mp degree
        simp only [List.map_cons, List.flatMap_cons]
        rw [degreeEq, CountedContractedIncidence.roles_cons_three]
        simp only [horizontalIncidenceEndpointSummariesForElement, incidencesEq,
          List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.zip_cons_cons,
          PeriodicThreeDM.contractedEdgesForElement]
        rw [IncidenceHeaderAssembler.output_retained_cons, induction tailValid]
        unfold IncidenceHeaderAssembler.retainedHeaders
        dsimp only
        rw [retainedHeader_horizontal source pair.1 pair.2 first second third first incidencesEq,
          retainedHeader_horizontal source pair.1 pair.2 first second third second incidencesEq,
          retainedHeader_horizontal source pair.1 pair.2 first second third third incidencesEq]
        simp only [PeriodicThreeDM.contractedEdgesForElement, List.cons_append, List.nil_append]

/-- The complete degree-driven header stream is the canonical contracted-edge
header list, including all three headers at each retained element. -/
theorem headerOutput_horizontal (source : PeriodicCNF Nat) :
    IncidenceHeaderAssembler.output
      ((CountedContractedIncidence.roles
        (CountedContractedIncidence.horizontalElementDegrees (horizontalThreeDMProblemComputed source))).zip
        (horizontalIncidenceEndpointSummariesByElement source)) =
      (horizontalThreeDMProblemComputed source).contractedEdges.map
        (horizontalAssembledRouteRequestHeader source) := by
  have degrees : (horizontalThreeDMProblemComputed source).DegreeTwoOrThree := by
    rw [horizontalThreeDMProblemComputed_eq_problem]
    exact problem_degreeTwoOrThree source
  have pairsValid : ∀ pair ∈ CountedContractedIncidence.horizontalElementPairs
      (horizontalThreeDMProblemComputed source),
      (horizontalThreeDMProblemComputed source).degree pair.1 pair.2 = 2 ∨
      (horizontalThreeDMProblemComputed source).degree pair.1 pair.2 = 3 := by
    intro pair member
    simp only [CountedContractedIncidence.horizontalElementPairs, List.mem_flatMap, List.mem_map] at member
    obtain ⟨color, _, atom, atomMember, rfl⟩ := member
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      degrees color atom (List.mem_range.mp atomMember)
  unfold CountedContractedIncidence.horizontalElementDegrees horizontalIncidenceEndpointSummariesByElement
  rw [headerOutput_elementPairs source _ pairsValid]
  unfold CountedContractedIncidence.horizontalElementPairs PeriodicThreeDM.contractedEdges
    PeriodicThreeDM.contractedEdgesForColor
  rw [List.flatMap_assoc, List.map_flatMap]
  apply List.flatMap_congr
  intro color _
  rw [List.flatMap_map, List.map_flatMap]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

def directSourceFinalContractedRouteHeaders (symbols : List encoding.Γ) : List Header :=
  IncidenceHeaderAssembler.output
    ((CountedContractedIncidence.roles (directSourceFinalCanonicalElementDegrees decider symbols)).zip
      (directSourceFinalSelectedIncidenceEndpointSummaries decider symbols))

/-- The header source is obtained by pairing the independently compiled role
and endpoint columns, then applying the fixed finite-state assembler. -/
noncomputable def directSourceFinalContractedRouteHeadersComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalContractedRouteHeaders decider) := by
  classical
  letI : Inhabited Header := ⟨IncidenceHeaderAssembler.throughHeader default default⟩
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    let roleCompiler := CountedContractedIncidence.rolesComputableInPolyTimeOf id
      (directSourceFinalCanonicalElementDegrees decider)
      (directSourceFinalCanonicalElementDegreesComputableInPolyTime decider)
    let pairCompiler := FiniteAlphabetAlignedZip.computableInPolyTimeOf id
      (fun symbols => CountedContractedIncidence.roles (directSourceFinalCanonicalElementDegrees decider symbols))
      (directSourceFinalSelectedIncidenceEndpointSummaries decider)
      (fun symbols => (directSourceFinalSelectedIncidenceEndpointSummaries_length_roles decider symbols).symm)
      roleCompiler (directSourceFinalSelectedIncidenceEndpointSummariesComputableInPolyTime decider)
    unfold directSourceFinalContractedRouteHeaders
    exact TM2CompositionMachine.computableInPolyTime pairCompiler
      IncidenceHeaderAssembler.computableInPolyTime
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- The explicit compiler emits exactly the geometric header at each
canonical contracted edge, without a remaining source-specific premise. -/
theorem directSourceFinalContractedRouteHeaders_eq_horizontal (symbols : List encoding.Γ) :
    directSourceFinalContractedRouteHeaders decider symbols =
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.map
        (horizontalAssembledRouteRequestHeader
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  unfold directSourceFinalContractedRouteHeaders
  rw [directSourceFinalCanonicalElementDegrees_eq_horizontal,
    directSourceFinalSelectedIncidenceEndpointSummaries_eq_horizontal, headerOutput_horizontal]

end LeanTrominoes.PeriodicCNFStripReduction

end
