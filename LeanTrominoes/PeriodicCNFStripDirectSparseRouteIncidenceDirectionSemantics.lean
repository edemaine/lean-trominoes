/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedAssignmentData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMIncidenceRouteLookup
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestPresentationDirections

/-! # Direct contracted requests as assembled incidence direction words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open PeriodicThreeDM
open PeriodicThreeDM.NormalizationCompiler
open PeriodicThreeDM.NormalizationDirectionRequest

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteIncidenceDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A direct retained edge request reads exactly its one original assembled
incidence route. -/
theorem directSparse_ofEdge_retained_directions_eq_assembled
    (symbols : List encoding.Γ)
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (member : incidence ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.incidences color atom) :
    let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
      decider symbols
    (ofEdge
        (directSparseComputedNormalizationInputOfSymbols decider symbols)
        (.retained color atom incidence)).directions =
      unitSubdivisionDirections
        (horizontalAssembledRouteAtTagComputed
          (source, ⟨incidence.tripleIndex, color⟩)) := by
  dsimp only
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  have tagMember :
      ⟨incidence.tripleIndex, color⟩ ∈ input.problem.incidenceTags :=
    incidenceTag_mem_of_incidence_mem
      input.problem color atom member
  rw [show directSparseComputedNormalizationInputOfSymbols
      decider symbols = input by rfl]
  rw [ofEdge_retained_directions]
  rw [show input = horizontalNormalizationInputComputed source by rfl]
  rw [horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
    source ⟨incidence.tripleIndex, color⟩ tagMember]

/-- A direct degree-two edge request reads only the two original assembled
incidence routes.  Contracted joining, periodic translation, and reversal
have been reduced to concatenation and list reversal of their direction
words. -/
theorem directSparse_ofEdge_through_directions_eq_assembled
    (symbols : List encoding.Γ)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (firstMember : first ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.incidences color atom)
    (secondMember : second ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.incidences color atom) :
    let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
      decider symbols
    (ofEdge
        (directSparseComputedNormalizationInputOfSymbols decider symbols)
        (.through color atom first second)).directions =
      unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨first.tripleIndex, color⟩)) ++
        unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨second.tripleIndex, color⟩)).reverse := by
  dsimp only
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  have inputEq : input = normalizationInput source :=
    directSparseComputedNormalizationInputOfSymbols_eq decider symbols
  have firstMemberSemantic :
      first ∈ (problem source).incidences color atom := by
    rw [← normalizationInput_problem source, ← inputEq]
    exact firstMember
  have secondMemberSemantic :
      second ∈ (problem source).incidences color atom := by
    rw [← normalizationInput_problem source, ← inputEq]
    exact secondMember
  have firstTagMember :
      ⟨first.tripleIndex, color⟩ ∈ input.problem.incidenceTags :=
    incidenceTag_mem_of_incidence_mem
      input.problem color atom firstMember
  have secondTagMember :
      ⟨second.tripleIndex, color⟩ ∈ input.problem.incidenceTags :=
    incidenceTag_mem_of_incidence_mem
      input.problem color atom secondMember
  have firstLength :
      2 ≤ (incidenceRoute input
        ⟨first.tripleIndex, color⟩).length := by
    have firstTagMemberSemantic :
        ⟨first.tripleIndex, color⟩ ∈
          (problem source).incidenceTags :=
      incidenceTag_mem_of_incidence_mem
        (problem source) color atom firstMemberSemantic
    have length :=
      (presentation source).toPlanarPresentation
        |>.incidenceRoute_length_ge_two firstTagMemberSemantic
    simpa only [inputEq, normalizationInput, inputOfPresentation,
      incidenceRoute, PlanarPresentation.incidenceRoute] using length
  have boundary :
      (incidenceRoute input
          ⟨first.tripleIndex, color⟩).getLast? =
        (reversedIncidenceRouteAt input color first second).head? := by
    have common :=
      (presentation source).toPlanarPresentation
        |>.throughIncidenceRoutes_boundary
          color atom firstMemberSemantic secondMemberSemantic
    simpa only [inputEq, normalizationInput, inputOfPresentation,
      incidenceRoute, reversedIncidenceRouteAt,
      PlanarPresentation.incidenceRoute,
      PlanarPresentation.reversedIncidenceRouteAt] using common
  rw [show directSparseComputedNormalizationInputOfSymbols
      decider symbols = input by rfl]
  rw [NormalizationDirectionRequest.ofEdge_through_directions
    input color atom first second firstLength boundary]
  rw [show input = horizontalNormalizationInputComputed source by rfl]
  rw [horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
      source ⟨first.tripleIndex, color⟩ firstTagMember,
    horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
      source ⟨second.tripleIndex, color⟩ secondTagMember]

end PeriodicCNFStripReduction
end LeanTrominoes

end
