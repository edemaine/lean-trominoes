/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOccurrences

/-! # Exact order of routed-variable endpoint nodes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The neighboring route-occurrence enumeration has no duplicates: its
global edge index distinguishes incidence blocks and its translation
distinguishes entries inside each block. -/
theorem drawingCNFRouteOccurrences_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingCNFRouteOccurrences formula).Nodup := by
  have indicesPairwise :
      (PeriodicCNF.incidencesWithMetadata formula).zipIdx.Pairwise
        (fun first second => first.2 ≠ second.2) := by
    rw [← List.pairwise_map]
    exact List.nodup_zipIdx_map_snd
      (PeriodicCNF.incidencesWithMetadata formula)
  unfold drawingCNFRouteOccurrences
  rw [List.nodup_flatMap]
  constructor
  · intro taggedIncidence _
    apply neighborTranslations_nodup.map_on
    intro first _ second _ equality
    exact congrArg CNFRouteOccurrence.translate equality
  · exact indicesPairwise.imp fun
      {first second} indexNe => by
        unfold Function.onFun
        rw [List.disjoint_left]
        intro occurrence firstMember secondMember
        rcases List.mem_map.mp firstMember with
          ⟨firstTranslate, _firstTranslateMember, firstEq⟩
        rcases List.mem_map.mp secondMember with
          ⟨secondTranslate, _secondTranslateMember, secondEq⟩
        have indexEq := congrArg CNFRouteOccurrence.edgeIndex
          (firstEq.trans secondEq.symm)
        exact indexNe indexEq

/-- Sorting the selected occurrences by global edge index preserves their
duplicate-free enumeration. -/
theorem variableRouteOccurrencesAt_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    (variableRouteOccurrencesAt formula site).Nodup := by
  unfold variableRouteOccurrencesAt
  apply (List.perm_insertionSort
    (fun first second : CNFRouteOccurrence Variable =>
      first.edgeIndex ≤ second.edgeIndex) _).nodup_iff.mpr
  exact (drawingCNFRouteOccurrences_nodup formula).filter _

/-- The target-terminal nodes selected at a variable site are already
duplicate-free, so `routedVariableNodes` preserves their exact sorted order. -/
theorem routedVariableNodes_eq_map_targetTerminals
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    routedVariableNodes formula site =
      (variableRouteOccurrencesAt formula site).map fun occurrence =>
        PlanarSATNode.carrier
          (.terminal (occurrence.targetTerminal formula)) := by
  unfold routedVariableNodes
  rw [List.dedup_eq_self]
  apply (variableRouteOccurrencesAt_nodup formula site).map_on
  intro first firstMember second secondMember nodeEq
  have firstDrawing :=
    (variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site firstMember).1
  have secondDrawing :=
    (variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site secondMember).1
  exact drawingCNFRouteOccurrences_targetTerminal_injective_on
    formula firstDrawing secondDrawing
      (CarrierNode.terminal.inj
        (PlanarSATNode.carrier.inj nodeEq))

end PeriodicOrthocrossing
end LeanTrominoes
