/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicCNFIncidenceLiteralPortRank
import LeanTrominoes.PeriodicCNFPlanarWidth
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice

/-! # Shape of routed-clause direct choices -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing

private theorem map_zipIdx_filter_fst
    {Value Output : Type}
    (values : List Value)
    (selected : Value → Bool)
    (output : Value → Output) :
    ((values.zipIdx.filter fun tagged => selected tagged.1).map
        fun tagged => output tagged.1) =
      (values.filter selected).map output := by
  simpa only [← List.map_eq_flatMap] using
    (IndexedListScan.zipIdx_filter_fst_flatMap
      values selected (fun value => [output value]))

/-- Routed occurrences retain their within-clause literal indices in
presentation order. -/
private theorem clauseRouteOccurrenceLiteralIndices_eq_range
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMember : taggedClause ∈ formula.clauses.zipIdx)
    (translate : Cell) :
    (clauseRouteOccurrencesAt formula
        (taggedClause.2, translate)).map
          (fun occurrence => occurrence.incidence.literalIndex) =
      List.range taggedClause.1.length := by
  unfold clauseRouteOccurrencesAt
  rw [List.map_map]
  calc
    _ = ((PeriodicCNF.incidencesWithMetadata formula).filter
          fun incidence =>
            decide (incidence.clauseIndex = taggedClause.2)).map
          CNFIncidence.literalIndex :=
      map_zipIdx_filter_fst _ _ _
    _ = _ := by
      rw [PeriodicOrthocrossing.incidencesWithMetadata_filter_clauseIndex
        formula taggedClause taggedClauseMember]
      simp only [List.map_map]
      change taggedClause.1.zipIdx.map Prod.snd = _
      rw [List.zipIdx_map_snd, List.range_eq_range']

/-- The physical routed-clause arms occur in the same left-to-right order
as the source clause's literal presentation. -/
private theorem routedClausePortArms_eq_range
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMember : taggedClause ∈ formula.clauses.zipIdx)
    (translate : Cell) :
    (routedClausePortLiterals formula
        (taggedClause.2, translate)).map Prod.fst =
      (List.range taggedClause.1.length).map targetDuplicatorArm := by
  unfold routedClausePortLiterals
  rw [List.map_map]
  calc
    _ = (clauseRouteOccurrencesAt formula
          (taggedClause.2, translate)).map fun occurrence =>
            targetDuplicatorArm occurrence.incidence.literalIndex := by
      apply List.map_congr_left
      intro occurrence occurrenceMember
      rcases List.mem_map.mp occurrenceMember with
        ⟨taggedIncidence, taggedIncidenceMember, occurrenceEq⟩
      subst occurrence
      change
        targetDuplicatorArm
            (portRank formula.incidenceGraph
              (sourcePort taggedIncidence.1.edge taggedIncidence.2)) =
          targetDuplicatorArm taggedIncidence.1.literalIndex
      rw [incidenceSourcePortRank_eq_literalIndex
        formula taggedIncidence
        (List.mem_filter.mp taggedIncidenceMember).1]
    _ = ((clauseRouteOccurrencesAt formula
          (taggedClause.2, translate)).map fun occurrence =>
            occurrence.incidence.literalIndex).map
          targetDuplicatorArm := by
      simp only [List.map_map, Function.comp_def]
    _ = _ := by
      rw [clauseRouteOccurrenceLiteralIndices_eq_range
        formula taggedClause taggedClauseMember translate]

/-- A successful raw routed-clause selector for a represented width-three
source clause has routed-clause kind and the exact literal presentation
index required by the stable final query template. -/
theorem retainedDirectSourceRouteChoice?_routedClause_eq_some_presentation_shape
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMember : taggedClause ∈ formula.clauses.zipIdx)
    (translate : Cell)
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedDirectSourceRouteChoice? formula
          (.routedClause (taggedClause.2, translate)) literalIndex =
        some choice) :
    choice.kind = .routedClause ∧
      choice.index.val = literalIndex := by
  simp only [retainedDirectSourceRouteChoice?] at lookup
  split at lookup
  next literalIndexLt =>
    simp only [Option.some.injEq] at lookup
    subst choice
    constructor
    · rfl
    · have occurrenceLength :
          (clauseRouteOccurrencesAt formula
            (taggedClause.2, translate)).length =
              taggedClause.1.length :=
        clauseRouteOccurrencesAt_length
          formula taggedClause taggedClauseMember translate
      have literalIndexClauseLt : literalIndex < taggedClause.1.length := by
        simpa [routedClausePortLiterals, occurrenceLength] using
          literalIndexLt
      have armsEq :=
        routedClausePortArms_eq_range
          formula taggedClause taggedClauseMember translate
      have armLookup := congrArg
        (fun arms => arms[literalIndex]?) armsEq
      have selectedArm :
          ((routedClausePortLiterals formula
            (taggedClause.2, translate)).get
              ⟨literalIndex, literalIndexLt⟩).1 =
            targetDuplicatorArm literalIndex := by
        simpa [List.getElem?_map, literalIndexLt,
          literalIndexClauseLt] using armLookup
      rw [selectedArm]
      have clauseWidth : taggedClause.1.length ≤ 3 :=
        sourceWidth taggedClause.1
          (List.fst_mem_of_mem_zipIdx taggedClauseMember)
      have literalIndexLtThree : literalIndex < 3 :=
        lt_of_lt_of_le literalIndexClauseLt clauseWidth
      interval_cases literalIndex <;>
        rfl
  next => contradiction

end PeriodicEightOccurrenceSplit
end LeanTrominoes
