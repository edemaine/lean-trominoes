/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseGlobalStableRankAttachmentSemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation

/-! # Family attachment of global stable-rank slots -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Pointwise successful global-rank attachment lifts to an explicitly
indexed clause family. The dummy position is harmless because the finite
query depends only on the clause's literal list and global index. -/
theorem retainedDirectClauseRouteTailRecordQueriesOfGlobalStableRankBlocks
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula))
    (clausesMember : ∀ taggedClause ∈ clauses.zipIdx start,
      taggedClause ∈
        (retainedFinalCoordinatedScaledSource formula).erase.clauses.zipIdx)
    (clausesNonempty : ∀ clause ∈ clauses, clause ≠ [])
    (clausesWidth : ∀ clause ∈ clauses, clause.length ≤ 3)
    (choicesSome : ∀ taggedClause ∈ clauses.zipIdx start,
      ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula taggedClause.2 taggedLiteral.2 = some choice) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (List.zip
          (retainedFinalIndexedClauseQueriesFrom formula start clauses)
          ((clauses.zipIdx start).map fun taggedClause =>
            RetainedDirectClauseOccurrenceSlots.ofList
              (retainedOccurrenceGlobalStableTerminalSlotBlock
                (retainedFinalCoordinatedScaledSource formula).erase
                (retainedFinalCoordinatedScaledSourceRoutes formula)
                taggedClause))) =
      (clauses.zipIdx start).map fun taggedClause =>
        retainedFinalDirectClauseRouteTailRecordQuery
          formula taggedClause.2 ⟨(0, 0), taggedClause.1⟩ := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause clauses induction =>
      have headMember :
          (clause, start) ∈ (clause :: clauses).zipIdx start := by
        simp only [List.zipIdx_cons, List.mem_cons, true_or]
      have tailMembers : ∀ taggedClause ∈ clauses.zipIdx (start + 1),
          taggedClause ∈
            (retainedFinalCoordinatedScaledSource formula).erase.clauses.zipIdx := by
        intro taggedClause taggedMember
        exact clausesMember taggedClause (by
          simp only [List.zipIdx_cons, List.mem_cons]
          exact Or.inr taggedMember)
      have tailNonempty : ∀ tailClause ∈ clauses,
          tailClause ≠ [] := by
        intro tailClause tailMember
        exact clausesNonempty tailClause (by simp [tailMember])
      have tailWidth : ∀ tailClause ∈ clauses,
          tailClause.length ≤ 3 := by
        intro tailClause tailMember
        exact clausesWidth tailClause (by simp [tailMember])
      have tailChoices : ∀ taggedClause ∈ clauses.zipIdx (start + 1),
          ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
            ∃ choice,
              retainedFinalDirectSourceRouteChoice?
                  formula taggedClause.2 taggedLiteral.2 = some choice := by
        intro taggedClause taggedMember taggedLiteral literalMember
        exact choicesSome taggedClause (by
          simp only [List.zipIdx_cons, List.mem_cons]
          exact Or.inr taggedMember) taggedLiteral literalMember
      unfold retainedFinalIndexedClauseQueriesFrom
      simp only [List.zipIdx_cons, List.map_cons, List.zip_cons_cons,
        retainedDirectClauseRouteTailRecordQueriesOfSlotInputs,
        List.flatMap_cons]
      rw [retainedDirectClauseRouteTailRecordQueryOfGlobalStableRankBlock
        formula (0, 0) (clause, start) certificate
        (clausesMember (clause, start) headMember)
        (clausesNonempty clause (by simp))
        (clausesWidth clause (by simp))
        (choicesSome (clause, start) headMember)]
      simp only [Option.toList_some, List.singleton_append,
        List.cons.injEq, true_and]
      exact induction (start + 1) tailMembers tailNonempty tailWidth
        tailChoices

end PeriodicEightOccurrenceSplit
end LeanTrominoes
