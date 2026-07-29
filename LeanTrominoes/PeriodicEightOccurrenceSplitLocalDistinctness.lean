import LeanTrominoes.PeriodicEightOccurrenceSplitCanonicalAngularRoutes
import LeanTrominoes.PlanarOneInThreeLocalDistinctness

/-!
# Local atom distinctness after fixed-eight occurrence splitting

Collision-free compass ports make all copied source occurrences globally
distinct.  Each copied clause is therefore atom-distinct.  The uniform
separator-enhanced implication ring also has distinct endpoints on every one
of its binary clauses.  Together these facts discharge the local distinctness
hypothesis of the positioned Figure 9 drawings.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Collision freedom implies atom distinctness in every copied source
clause. -/
theorem occurrenceClauses_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (collisionFree : occurrencePorts.CollisionFree source) :
    ∀ clause ∈ occurrenceClauses source occurrencePorts,
      (clause.map PeriodicLiteral.atom).Nodup := by
  have flattenedNodup :
      ((occurrenceClauses source occurrencePorts).flatMap fun clause =>
        clause.map PeriodicLiteral.atom).Nodup := by
    have selectedNodup :
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk
            (occurrenceClauses source occurrencePorts))).Nodup := by
      rw [occurrenceClauses_variableOccurrences]
      exact collisionFree
    simpa [PeriodicCNF.variableOccurrences] using selectedNodup
  exact (List.nodup_flatMap.mp flattenedNodup).1

/-- Every binary implication clause in one fixed separator-enhanced ring has
distinct endpoints. -/
theorem cycleClausesFor_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) :
    ∀ clause ∈ cycleClausesFor atom,
      (clause.map PeriodicLiteral.atom).Nodup := by
  intro clause clauseMember
  simp [cycleClausesFor, copies,
    OccurrenceSplitRing.cycleVertices, ringCopy,
    PeriodicThreeSATThree.cycleClauses,
    PeriodicThreeSATThree.cycleFrom]
    at clauseMember
  rcases clauseMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [PeriodicThreeSATThree.implicationClause,
      copy, portIndex]

end PeriodicEightOccurrenceSplit

namespace PeriodicEightOccurrenceSplitPositioned

/-- Every copied positioned source clause is atom-distinct under a
collision-free port assignment. -/
theorem occurrenceClauses_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    (collisionFree :
      occurrencePorts.CollisionFree source.erase) :
    ∀ clause ∈ occurrenceClauses source occurrencePorts,
      clause.AtomsNodup := by
  intro clause clauseMember
  unfold occurrenceClauses at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedSource, taggedSourceMember, clauseEqual⟩
  subst clause
  unfold occurrenceClause PositionedPeriodicClause.AtomsNodup
  exact
    PeriodicEightOccurrenceSplit.occurrenceClauses_atomsNodup
      source.erase occurrencePorts collisionFree
      (PeriodicEightOccurrenceSplit.occurrenceClause
        occurrencePorts taggedSource.2 taggedSource.1.literals)
      (by
        unfold PeriodicEightOccurrenceSplit.occurrenceClauses
        have erasedMember :=
          erasedClause_mem_of_positioned_mem
            source taggedSourceMember
        exact List.mem_map.mpr
          ⟨(taggedSource.1.literals, taggedSource.2),
            erasedMember, rfl⟩)

/-- Every positioned implication clause in a fixed ring has distinct
atoms. -/
theorem cycleClausesFor_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    ∀ clause ∈ cycleClausesFor sourcePlacement atom,
      clause.AtomsNodup := by
  intro clause clauseMember
  unfold cycleClausesFor at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, clauseEqual⟩
  subst clause
  exact
    PeriodicEightOccurrenceSplit.cycleClausesFor_atomsNodup
      atom taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)

/-- Collision-free fixed-eight splitting gives atom distinctness in every
positioned output clause. -/
theorem formula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    (collisionFree :
      occurrencePorts.CollisionFree source.erase) :
    (formula source sourcePlacement occurrencePorts).AllAtomsNodup := by
  intro clause clauseMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with occurrenceMember | cycleMember
  · exact occurrenceClauses_allAtomsNodup
      source occurrencePorts collisionFree clause occurrenceMember
  · unfold allCycleClauses at cycleMember
    rcases List.mem_flatMap.mp cycleMember with
      ⟨atom, _atomMember, cycleMember⟩
    exact cycleClausesFor_allAtomsNodup
      sourcePlacement atom clause cycleMember

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
