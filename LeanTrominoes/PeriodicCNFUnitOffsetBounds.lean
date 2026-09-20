/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedPeriodicCNFLocality
import LeanTrominoes.PositionedPeriodicCNFVariableGauge
import LeanTrominoes.PeriodicEightOccurrenceSplit
import LeanTrominoes.PeriodicOneInThreeNoUnits

/-! # Unit-radius literal offsets and locality under partial offset resets -/
namespace LeanTrominoes

def Cell.IsUnitOffset (c : Cell) : Prop := c.1.natAbs+c.2.natAbs ≤ 1

def PeriodicCNF.HasUnitOffsets {V : Type*} (f : PeriodicCNF V) : Prop :=
  ∀ clause ∈ f.clauses, ∀ literal ∈ clause, literal.offset.IsUnitOffset

theorem PeriodicClause.anchorNormalize_hasUnitOffsets {V : Type*}
    {clause : PeriodicClause V} (locality : clause.IsLocal) :
    ∀ literal ∈ clause.anchorNormalize, literal.offset.IsUnitOffset := by
  cases clause with
  | nil => simp [anchorNormalize]
  | cons first rest =>
      intro literal member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      have bound := locality original originalMember first (by simp)
      simpa [Cell.IsUnitOffset,PeriodicClause.offsetDistance,PeriodicLiteral.anchorNormalize,
        PeriodicCNF.clauseAnchor,Cell.sub] using bound

theorem PeriodicCNF.anchorNormalize_hasUnitOffsets {V : Type*}
    {f : PeriodicCNF V} (locality : f.IsLocal) : f.anchorNormalize.HasUnitOffsets := by
  intro clause member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact PeriodicClause.anchorNormalize_hasUnitOffsets (locality original originalMember)

theorem PeriodicClause.variableGauge_isLocal_of_reset {V : Type*}
    {clause : PeriodicClause V} (gauge : V → Cell) (locality : clause.IsLocal)
    (bounds : ∀ literal ∈ clause, literal.offset.IsUnitOffset)
    (reset : ∀ literal ∈ clause, (literal.variableGauge gauge).offset=literal.offset ∨
      (literal.variableGauge gauge).offset=(0,0)) :
    (clause.variableGauge gauge).IsLocal := by
  intro a ha b hb
  obtain ⟨originalA,memberA,rfl⟩ := List.mem_map.mp ha
  obtain ⟨originalB,memberB,rfl⟩ := List.mem_map.mp hb
  have ba := bounds originalA memberA
  have bb := bounds originalB memberB
  have near := locality originalA memberA originalB memberB
  rcases reset originalA memberA with sameA | zeroA <;>
    rcases reset originalB memberB with sameB | zeroB <;>
    simp_all [PeriodicClause.offsetDistance,Cell.IsUnitOffset,Int.natAbs_neg]

theorem PeriodicOneInThree.formula_hasUnitOffsets {V : Type*} {source : PeriodicCNF V}
    (bounds : source.HasUnitOffsets) : (formula source).HasUnitOffsets := by
  intro clause member literal literalMember
  simp only [formula,List.mem_flatMap] at member
  obtain ⟨tagged,taggedMember,clauseMember⟩ := member
  have sourceBounds := bounds tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)
  rcases clauseClauses_supported tagged.2 tagged.1 clause clauseMember literal literalMember with
    ⟨original,originalMember,offsetEq⟩ | offsetEq
  · rw [offsetEq]
    exact sourceBounds original originalMember
  · rw [offsetEq]
    cases h : tagged.1 with
    | nil => simp [anchor,Cell.IsUnitOffset]
    | cons first rest =>
        simpa [anchor,h] using sourceBounds first (by simp [h])

namespace PeriodicOneInThreeNoUnits

/-- Unit elimination preserves the unit-radius bound on literal offsets. -/
theorem clauseClauses_haveUnitOffsets
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (bounds : ∀ literal ∈ source, literal.offset.IsUnitOffset) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      ∀ literal ∈ generated, literal.offset.IsUnitOffset := by
  cases source with
  | nil =>
      intro generated generatedMember literal literalMember
      simp only [clauseClauses, List.mem_cons, List.not_mem_nil, or_false]
        at generatedMember
      rcases generatedMember with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false]
          at literalMember <;>
        rcases literalMember with rfl | rfl <;> simp [auxiliary,PeriodicOneInThree.anchor,Cell.IsUnitOffset]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstBound := bounds first (by simp)
          intro generated generatedMember literal literalMember
          simp only [clauseClauses, List.mem_cons, List.not_mem_nil, or_false]
            at generatedMember
          rcases generatedMember with rfl | rfl
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
              at literalMember
            rcases literalMember with rfl | rfl | rfl <;>
              simpa [PeriodicOneInThree.negate, liftLiteral, auxiliary,
                PeriodicOneInThree.anchor] using firstBound
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
              at literalMember
            rcases literalMember with rfl | rfl <;>
              simpa [auxiliary, PeriodicOneInThree.anchor] using firstBound
      | cons second rest =>
          intro generated generatedMember literal literalMember
          simp only [clauseClauses, List.mem_singleton] at generatedMember
          subst generated
          simp only [List.mem_map] at literalMember
          obtain ⟨sourceLiteral, sourceLiteralMember, rfl⟩ := literalMember
          simpa [liftLiteral] using
            bounds sourceLiteral sourceLiteralMember

/-- Exact-one unit elimination preserves unit-radius offsets throughout a formula. -/
theorem formula_hasUnitOffsets
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (bounds : source.HasUnitOffsets) :
    (formula source).HasUnitOffsets := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  obtain ⟨taggedClause, taggedClauseMember, clauseMember⟩ := clauseMember
  exact clauseClauses_haveUnitOffsets taggedClause.2 taggedClause.1
    (bounds taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    clause clauseMember literal literalMember

end PeriodicOneInThreeNoUnits

namespace PeriodicEightOccurrenceSplit

theorem formula_hasUnitOffsets {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (ports : OccurrencePorts) (bounds : source.HasUnitOffsets) :
    (formula source ports).HasUnitOffsets := by
  intro clause clauseMember literal literalMember
  simp only [formula,List.mem_append] at clauseMember
  rcases clauseMember with occurrenceMember | cycleMember
  · simp only [occurrenceClauses,List.mem_map] at occurrenceMember
    obtain ⟨tagged,taggedMember,rfl⟩ := occurrenceMember
    simp only [occurrenceClause,List.mem_map] at literalMember
    obtain ⟨taggedLiteral,taggedLiteralMember,rfl⟩ := literalMember
    exact bounds tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)
      taggedLiteral.1 (List.fst_mem_of_mem_zipIdx taggedLiteralMember)
  · have cycleBound (first current : ThreeOccurrenceVariable V)
        (rest : List (ThreeOccurrenceVariable V)) :
        ∀ c ∈ PeriodicThreeSATThree.cycleFrom first current rest,
          ∀ l ∈ c, l.offset.IsUnitOffset := by
      induction rest generalizing current with
      | nil => simp [PeriodicThreeSATThree.cycleFrom,PeriodicThreeSATThree.implicationClause,Cell.IsUnitOffset]
      | cons next rest ih =>
          intro c hc
          simp only [PeriodicThreeSATThree.cycleFrom,List.mem_cons] at hc
          rcases hc with rfl | hc
          · simp [PeriodicThreeSATThree.implicationClause,Cell.IsUnitOffset]
          · exact ih next c hc
    simp only [allCycleClauses,List.mem_flatMap] at cycleMember
    obtain ⟨atom,_,member⟩ := cycleMember
    change clause ∈ PeriodicThreeSATThree.cycleClauses (copies atom) at member
    cases h : copies atom with
    | nil => simp [h,PeriodicThreeSATThree.cycleClauses] at member
    | cons first rest =>
        exact cycleBound first first rest clause (by simpa [h,PeriodicThreeSATThree.cycleClauses] using member)
          literal literalMember

end PeriodicEightOccurrenceSplit

namespace PositionedPeriodicCNF

theorem orderClausesByRouteDirection_hasUnitOffsets {V : Type*}
    (source : PositionedPeriodicCNF V) (routes : IncidenceRoutes)
    (bounds : source.erase.HasUnitOffsets) :
    (orderClausesByRouteDirection source routes).erase.HasUnitOffsets := by
  intro c hc literal literalMember
  change c ∈ ((orderClausesByRouteDirection source routes).clauses.map PositionedPeriodicClause.literals) at hc
  obtain ⟨positioned,positionedMember,rfl⟩ := List.mem_map.mp hc
  change positioned ∈ source.clauses.zipIdx.map _ at positionedMember
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp positionedMember
  exact bounds tagged.1.literals
    (List.mem_map.mpr ⟨tagged.1,List.fst_mem_of_mem_zipIdx taggedMember,rfl⟩)
    literal ((orderClauseByRouteDirection_literals_perm routes tagged.2 tagged.1).mem_iff.mp literalMember)

theorem variableGauge_isLocal_of_reset {V : Type*} (source : PositionedPeriodicCNF V)
    (gauge : V → Cell) (locality : source.erase.IsLocal) (bounds : source.erase.HasUnitOffsets)
    (reset : ∀ clause index, (clause,index) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex, (literal,literalIndex) ∈ clause.literals.zipIdx →
        (literal.variableGauge gauge).offset=literal.offset ∨ (literal.variableGauge gauge).offset=(0,0)) :
    (source.variableGauge gauge).erase.IsLocal := by
  rw [erase_variableGauge]
  intro clause member
  simp only [PeriodicCNF.variableGauge,erase] at member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨positioned,positionedMember,rfl⟩ := List.mem_map.mp originalMember
  have erasedMem : positioned.literals ∈ source.erase.clauses :=
    List.mem_map.mpr ⟨positioned,positionedMember,rfl⟩
  apply PeriodicClause.variableGauge_isLocal_of_reset gauge (locality _ erasedMem) (bounds _ erasedMem)
  intro literal literalMember
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp positionedMember
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp literalMember
  exact reset positioned i (List.mem_zipIdx_iff_getElem?.mpr hi) literal j
    (List.mem_zipIdx_iff_getElem?.mpr hj)

theorem orderClausesByRouteDirection_variableGauge_isLocal {V : Type*}
    (source : PositionedPeriodicCNF V) (routes : IncidenceRoutes) (gauge : V → Cell)
    (locality : (source.variableGauge gauge).erase.IsLocal) :
    ((orderClausesByRouteDirection source routes).variableGauge gauge).erase.IsLocal := by
  rw [erase_variableGauge] at locality ⊢
  intro c hc
  simp only [PeriodicCNF.variableGauge,erase] at hc
  obtain ⟨literals,literalsMember,rfl⟩ := List.mem_map.mp hc
  obtain ⟨positioned,positionedMember,rfl⟩ := List.mem_map.mp literalsMember
  change positioned ∈ source.clauses.zipIdx.map _ at positionedMember
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp positionedMember
  have originalMem : tagged.1.literals.variableGauge gauge ∈ (source.erase.variableGauge gauge).clauses :=
    List.mem_map.mpr ⟨tagged.1.literals,
      List.mem_map.mpr ⟨tagged.1,List.fst_mem_of_mem_zipIdx taggedMember,rfl⟩,rfl⟩
  have perm := (orderClauseByRouteDirection_literals_perm routes tagged.2 tagged.1).map
    (PeriodicLiteral.variableGauge gauge)
  intro a ha b hb
  exact locality _ originalMem a (perm.mem_iff.mp ha) b (perm.mem_iff.mp hb)

end PositionedPeriodicCNF

end LeanTrominoes
