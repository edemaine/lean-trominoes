/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCNFZeroOffsets
import LeanTrominoes.PositionedPeriodicCNFVariableGauge
import LeanTrominoes.PeriodicEightOccurrenceSplit
import LeanTrominoes.PeriodicOneInThreeOneDimensional
import LeanTrominoes.PeriodicOneInThreeNoUnitsOneDimensional
import LeanTrominoes.PositionedPeriodicCNFOneDimensionalOrdering

/-! # Finite offsets survive occurrence splitting and exact-one conversion -/
namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- A fixed-port occurrence clause inherits zero offsets from its
source clause. -/
theorem occurrenceClause_zeroOffsets
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (zero : ∀ literal ∈ source, literal.offset = (0,0)) :
    ∀ literal ∈ occurrenceClause occurrencePorts clauseIndex source,
      literal.offset = (0,0) := by
  intro literal literalMember
  simp only [occurrenceClause, List.mem_map] at literalMember
  obtain ⟨tagged, taggedMember, rfl⟩ := literalMember
  simpa [occurrenceLiteral] using
    zero tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)

/-- Every implication clause in one fixed ring has zero offsets. -/
theorem cycleClausesFor_zeroOffsets
    {Variable : Type*} (atom : Variable) :
    ∀ clause ∈ cycleClausesFor atom,
      ∀ literal ∈ clause, literal.offset = (0,0) := by
  have fromZero (first current : ThreeOccurrenceVariable Variable)
      (rest : List (ThreeOccurrenceVariable Variable)) :
      ∀ clause∈PeriodicThreeSATThree.cycleFrom first current rest,
        ∀ literal∈clause,literal.offset=(0,0) := by
    induction rest generalizing current with
    | nil => simp [PeriodicThreeSATThree.cycleFrom,PeriodicThreeSATThree.implicationClause]
    | cons next rest ih =>
      intro clause member literal hl
      rcases List.mem_cons.mp member with rfl|member
      · simp only [PeriodicThreeSATThree.implicationClause,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|rfl <;> rfl
      · exact ih next clause member literal hl
  cases h : copies atom with
  | nil => simp [cycleClausesFor,h,PeriodicThreeSATThree.cycleClauses]
  | cons first rest =>
    simpa only [cycleClausesFor,h,PeriodicThreeSATThree.cycleClauses] using fromZero first first rest

/-- All fixed implication rings have zero offsets. -/
theorem allCycleClauses_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ∀ clause ∈ allCycleClauses source,
      ∀ literal ∈ clause, literal.offset = (0,0) := by
  intro clause clauseMember literal literalMember
  simp only [allCycleClauses, List.mem_flatMap] at clauseMember
  obtain ⟨atom, _atomMember, clauseMember⟩ := clauseMember
  exact cycleClausesFor_zeroOffsets atom
    clause clauseMember literal literalMember

/-- Fixed-eight occurrence splitting preserves zero offsets for every
compass-port assignment. -/
theorem formula_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (occurrencePorts : OccurrencePorts)
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (formula source occurrencePorts) := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with occurrenceMember | cycleMember
  · simp only [occurrenceClauses, List.mem_map] at occurrenceMember
    obtain ⟨taggedClause, taggedClauseMember, rfl⟩ := occurrenceMember
    exact occurrenceClause_zeroOffsets occurrencePorts
      taggedClause.2 taggedClause.1
      (zero taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember))
      literal literalMember
  · exact allCycleClauses_zeroOffsets source
      clause cycleMember literal literalMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicOneInThree

/-- A Figure 9 literal supported by a zero source clause has zero
offset. -/
theorem Supported.offset_eq_zero
    {Variable : Type*}
    {source : PeriodicClause Variable}
    (zero : ∀ literal ∈ source, literal.offset = (0,0))
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    (supported : Supported source literal) :
    literal.offset = (0,0) := by
  rcases supported with ⟨original, originalMember, offsetEqual⟩ |
      offsetEqual
  · simpa [offsetEqual] using zero original originalMember
  · cases source with
    | nil => simpa [anchor] using offsetEqual
    | cons first rest =>
        have firstVertical := zero first (by simp)
        simpa [anchor, offsetEqual] using firstVertical

/-- Figure 9's periodic exact-one conversion preserves the
zero-offset fragment. -/
theorem formula_zeroOffsets
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (formula source) := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  obtain ⟨taggedClause, taggedClauseMember, clauseMember⟩ := clauseMember
  exact Supported.offset_eq_zero
    (zero taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    (clauseClauses_supported taggedClause.2 taggedClause.1
      clause clauseMember literal literalMember)

end PeriodicOneInThree
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

/-- Every clause generated from one zeroly supported exact-one clause
has only zero offsets. -/
theorem clauseClauses_zeroOffsets
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (zero : ∀ literal ∈ source, literal.offset = (0,0)) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      ∀ literal ∈ generated, literal.offset = (0,0) := by
  cases source with
  | nil =>
      intro generated generatedMember literal literalMember
      simp only [clauseClauses, List.mem_cons, List.not_mem_nil, or_false]
        at generatedMember
      rcases generatedMember with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false]
          at literalMember <;>
        rcases literalMember with rfl | rfl <;> rfl
  | cons first rest =>
      cases rest with
      | nil =>
          have firstVertical := zero first (by simp)
          intro generated generatedMember literal literalMember
          simp only [clauseClauses, List.mem_cons, List.not_mem_nil, or_false]
            at generatedMember
          rcases generatedMember with rfl | rfl
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
              at literalMember
            rcases literalMember with rfl | rfl | rfl <;>
              simpa [PeriodicOneInThree.negate, liftLiteral, auxiliary,
                PeriodicOneInThree.anchor] using firstVertical
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
              at literalMember
            rcases literalMember with rfl | rfl <;>
              simpa [auxiliary, PeriodicOneInThree.anchor] using firstVertical
      | cons second rest =>
          intro generated generatedMember literal literalMember
          simp only [clauseClauses, List.mem_singleton] at generatedMember
          subst generated
          simp only [List.mem_map] at literalMember
          obtain ⟨sourceLiteral, sourceLiteralMember, rfl⟩ := literalMember
          simpa [liftLiteral] using
            zero sourceLiteral sourceLiteralMember

/-- Exact-one unit elimination preserves zero offsets. -/
theorem formula_zeroOffsets
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (formula source) := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  obtain ⟨taggedClause, taggedClauseMember, clauseMember⟩ := clauseMember
  exact clauseClauses_zeroOffsets taggedClause.2 taggedClause.1
    (zero taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    clause clauseMember literal literalMember

end PeriodicOneInThreeNoUnits
end LeanTrominoes

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Stable route-direction ordering preserves zero offsets after
positions are erased. -/
theorem orderClausesByRouteDirection_erase_zeroOffsets
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes)
    (zero : FiniteCNF.ZeroOffsets source.erase) :
    FiniteCNF.ZeroOffsets (orderClausesByRouteDirection source routes).erase := by
  intro outputClause outputClauseMember outputLiteral outputLiteralMember
  rw [PositionedPeriodicCNF.erase] at outputClauseMember
  rcases List.mem_map.mp outputClauseMember with
    ⟨outputPositionedClause, outputPositionedClauseMember, rfl⟩
  rw [orderClausesByRouteDirection] at outputPositionedClauseMember
  rcases List.mem_map.mp outputPositionedClauseMember with
    ⟨taggedSourceClause, taggedSourceClauseMember, rfl⟩
  have sourceClauseMember :
      taggedSourceClause.1.literals ∈ source.erase.clauses := by
    change taggedSourceClause.1.literals ∈
      source.clauses.map PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨taggedSourceClause.1,
        List.fst_mem_of_mem_zipIdx taggedSourceClauseMember, rfl⟩
  have sourceLiteralMember :
      outputLiteral ∈ taggedSourceClause.1.literals :=
    (orderClauseByRouteDirection_literals_perm
      routes taggedSourceClause.2 taggedSourceClause.1).mem_iff.mp
        outputLiteralMember
  exact zero taggedSourceClause.1.literals sourceClauseMember
    outputLiteral sourceLiteralMember

end PositionedPeriodicCNF
end LeanTrominoes

namespace LeanTrominoes.FiniteCNF
/-- Adding a zero gauge on occurring variables preserves finite offsets. -/
theorem zeroOffsets_variableGauge {V : Type*} (source : PeriodicCNF V) (gauge : V → Cell)
    (zero : ZeroOffsets source)
    (gaugeZero : ∀ atom∈source.variableOccurrences,gauge atom=(0,0)) :
    ZeroOffsets (source.variableGauge gauge) := by
  intro clause member literal hl
  simp only [PeriodicCNF.variableGauge,List.mem_map] at member
  obtain ⟨original,originalMember,rfl⟩ := member
  simp only [PeriodicClause.variableGauge,List.mem_map] at hl
  obtain ⟨oldLiteral,oldMember,rfl⟩ := hl
  have atomMember : oldLiteral.atom∈source.variableOccurrences :=
    List.mem_flatMap.mpr ⟨original,originalMember,List.mem_map.mpr ⟨oldLiteral,oldMember,rfl⟩⟩
  simp [PeriodicLiteral.variableGauge,zero original originalMember oldLiteral oldMember,
    gaugeZero _ atomMember,Cell.add]
end LeanTrominoes.FiniteCNF
