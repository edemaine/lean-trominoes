/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitOccurrences
import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences

/-!
# Degree-three split variables come from source occurrences

Every implication-ring vertex has at most two occurrences in the cycle
suffix.  Therefore a variable that reaches the third occurrence slot must
also occur in the copied-source prefix.  Such prefix variables are precisely
the eight selected source-port copies; in particular, the degree-two
separator can never reach the third slot.

This is the structural classification needed before transporting the local
Figure 7 occurrence-order certificate to the full periodic formula.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- Counts computed by two equality-correct Boolean equality procedures
coincide. -/
private theorem count_eq_of_beq_iff_eq {α : Type*}
    (first second : BEq α)
    (firstLawful : ∀ a b : α,
      @BEq.beq α first a b = true ↔ a = b)
    (secondLawful : ∀ a b : α,
      @BEq.beq α second a b = true ↔ a = b)
    (value : α) (values : List α) :
    @List.count α first value values =
      @List.count α second value values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.count_cons]
      have beqEq :
          @BEq.beq α first head value =
            @BEq.beq α second head value := by
        apply Bool.eq_iff_iff.mpr
        exact (firstLawful head value).trans
          (secondLawful head value).symm
      rw [beqEq, induction]

/-- Filtering to one mapped value has the expected multiplicity. -/
private theorem filter_length_eq_count_map
    {α β : Type*} [DecidableEq β]
    (function : α → β) (value : β) (values : List α) :
    (values.filter fun item => function item = value).length =
      (values.map function).count value := by
  induction values with
  | nil => rfl
  | cons head rest induction =>
      by_cases same : function head = value
      · simp [same, induction]
      · simp [same, induction]

/-- Clause-major tagged literals beginning at an arbitrary outer presentation
index. -/
def taggedLiteralsFrom {Variable : Type*}
    (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    List
      (PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable) :=
  clauses.zipIdx start |>.flatMap fun taggedClause =>
    taggedClause.1.zipIdx.map fun taggedLiteral =>
      (taggedLiteral.1, taggedClause.2, taggedLiteral.2)

/-- Tagging an appended clause list shifts only the suffix's clause indices. -/
theorem taggedLiteralsFrom_append
    {Variable : Type*}
    (start : Nat)
    (first second : List (PeriodicClause Variable)) :
    taggedLiteralsFrom start (first ++ second) =
      taggedLiteralsFrom start first ++
        taggedLiteralsFrom (start + first.length) second := by
  simp [taggedLiteralsFrom, List.zipIdx_append]

/-- Atom projection forgets the arbitrary starting index and recovers the
ordinary flattened variable-occurrence list. -/
theorem taggedLiteralsFrom_atoms
    {Variable : Type*}
    (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    (taggedLiteralsFrom start clauses).map
        (fun tagged => tagged.1.atom) =
      PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk clauses) := by
  have clauseMap (clause : PeriodicClause Variable) :
      (clause.zipIdx.map fun tagged => tagged.1.atom) =
        clause.map PeriodicLiteral.atom := by
    have mapped :=
      congrArg (List.map PeriodicLiteral.atom)
        (List.zipIdx_map_fst 0 clause)
    simpa only [List.map_map, Function.comp_def] using mapped
  unfold taggedLiteralsFrom
    PeriodicCNF.variableOccurrences
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def,
    clauseMap]
  exact
    PeriodicCNF.zipIdx_flatMap_fst
      (fun clause =>
        clause.map PeriodicLiteral.atom)
      clauses start

/-- Occurrences of one split variable in the copied-source prefix. -/
def copiedSourceOccurrencesOf
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable) :
    List
      (PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (ThreeOccurrenceVariable Variable)) :=
  PeriodicOneInThreeToThreeDM.occurrencesOf
    (PeriodicCNF.mk
      (occurrenceClauses source occurrencePorts))
    output

/-- Occurrences of one split variable in the implication-cycle suffix, with
their clause indices shifted to the full formula presentation. -/
def cycleOccurrencesOf
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable) :
    List
      (PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (ThreeOccurrenceVariable Variable)) :=
  (taggedLiteralsFrom
      (occurrenceClauses source occurrencePorts).length
      (allCycleClauses source)).filter
    (fun tagged => tagged.1.atom = output)

/-- The occurrence list of the full split formula is the copied-source list
followed by the shifted cycle list. -/
theorem occurrencesOf_formula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable) :
    PeriodicOneInThreeToThreeDM.occurrencesOf
        (formula source occurrencePorts) output =
      copiedSourceOccurrencesOf source occurrencePorts output ++
        cycleOccurrencesOf source occurrencePorts output := by
  unfold PeriodicOneInThreeToThreeDM.occurrencesOf
  rw [show
    PeriodicThreeSATThree.taggedLiterals
        (formula source occurrencePorts) =
      taggedLiteralsFrom 0
        (occurrenceClauses source occurrencePorts ++
          allCycleClauses source) by
      rfl]
  rw [taggedLiteralsFrom_append, List.filter_append]
  rw [show
    taggedLiteralsFrom 0
        (occurrenceClauses source occurrencePorts) =
      PeriodicThreeSATThree.taggedLiterals
        (PeriodicCNF.mk
          (occurrenceClauses source occurrencePorts)) by
      rfl]
  simp [copiedSourceOccurrencesOf,
    cycleOccurrencesOf,
    PeriodicOneInThreeToThreeDM.occurrencesOf]

/-- The shifted cycle occurrence list has the ordinary cycle occurrence
count as its length. -/
theorem cycleOccurrencesOf_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable) :
    (cycleOccurrencesOf source occurrencePorts output).length =
      @List.count (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq output
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk (allCycleClauses source))) := by
  unfold cycleOccurrencesOf
  rw [filter_length_eq_count_map
      (function := fun tagged :
        PeriodicOneInThreeToThreeDM.TaggedOccurrence
          (ThreeOccurrenceVariable Variable) =>
          tagged.1.atom)
      (value := output)]
  rw [taggedLiteralsFrom_atoms]

/-- Any split variable reaching the third occurrence slot is the selected
port copy of a genuine tagged source occurrence. -/
theorem exists_selected_source_of_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (ThreeOccurrenceVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source occurrencePorts)
          output .third = some tagged) :
    ∃ sourceOccurrence,
      sourceOccurrence ∈ taggedLiterals source ∧
        output =
          copy sourceOccurrence.1.atom
            (occurrencePorts.port
              sourceOccurrence.2.1 sourceOccurrence.2.2) := by
  have threeLe :=
    PeriodicOneInThreeToThreeDM.three_le_variableOccurrences_count_of_occurrenceAt_third
      (formula source occurrencePorts) output tagged lookup
  have cycleLe :=
    allCycleClauses_count_le_two source output
  have countEq :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq output
          (PeriodicCNF.variableOccurrences
            (formula source occurrencePorts)) =
        @List.count (ThreeOccurrenceVariable Variable)
          instBEqProd output
          (PeriodicCNF.variableOccurrences
            (formula source occurrencePorts)) := by
    apply count_eq_of_beq_iff_eq
    · intro first second
      exact
        @beq_iff_eq _ instBEqOfDecidableEq
          inferInstance first second
    · intro first second
      exact
        @beq_iff_eq _ instBEqProd
          inferInstance first second
  rw [countEq] at threeLe
  have sourcePositive :
      0 <
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk
            (occurrenceClauses
              source occurrencePorts))).count output := by
    change
      3 ≤
        (PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk
            (occurrenceClauses source occurrencePorts ++
              allCycleClauses source))).count output
      at threeLe
    rw [PeriodicThreeSATThree.variableOccurrences_append,
      List.count_append] at threeLe
    omega
  have sourceMember :
      output ∈
        PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk
            (occurrenceClauses source occurrencePorts)) :=
    List.count_pos_iff.mp sourcePositive
  rw [occurrenceClauses_variableOccurrences] at sourceMember
  rcases List.mem_map.mp sourceMember with
    ⟨sourceOccurrence, sourceOccurrenceMember,
      sourceOccurrenceEqual⟩
  exact
    ⟨sourceOccurrence, sourceOccurrenceMember,
      sourceOccurrenceEqual.symm⟩

/-- In particular, a degree-three split variable is one of the eight real
source-port copies, never the separator. -/
theorem exists_port_of_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (ThreeOccurrenceVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source occurrencePorts)
          output .third = some tagged) :
    ∃ atom port, output = copy atom port := by
  rcases exists_selected_source_of_occurrenceAt_third
      source occurrencePorts output tagged lookup with
    ⟨sourceOccurrence, _sourceOccurrenceMember, outputEqual⟩
  exact
    ⟨sourceOccurrence.1.atom,
      occurrencePorts.port
        sourceOccurrence.2.1 sourceOccurrence.2.2,
      outputEqual⟩

/-- Under collision freedom, successful first/second/third lookups split
exactly as intended: the first occurrence is the unique copied-source
incidence and the latter two are precisely the cycle incidences in their
presentation order. -/
theorem occurrenceAt_three_decomposition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (collisionFree : occurrencePorts.CollisionFree source)
    (output : ThreeOccurrenceVariable Variable)
    (first second third :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (ThreeOccurrenceVariable Variable))
    (firstLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source occurrencePorts)
          output .first = some first)
    (secondLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source occurrencePorts)
          output .second = some second)
    (thirdLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source occurrencePorts)
          output .third = some third) :
    copiedSourceOccurrencesOf source occurrencePorts output =
        [first] ∧
      cycleOccurrencesOf source occurrencePorts output =
        [second, third] := by
  let sourceOccurrences :=
    copiedSourceOccurrencesOf source occurrencePorts output
  let cycleOccurrences :=
    cycleOccurrencesOf source occurrencePorts output
  have sourceCountEq :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq output
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk
              (occurrenceClauses source occurrencePorts))) =
        @List.count (ThreeOccurrenceVariable Variable)
          instBEqProd output
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk
              (occurrenceClauses source occurrencePorts))) := by
    apply count_eq_of_beq_iff_eq
    · intro left right
      exact
        @beq_iff_eq _ instBEqOfDecidableEq
          inferInstance left right
    · intro left right
      exact
        @beq_iff_eq _ instBEqProd
          inferInstance left right
  have cycleCountEq :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq output
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (allCycleClauses source))) =
        @List.count (ThreeOccurrenceVariable Variable)
          instBEqProd output
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (allCycleClauses source))) := by
    apply count_eq_of_beq_iff_eq
    · intro left right
      exact
        @beq_iff_eq _ instBEqOfDecidableEq
          inferInstance left right
    · intro left right
      exact
        @beq_iff_eq _ instBEqProd
          inferInstance left right
  have sourceLengthLe : sourceOccurrences.length ≤ 1 := by
    rw [show
      sourceOccurrences.length =
        @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq output
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk
              (occurrenceClauses source occurrencePorts))) by
        exact
          PeriodicOneInThreeToThreeDM.occurrencesOf_length
            (PeriodicCNF.mk
              (occurrenceClauses source occurrencePorts))
            output]
    rw [sourceCountEq]
    exact occurrenceClauses_count_le_one
      source occurrencePorts collisionFree output
  have cycleLengthLe : cycleOccurrences.length ≤ 2 := by
    rw [show
      cycleOccurrences.length =
        @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq output
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (allCycleClauses source))) by
        exact cycleOccurrencesOf_length
          source occurrencePorts output]
    rw [cycleCountEq]
    exact allCycleClauses_count_le_two source output
  have totalLengthGe :
      3 ≤
        (PeriodicOneInThreeToThreeDM.occurrencesOf
          (formula source occurrencePorts) output).length := by
    rw [PeriodicOneInThreeToThreeDM.occurrenceAt,
      List.getElem?_eq_some_iff] at thirdLookup
    rcases thirdLookup with ⟨thirdIndexLt, _thirdEqual⟩
    simp only [
      PeriodicOneInThreeToThreeDM.OccurrenceSlot.index]
      at thirdIndexLt
    omega
  have lengthSum :
      3 ≤ sourceOccurrences.length + cycleOccurrences.length := by
    rw [occurrencesOf_formula] at totalLengthGe
    simpa [sourceOccurrences, cycleOccurrences] using totalLengthGe
  have sourceLength : sourceOccurrences.length = 1 := by
    omega
  have cycleLength : cycleOccurrences.length = 2 := by
    omega
  rcases List.length_eq_one_iff.mp sourceLength with
    ⟨sourceOccurrence, sourceOccurrencesEq⟩
  rcases List.length_eq_two.mp cycleLength with
    ⟨firstCycle, secondCycle, cycleOccurrencesEq⟩
  change
    (PeriodicOneInThreeToThreeDM.occurrencesOf
      (formula source occurrencePorts) output)[0]? =
        some first at firstLookup
  change
    (PeriodicOneInThreeToThreeDM.occurrencesOf
      (formula source occurrencePorts) output)[1]? =
        some second at secondLookup
  change
    (PeriodicOneInThreeToThreeDM.occurrencesOf
      (formula source occurrencePorts) output)[2]? =
        some third at thirdLookup
  rw [occurrencesOf_formula,
    show copiedSourceOccurrencesOf
        source occurrencePorts output = [sourceOccurrence] by
      simpa [sourceOccurrences] using sourceOccurrencesEq,
    show cycleOccurrencesOf
        source occurrencePorts output =
          [firstCycle, secondCycle] by
      simpa [cycleOccurrences] using cycleOccurrencesEq]
    at firstLookup secondLookup thirdLookup
  change some sourceOccurrence = some first at firstLookup
  change some firstCycle = some second at secondLookup
  change some secondCycle = some third at thirdLookup
  have sourceOccurrenceEq : sourceOccurrence = first :=
    Option.some.inj firstLookup
  have firstCycleEq : firstCycle = second :=
    Option.some.inj secondLookup
  have secondCycleEq : secondCycle = third :=
    Option.some.inj thirdLookup
  subst sourceOccurrence
  subst firstCycle
  subst secondCycle
  exact
    ⟨by simpa [sourceOccurrences] using sourceOccurrencesEq,
      by simpa [cycleOccurrences] using cycleOccurrencesEq⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
