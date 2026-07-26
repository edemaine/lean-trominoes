import LeanTrominoes.PlanarThreeSATWidth
import Mathlib.Data.List.Count

/-!
# Occurrence bounds for finite embedded 3SAT formulas

Positions do not affect how often a variable occurs.  This file provides the
finite counterpart of `PeriodicCNF.OccurrencesAtMost`, together with the
composition rules needed to count the Figure 8 gadgets before
periodicization.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Variables named by all literal occurrences of an embedded formula, in
clause-major order. -/
def embeddedVariableOccurrences {Variable : Type*}
    (formula : List (EmbeddedClause Variable)) : List Variable :=
  formula.flatMap fun clause =>
    clause.literals.map Prod.fst

/-- Every variable occurs at most `bound` times in a finite embedded
presentation. -/
def FormulaOccurrencesAtMost
    {Variable : Type*} [BEq Variable] [LawfulBEq Variable]
    (bound : Nat)
    (formula : List (EmbeddedClause Variable)) : Prop :=
  ∀ atom,
    (embeddedVariableOccurrences formula).count atom ≤ bound

instance {Variable : Type*} [Fintype Variable]
    [DecidableEq Variable]
    (bound : Nat) (formula : List (EmbeddedClause Variable)) :
    Decidable (FormulaOccurrencesAtMost bound formula) := by
  unfold FormulaOccurrencesAtMost
  infer_instance

/-- Mapping clause positions and variables maps the flattened occurrence
list by exactly the same variable map. -/
@[simp]
theorem embeddedVariableOccurrences_map
    {Source Target : Type*}
    (variableMap : Source → Target)
    (positionMap : Cell → Cell)
    (formula : List (EmbeddedClause Source)) :
    embeddedVariableOccurrences
        (formula.map fun clause =>
          clause.map variableMap positionMap) =
      (embeddedVariableOccurrences formula).map variableMap := by
  simp [embeddedVariableOccurrences,
    EmbeddedClause.map, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def]

/-- Concatenating formulas concatenates their occurrence lists. -/
@[simp]
theorem embeddedVariableOccurrences_append
    {Variable : Type*}
    (first second : List (EmbeddedClause Variable)) :
    embeddedVariableOccurrences (first ++ second) =
      embeddedVariableOccurrences first ++
        embeddedVariableOccurrences second := by
  simp [embeddedVariableOccurrences, List.flatMap_append]

/-- Bounds for two formula components add under concatenation. -/
theorem formulaOccurrencesAtMost_append
    {Variable : Type*} [BEq Variable] [LawfulBEq Variable]
    {firstBound secondBound : Nat}
    {first second : List (EmbeddedClause Variable)}
    (firstOccurrences :
      FormulaOccurrencesAtMost firstBound first)
    (secondOccurrences :
      FormulaOccurrencesAtMost secondBound second) :
    FormulaOccurrencesAtMost
      (firstBound + secondBound) (first ++ second) := by
  intro atom
  rw [embeddedVariableOccurrences_append,
    List.count_append]
  exact Nat.add_le_add
    (firstOccurrences atom)
    (secondOccurrences atom)

/-- An injective variable renaming preserves every finite occurrence
bound; changing positions remains irrelevant. -/
theorem formulaOccurrencesAtMost_map_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (bound : Nat)
    (variableMap : Source → Target)
    (positionMap : Cell → Cell)
    (formula : List (EmbeddedClause Source))
    (injective : Function.Injective variableMap)
    (sourceOccurrences :
      FormulaOccurrencesAtMost bound formula) :
    FormulaOccurrencesAtMost bound
      (formula.map fun clause =>
        clause.map variableMap positionMap) := by
  intro target
  rw [embeddedVariableOccurrences_map]
  by_cases targetMember :
      target ∈
        (embeddedVariableOccurrences formula).map variableMap
  · rcases List.mem_map.mp targetMember with
      ⟨source, _sourceMember, targetEqual⟩
    subst target
    rw [List.count_map_of_injective
      (embeddedVariableOccurrences formula)
      variableMap injective source]
    exact sourceOccurrences source
  · rw [List.count_eq_zero_of_not_mem targetMember]
    exact Nat.zero_le _

/-- Injective affine gadget instantiation preserves occurrence bounds. -/
theorem instantiateFormula_occurrencesAtMost_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (bound : Nat)
    (variableMap : Source → Target)
    (origin : Cell) (scale : Int)
    (formula : List (EmbeddedClause Source))
    (injective : Function.Injective variableMap)
    (sourceOccurrences :
      FormulaOccurrencesAtMost bound formula) :
    FormulaOccurrencesAtMost bound
      (instantiateFormula variableMap origin scale formula) := by
  unfold instantiateFormula
  simpa [EmbeddedClause.rename, EmbeddedClause.place,
    EmbeddedClause.map, Function.comp_def] using
    formulaOccurrencesAtMost_map_of_injective
    bound variableMap
      (fun position =>
        Cell.add origin (Cell.scale scale position))
      formula injective sourceOccurrences

/-- Every variable of the fixed Figure 8 crossover occurs at most eight
times. -/
theorem crossoverFormula_occurrencesAtMostEight :
    FormulaOccurrencesAtMost 8 crossoverFormula := by
  native_decide

/-- Every variable of the fixed Figure 8 duplicator occurs at most six
times. -/
theorem duplicatorFormula_occurrencesAtMostSix :
    FormulaOccurrencesAtMost 6 duplicatorFormula := by
  native_decide

/-- One equality link contributes at most four occurrences of any variable,
including the degenerate case where its endpoints coincide. -/
theorem equalityInstance_occurrencesAtMostFour
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (positions : EqualityPositions) :
    FormulaOccurrencesAtMost 4
      (equalityInstance first second positions) := by
  intro atom
  by_cases firstEqual : first = atom <;>
    by_cases secondEqual : second = atom <;>
      simp [embeddedVariableOccurrences,
        equalityInstance, firstEqual, secondEqual]

end PlanarThreeSAT
end LeanTrominoes
