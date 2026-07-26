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
    {Variable : Type*} [DecidableEq Variable]
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

/-- Affine instantiation maps exactly the source occurrence list. -/
@[simp]
theorem embeddedVariableOccurrences_instantiateFormula
    {Source Target : Type*}
    (variableMap : Source → Target)
    (origin : Cell) (scale : Int)
    (formula : List (EmbeddedClause Source)) :
    embeddedVariableOccurrences
        (instantiateFormula variableMap origin scale formula) =
      (embeddedVariableOccurrences formula).map variableMap := by
  unfold instantiateFormula
  simpa [EmbeddedClause.rename, EmbeddedClause.place,
    EmbeddedClause.map, Function.comp_def] using
      embeddedVariableOccurrences_map variableMap
        (fun position =>
          Cell.add origin (Cell.scale scale position))
        formula

/-- Concatenating formulas concatenates their occurrence lists. -/
@[simp]
theorem embeddedVariableOccurrences_append
    {Variable : Type*}
    (first second : List (EmbeddedClause Variable)) :
    embeddedVariableOccurrences (first ++ second) =
      embeddedVariableOccurrences first ++
        embeddedVariableOccurrences second := by
  simp [embeddedVariableOccurrences, List.flatMap_append]

/-- Flattening a family of formulas flattens the corresponding family of
occurrence lists. -/
@[simp]
theorem embeddedVariableOccurrences_flatMap
    {Site Variable : Type*}
    (sites : List Site)
    (formulaAt : Site → List (EmbeddedClause Variable)) :
    embeddedVariableOccurrences (sites.flatMap formulaAt) =
      sites.flatMap fun site =>
        embeddedVariableOccurrences (formulaAt site) := by
  induction sites with
  | nil => rfl
  | cons site sites induction =>
      simp [embeddedVariableOccurrences_append, induction]

/-- Bounds for two formula components add under concatenation. -/
theorem formulaOccurrencesAtMost_append
    {Variable : Type*} [DecidableEq Variable]
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

/-- In a noduplicated site family, a site-scoped variable occurs no more
often than its unscoped variable in one member formula. -/
theorem scopedOccurrences_count_le
    {Site Variable : Type*}
    [DecidableEq Site] [DecidableEq Variable]
    (sites : List Site) (values : List Variable)
    (sitesNodup : sites.Nodup)
    (target : Site × Variable) :
    (sites.flatMap fun site =>
      values.map fun atom => (site, atom)).count target ≤
        values.count target.2 := by
  induction sites with
  | nil =>
      simp
  | cons site sites induction =>
      have nodupParts := List.nodup_cons.mp sitesNodup
      rw [List.flatMap_cons, List.count_append]
      by_cases sameSite : site = target.1
      · subst site
        have tailMissing :
            target ∉
              (sites.flatMap fun otherSite =>
                values.map fun atom =>
                  (otherSite, atom)) := by
          intro targetMember
          rcases List.mem_flatMap.mp targetMember with
            ⟨otherSite, otherSiteMember, targetMember⟩
          rcases List.mem_map.mp targetMember with
            ⟨atom, _atomMember, targetEqual⟩
          have otherSiteEqual :
              otherSite = target.1 :=
            congrArg Prod.fst targetEqual
          exact nodupParts.1
            (otherSiteEqual ▸ otherSiteMember)
        rw [List.count_map_of_injective values
          (fun atom => (target.1, atom))
          (fun first second equal =>
            congrArg Prod.snd equal)
          target.2]
        rw [List.count_eq_zero_of_not_mem tailMissing]
        simp
      · have headMissing :
            target ∉ values.map fun atom => (site, atom) := by
          intro targetMember
          rcases List.mem_map.mp targetMember with
            ⟨atom, _atomMember, targetEqual⟩
          exact sameSite
            (congrArg Prod.fst targetEqual)
        rw [List.count_eq_zero_of_not_mem headMissing,
          zero_add]
        exact induction nodupParts.2

/-- A noduplicated family of identical finite gadgets preserves the member
occurrence bound whenever the site-scoped variable maps are jointly
injective. -/
theorem instantiateFamily_occurrencesAtMost_of_jointly_injective
    {Site Source Target : Type*}
    [DecidableEq Site] [DecidableEq Source] [DecidableEq Target]
    (bound : Nat)
    (sites : List Site)
    (variableMap : Site → Source → Target)
    (origin : Site → Cell) (scale : Int)
    (formula : List (EmbeddedClause Source))
    (sitesNodup : sites.Nodup)
    (jointlyInjective :
      Function.Injective
        (fun pair : Site × Source =>
          variableMap pair.1 pair.2))
    (sourceOccurrences :
      FormulaOccurrencesAtMost bound formula) :
    FormulaOccurrencesAtMost bound
      (sites.flatMap fun site =>
        instantiateFormula (variableMap site)
          (origin site) scale formula) := by
  intro target
  let scopedOccurrences :=
    sites.flatMap fun site =>
      (embeddedVariableOccurrences formula).map fun atom =>
        (site, atom)
  let combinedMap : Site × Source → Target :=
    fun pair => variableMap pair.1 pair.2
  have occurrenceList :
      embeddedVariableOccurrences
          (sites.flatMap fun site =>
            instantiateFormula (variableMap site)
              (origin site) scale formula) =
        scopedOccurrences.map combinedMap := by
    rw [embeddedVariableOccurrences_flatMap]
    simp only [embeddedVariableOccurrences_instantiateFormula]
    simp [scopedOccurrences, combinedMap,
      List.map_flatMap, List.map_map, Function.comp_def]
  rw [occurrenceList]
  by_cases targetMember : target ∈ scopedOccurrences.map combinedMap
  · rcases List.mem_map.mp targetMember with
      ⟨source, _sourceMember, targetEqual⟩
    subst target
    rw [List.count_map_of_injective
      scopedOccurrences combinedMap jointlyInjective source]
    exact
      (scopedOccurrences_count_le
        sites (embeddedVariableOccurrences formula)
        sitesNodup source).trans
          (sourceOccurrences source.2)
  · rw [List.count_eq_zero_of_not_mem targetMember]
    exact Nat.zero_le _

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

/-- Endpoint variables of an equality-link family, counting each end of
each link once. -/
def equalityLinkEndpoints {Variable : Type*}
    (links : List (EqualityLink Variable)) : List Variable :=
  links.flatMap fun link => [link.first, link.second]

/-- Equality encoding uses each link endpoint in both implication clauses. -/
theorem equalityFamily_occurrence_count
    {Variable : Type*} [DecidableEq Variable]
    (links : List (EqualityLink Variable))
    (atom : Variable) :
    (embeddedVariableOccurrences
      (equalityFamily links)).count atom =
        2 * (equalityLinkEndpoints links).count atom := by
  have occurrences :
      embeddedVariableOccurrences (equalityFamily links) =
        links.flatMap fun link =>
          [link.first, link.second,
            link.first, link.second] := by
    unfold equalityFamily
    rw [embeddedVariableOccurrences_flatMap]
    apply List.flatMap_congr
    intro link _linkMember
    simp [equalityInstance,
      embeddedVariableOccurrences]
  rw [occurrences]
  clear occurrences
  unfold equalityLinkEndpoints
  induction links with
  | nil =>
      simp
  | cons link links induction =>
      simp only [List.flatMap_cons,
        List.count_append,
        List.count_cons, List.count_nil]
      rw [induction]
      by_cases firstEqual : link.first = atom <;>
        by_cases secondEqual : link.second = atom <;>
          simp [firstEqual, secondEqual] <;>
          omega

/-- If every variable is incident to at most `degree` equality links, the
two-clause encoding contributes at most twice that many occurrences. -/
theorem equalityFamily_occurrencesAtMost
    {Variable : Type*} [DecidableEq Variable]
    (links : List (EqualityLink Variable))
    (degree bound : Nat)
    (boundEqual : bound = 2 * degree)
    (endpointDegree :
      ∀ atom,
        (equalityLinkEndpoints links).count atom ≤ degree) :
    FormulaOccurrencesAtMost bound
      (equalityFamily links) := by
  subst bound
  intro atom
  rw [equalityFamily_occurrence_count]
  exact Nat.mul_le_mul_left 2 (endpointDegree atom)

end PlanarThreeSAT
end LeanTrominoes
