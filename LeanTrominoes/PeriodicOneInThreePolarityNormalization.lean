import LeanTrominoes.PeriodicOneInThreeNoUnits

/-!
# Polarity normalization for the planar 3DM connector order

The variable-to-clause ribbons in the 3DM drawing use the first clause
literal at the fixed-red terminal, the second at the fixed-blue terminal,
and the third at the fixed-green terminal.  The endpoint-clear variable
templates require the corresponding literal polarities `false`, `false`,
and `true`.

This file gives the logical preprocessing needed to impose that convention.
An occurrence that already has the requested polarity is merely embedded.
An occurrence with the opposite polarity is replaced by a fresh variable,
and the binary exact-one clause `[fresh = false, original = false]` forces
the fresh variable to be the complement of the original.  Consequently the
replacement literal has exactly the same truth value as the source literal.
-/

namespace LeanTrominoes

/-- Original variables or a fresh complement variable attached to one
syntactic literal occurrence.  Retaining the source literal makes the
canonical assignment extension independent of the surrounding formula. -/
abbrev PolarityNormalizedVariable (Variable : Type*) :=
  Sum Variable ((Nat × Nat) × PeriodicLiteral Variable)

namespace PeriodicOneInThreePolarityNormalization

/-- Literal polarity requested by the fixed-red, fixed-blue, and fixed-green
clause terminals, respectively. -/
def normalizedPolarity : Nat → Bool
  | 0 | 1 => false
  | _ => true

/-- Embed a source literal without changing its atom, offset, or polarity. -/
def liftLiteral {Variable : Type*} (literal : PeriodicLiteral Variable) :
    PeriodicLiteral (PolarityNormalizedVariable Variable) :=
  ⟨Sum.inl literal.atom, literal.offset, literal.value⟩

/-- The requested-polarity literal of an occurrence-local fresh variable. -/
def complementLiteral {Variable : Type*} (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    PeriodicLiteral (PolarityNormalizedVariable Variable) :=
  ⟨Sum.inr ((clauseIndex, literalIndex), source), source.offset,
    normalizedPolarity literalIndex⟩

/-- Embed a compatible occurrence and replace an incompatible occurrence by
its fresh complement variable. -/
def normalizeLiteral {Variable : Type*} (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    PeriodicLiteral (PolarityNormalizedVariable Variable) :=
  if source.value = normalizedPolarity literalIndex then
    liftLiteral source
  else
    complementLiteral clauseIndex literalIndex source

/-- A false literal of an embedded original variable, used by the binary
complement clause. -/
def originalFalseLiteral {Variable : Type*}
    (source : PeriodicLiteral Variable) :
    PeriodicLiteral (PolarityNormalizedVariable Variable) :=
  ⟨Sum.inl source.atom, source.offset, false⟩

/-- A false literal of an occurrence-local fresh variable. -/
def complementFalseLiteral {Variable : Type*}
    (clauseIndex literalIndex : Nat) (source : PeriodicLiteral Variable) :
    PeriodicLiteral (PolarityNormalizedVariable Variable) :=
  ⟨Sum.inr ((clauseIndex, literalIndex), source), source.offset, false⟩

/-- The binary exact-one clause forcing a fresh variable to complement its
source variable.  The fresh literal comes first so that the later
fresh-variable gauge makes this clause's anchor zero. -/
def complementClause {Variable : Type*} (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    PeriodicClause (PolarityNormalizedVariable Variable) :=
  [complementFalseLiteral clauseIndex literalIndex source,
    originalFalseLiteral source]

/-- Normalize a suffix of literal occurrences, retaining its absolute
starting index. -/
def normalizeClauseFrom {Variable : Type*} (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    PeriodicClause (PolarityNormalizedVariable Variable) :=
  (source.zipIdx literalStart).map fun tagged =>
    normalizeLiteral clauseIndex tagged.2 tagged.1

@[simp]
theorem normalizeClauseFrom_cons {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (literal : PeriodicLiteral Variable)
    (rest : PeriodicClause Variable) :
    normalizeClauseFrom clauseIndex literalStart (literal :: rest) =
      normalizeLiteral clauseIndex literalStart literal ::
        normalizeClauseFrom clauseIndex (literalStart + 1) rest := by
  rfl

/-- Normalize every literal occurrence in one source clause. -/
def normalizeClause {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) :
    PeriodicClause (PolarityNormalizedVariable Variable) :=
  normalizeClauseFrom clauseIndex 0 source

/-- Emit one binary complement clause for every occurrence whose polarity
must be changed. -/
def complementClausesFrom {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    List (PeriodicClause (PolarityNormalizedVariable Variable)) :=
  (source.zipIdx literalStart).filterMap fun tagged =>
    if tagged.1.value = normalizedPolarity tagged.2 then
      none
    else
      some (complementClause clauseIndex tagged.2 tagged.1)

@[simp]
theorem complementClausesFrom_cons {Variable : Type*}
    (clauseIndex literalStart : Nat)
    (literal : PeriodicLiteral Variable)
    (rest : PeriodicClause Variable) :
    complementClausesFrom clauseIndex literalStart (literal :: rest) =
      if literal.value = normalizedPolarity literalStart then
        complementClausesFrom clauseIndex (literalStart + 1) rest
      else
        complementClause clauseIndex literalStart literal ::
          complementClausesFrom clauseIndex (literalStart + 1) rest := by
  unfold complementClausesFrom
  by_cases compatible : literal.value = normalizedPolarity literalStart <;>
    simp [compatible]

/-- All complement clauses belonging to one source clause. -/
def complementClauses {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) :
    List (PeriodicClause (PolarityNormalizedVariable Variable)) :=
  complementClausesFrom clauseIndex 0 source

/-- A normalized literal suffix followed by its occurrence-local complement
clauses, retaining the absolute starting literal index. -/
def clauseClausesFrom {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    List (PeriodicClause (PolarityNormalizedVariable Variable)) :=
  normalizeClauseFrom clauseIndex literalStart source ::
    complementClausesFrom clauseIndex literalStart source

/-- One normalized clause followed by its occurrence-local complement
clauses. -/
def clauseClauses {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) :
    List (PeriodicClause (PolarityNormalizedVariable Variable)) :=
  normalizeClause clauseIndex source ::
    complementClauses clauseIndex source

@[simp]
theorem clauseClausesFrom_zero {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    clauseClausesFrom clauseIndex 0 source =
      clauseClauses clauseIndex source := by
  rfl

/-- Normalize every occurrence of a unit-free periodic exact-one formula. -/
def formula {Variable : Type*} (source : PeriodicCNF Variable) :
    PeriodicCNF (PolarityNormalizedVariable Variable) where
  clauses := source.clauses.zipIdx.flatMap fun tagged =>
    clauseClauses tagged.2 tagged.1

/-- Extend an assignment by making every occurrence-local fresh variable the
Boolean complement of its source atom at the same cell. -/
def extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    PolarityNormalizedVariable Variable → Cell → Bool
  | Sum.inl atom, cell => assignment atom cell
  | Sum.inr ((_, _), source), cell => !assignment source.atom cell

/-- Restrict a normalized assignment to the embedded source variables. -/
def restrictAssignment {Variable : Type*}
    (assignment : PolarityNormalizedVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell => assignment (Sum.inl atom) cell

@[simp]
theorem restrict_extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    restrictAssignment (extendAssignment assignment) = assignment := by
  rfl

/-- The requested polarity is false at the red and blue terminals and true
at the green terminal of every binary-or-ternary clause. -/
theorem normalizedPolarity_eq (literalIndex : Nat)
    (indexLt : literalIndex < 3) :
    (normalizedPolarity literalIndex = true ↔ literalIndex = 2) := by
  have cases : literalIndex = 0 ∨ literalIndex = 1 ∨ literalIndex = 2 := by
    omega
  rcases cases with rfl | rfl | rfl <;>
    simp [normalizedPolarity]

/-- Normalizing a literal always gives the polarity requested by its clause
terminal. -/
@[simp]
theorem normalizeLiteral_value {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    (normalizeLiteral clauseIndex literalIndex source).value =
      normalizedPolarity literalIndex := by
  simp only [normalizeLiteral]
  split
  · assumption
  · rfl

/-- Every complement clause itself obeys the red/blue false-polarity
convention. -/
theorem complementClause_values {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    (complementClause clauseIndex literalIndex source).map
        PeriodicLiteral.value = [false, false] := by
  rfl

/-- Under the canonical extension, a normalized literal has exactly the
truth value of its source occurrence. -/
@[simp]
theorem literalTruth_normalizeLiteral_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    PeriodicOneInThree.literalTruth (extendAssignment assignment) translate
        (normalizeLiteral clauseIndex literalIndex source) =
      PeriodicOneInThree.literalTruth assignment translate source := by
  by_cases compatible :
      source.value = normalizedPolarity literalIndex
  · simp [normalizeLiteral, compatible,
      PeriodicOneInThree.literalTruth, liftLiteral, extendAssignment]
  · rw [normalizeLiteral, if_neg compatible]
    simp only [PeriodicOneInThree.literalTruth,
      complementLiteral, extendAssignment]
    have opposite :
        source.value = !normalizedPolarity literalIndex := by
      have boolOpposite : ∀ first second : Bool,
          first ≠ second → first = !second := by
        decide
      exact boolOpposite source.value
        (normalizedPolarity literalIndex) compatible
    rw [opposite]
    generalize valueEq :
        assignment source.atom (Cell.add translate source.offset) = value
    generalize polarityEq : normalizedPolarity literalIndex = polarity
    cases value <;> cases polarity <;> decide

/-- The canonical extension satisfies every emitted complement clause. -/
theorem complementClause_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    PeriodicOneInThree.ClauseHolds (extendAssignment assignment) translate
      (complementClause clauseIndex literalIndex source) := by
  generalize valueEq :
      assignment source.atom (Cell.add translate source.offset) = value
  cases value <;>
    simp [PeriodicOneInThree.ClauseHolds,
      PeriodicOneInThree.clauseValues,
      PeriodicOneInThree.ExactlyOne,
      complementClause, originalFalseLiteral,
      complementFalseLiteral, extendAssignment, valueEq]

/-- Normalizing every occurrence preserves the complete truth-value list
under the canonical assignment extension. -/
theorem clauseValues_normalizeClauseFrom_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    PeriodicOneInThree.clauseValues (extendAssignment assignment) translate
        (normalizeClauseFrom clauseIndex literalStart source) =
      PeriodicOneInThree.clauseValues assignment translate source := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      change
        PeriodicOneInThree.literalTruth (extendAssignment assignment)
            translate (normalizeLiteral clauseIndex literalStart literal) ::
          PeriodicOneInThree.clauseValues (extendAssignment assignment)
            translate
            (normalizeClauseFrom clauseIndex (literalStart + 1) rest) =
        PeriodicOneInThree.literalTruth assignment translate literal ::
          PeriodicOneInThree.clauseValues assignment translate rest
      rw [literalTruth_normalizeLiteral_extend,
        induction (literalStart + 1)]

/-- The normalized main clause holds whenever its source clause holds. -/
theorem normalizeClause_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds assignment translate source) :
    PeriodicOneInThree.ClauseHolds (extendAssignment assignment) translate
      (normalizeClause clauseIndex source) := by
  unfold PeriodicOneInThree.ClauseHolds at sourceHolds ⊢
  rw [normalizeClause,
    clauseValues_normalizeClauseFrom_extend]
  exact sourceHolds

/-- Every occurrence-specific clause in the filtered complement list holds
under the canonical assignment extension. -/
theorem complementClauses_hold_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    ∀ generated ∈ complementClausesFrom clauseIndex literalStart source,
      PeriodicOneInThree.ClauseHolds
        (extendAssignment assignment) translate generated := by
  intro generated generatedMember
  simp only [complementClausesFrom, List.mem_filterMap] at generatedMember
  rcases generatedMember with ⟨⟨literal, literalIndex⟩,
    taggedMember, generatedEq⟩
  split at generatedEq
  · contradiction
  · simp only [Option.some.injEq] at generatedEq
    subst generated
    exact complementClause_holds_extend assignment translate
      clauseIndex literalIndex literal

/-- A satisfying source clause satisfies its normalized clause and all of
its complement clauses. -/
theorem clauseClauses_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds assignment translate source) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      PeriodicOneInThree.ClauseHolds
        (extendAssignment assignment) translate generated := by
  intro generated generatedMember
  simp only [clauseClauses, List.mem_cons] at generatedMember
  rcases generatedMember with rfl | generatedMember
  · exact normalizeClause_holds_extend assignment translate
      clauseIndex source sourceHolds
  · exact complementClauses_hold_extend assignment translate
      clauseIndex 0 source generated generatedMember

/-- Canonical extension sends every source solution to a solution of the
polarity-normalized formula. -/
theorem formula_satisfies_of_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (satisfies : PeriodicOneInThree.Satisfies source assignment) :
    PeriodicOneInThree.Satisfies
      (formula source) (extendAssignment assignment) := by
  intro translate generated generatedMember
  simp only [formula, List.mem_flatMap] at generatedMember
  rcases generatedMember with ⟨tagged, taggedMember, generatedMember⟩
  exact clauseClauses_complete assignment translate tagged.2 tagged.1
    (satisfies translate tagged.1
      (List.fst_mem_of_mem_zipIdx taggedMember))
    generated generatedMember

/-- Every incompatible tagged occurrence contributes its expected binary
complement clause. -/
theorem complementClause_mem_complementClausesFrom {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable)
    (literal : PeriodicLiteral Variable) (literalIndex : Nat)
    (literalMember :
      (literal, literalIndex) ∈ source.zipIdx literalStart)
    (different : literal.value ≠ normalizedPolarity literalIndex) :
    complementClause clauseIndex literalIndex literal ∈
      complementClausesFrom clauseIndex literalStart source := by
  simp only [complementClausesFrom, List.mem_filterMap]
  refine ⟨(literal, literalIndex), literalMember, ?_⟩
  simp [different]

/-- A binary exact-one clause with two negative literals forces its two
underlying variables to have opposite Boolean values. -/
theorem exactlyOne_negative_pair_forces_complement
    (first second : Bool)
    (holds :
      PeriodicOneInThree.ExactlyOne
        [first == false, second == false]) :
    first = !second := by
  cases first <;> cases second <;>
    simp_all [PeriodicOneInThree.ExactlyOne]

/-- Satisfying an emitted complement clause forces the fresh variable to be
the complement of the embedded source variable at the occurrence cell. -/
theorem complementClause_forces_complement {Variable : Type*}
    (assignment : PolarityNormalizedVariable Variable → Cell → Bool)
    (translate : Cell) (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable)
    (holds : PeriodicOneInThree.ClauseHolds assignment translate
      (complementClause clauseIndex literalIndex source)) :
    assignment (Sum.inr ((clauseIndex, literalIndex), source))
        (Cell.add translate source.offset) =
      !assignment (Sum.inl source.atom)
        (Cell.add translate source.offset) := by
  apply exactlyOne_negative_pair_forces_complement
  simpa [PeriodicOneInThree.ClauseHolds,
    PeriodicOneInThree.clauseValues, complementClause,
    originalFalseLiteral, complementFalseLiteral] using holds

/-- In any normalized solution, a normalized literal has the truth value of
its source occurrence after restricting the assignment. -/
theorem literalTruth_normalizeLiteral_restrict {Variable : Type*}
    (assignment : PolarityNormalizedVariable Variable → Cell → Bool)
    (translate : Cell) (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable)
    (complementHolds :
      source.value ≠ normalizedPolarity literalIndex →
        PeriodicOneInThree.ClauseHolds assignment translate
          (complementClause clauseIndex literalIndex source)) :
    PeriodicOneInThree.literalTruth assignment translate
        (normalizeLiteral clauseIndex literalIndex source) =
      PeriodicOneInThree.literalTruth
        (restrictAssignment assignment) translate source := by
  by_cases compatible : source.value = normalizedPolarity literalIndex
  · simp [normalizeLiteral, compatible,
      PeriodicOneInThree.literalTruth, liftLiteral, restrictAssignment]
  · rw [normalizeLiteral, if_neg compatible]
    simp only [PeriodicOneInThree.literalTruth,
      complementLiteral, restrictAssignment]
    rw [complementClause_forces_complement assignment translate
      clauseIndex literalIndex source (complementHolds compatible)]
    have opposite :
        source.value = !normalizedPolarity literalIndex := by
      have boolOpposite : ∀ first second : Bool,
          first ≠ second → first = !second := by
        decide
      exact boolOpposite source.value
        (normalizedPolarity literalIndex) compatible
    rw [opposite]
    generalize valueEq :
        assignment (Sum.inl source.atom)
          (Cell.add translate source.offset) = value
    generalize polarityEq : normalizedPolarity literalIndex = polarity
    cases value <;> cases polarity <;> decide

/-- Restriction preserves the truth-value list of a normalized clause once
all of its emitted complement clauses are known to hold. -/
theorem clauseValues_normalizeClauseFrom_restrict {Variable : Type*}
    (assignment : PolarityNormalizedVariable Variable → Cell → Bool)
    (translate : Cell) (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    (complements :
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ source.zipIdx literalStart →
        literal.value ≠ normalizedPolarity literalIndex →
        PeriodicOneInThree.ClauseHolds assignment translate
          (complementClause clauseIndex literalIndex literal)) :
    PeriodicOneInThree.clauseValues assignment translate
        (normalizeClauseFrom clauseIndex literalStart source) =
      PeriodicOneInThree.clauseValues
        (restrictAssignment assignment) translate source := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      have headComplement :
          literal.value ≠ normalizedPolarity literalStart →
          PeriodicOneInThree.ClauseHolds assignment translate
            (complementClause clauseIndex literalStart literal) := by
        intro different
        exact complements literal literalStart (by simp) different
      have tailComplements :
          ∀ tailLiteral tailIndex,
            (tailLiteral, tailIndex) ∈ rest.zipIdx (literalStart + 1) →
            tailLiteral.value ≠ normalizedPolarity tailIndex →
            PeriodicOneInThree.ClauseHolds assignment translate
              (complementClause clauseIndex tailIndex tailLiteral) := by
        intro tailLiteral tailIndex tailMember different
        exact complements tailLiteral tailIndex (by simp [tailMember])
          different
      change
        PeriodicOneInThree.literalTruth assignment translate
            (normalizeLiteral clauseIndex literalStart literal) ::
          PeriodicOneInThree.clauseValues assignment translate
            (normalizeClauseFrom clauseIndex (literalStart + 1) rest) =
        PeriodicOneInThree.literalTruth (restrictAssignment assignment)
            translate literal ::
          PeriodicOneInThree.clauseValues (restrictAssignment assignment)
            translate rest
      rw [literalTruth_normalizeLiteral_restrict assignment translate
        clauseIndex literalStart literal headComplement,
        induction (literalStart + 1) tailComplements]

/-- Restricting any normalized solution satisfies the source formula. -/
theorem satisfies_of_formula_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : PolarityNormalizedVariable Variable → Cell → Bool)
    (satisfies :
      PeriodicOneInThree.Satisfies (formula source) assignment) :
    PeriodicOneInThree.Satisfies source
      (restrictAssignment assignment) := by
  intro translate clause clauseMember
  have mappedMember : clause ∈ source.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clauseMember
  rcases List.mem_map.mp mappedMember with
    ⟨⟨taggedClause, clauseIndex⟩, taggedMember, taggedEq⟩
  simp only at taggedEq
  subst taggedClause
  have normalizedHolds :
      PeriodicOneInThree.ClauseHolds assignment translate
        (normalizeClause clauseIndex clause) := by
    apply satisfies translate (normalizeClause clauseIndex clause)
    simp only [formula, List.mem_flatMap]
    exact ⟨(clause, clauseIndex), taggedMember,
      by simp [clauseClauses]⟩
  have valuesEq :
      PeriodicOneInThree.clauseValues assignment translate
          (normalizeClause clauseIndex clause) =
        PeriodicOneInThree.clauseValues (restrictAssignment assignment)
          translate clause := by
    rw [normalizeClause]
    apply clauseValues_normalizeClauseFrom_restrict
    intro literal literalIndex literalMember different
    apply satisfies translate
      (complementClause clauseIndex literalIndex literal)
    simp only [formula, List.mem_flatMap]
    exact ⟨(clause, clauseIndex), taggedMember,
      by
        simp only [clauseClauses, List.mem_cons]
        right
        exact complementClause_mem_complementClausesFrom
          clauseIndex 0 clause literal literalIndex literalMember different⟩
  unfold PeriodicOneInThree.ClauseHolds at normalizedHolds ⊢
  rw [← valuesEq]
  exact normalizedHolds

/-- Polarity normalization preserves periodic exact-one satisfiability
exactly. -/
theorem satisfiable_iff {Variable : Type*}
    (source : PeriodicCNF Variable) :
    PeriodicOneInThree.Satisfiable (formula source) ↔
      PeriodicOneInThree.Satisfiable source := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨restrictAssignment assignment,
      satisfies_of_formula_satisfies source assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨extendAssignment assignment,
      formula_satisfies_of_satisfies source assignment satisfies⟩

/-! ## Structural promises -/

/-- A clause's polarity list is exactly the requested terminal-polarity
prefix of the same length. -/
def ClausePolarityNormalized {Variable : Type*}
    (clause : PeriodicClause Variable) : Prop :=
  clause.map PeriodicLiteral.value =
    (List.range clause.length).map normalizedPolarity

/-- Every clause in a formula obeys the terminal-polarity convention. -/
def FormulaPolarityNormalized {Variable : Type*}
    (source : PeriodicCNF Variable) : Prop :=
  ∀ clause ∈ source.clauses, ClausePolarityNormalized clause

/-- Pointwise form of a clause's polarity-normalization certificate. -/
theorem literal_value_eq_normalizedPolarity_of_clause
    {Variable : Type*} {clause : PeriodicClause Variable}
    (normalized : ClausePolarityNormalized clause)
    {literal : PeriodicLiteral Variable} {literalIndex : Nat}
    (literalMember : (literal, literalIndex) ∈ clause.zipIdx) :
    literal.value = normalizedPolarity literalIndex := by
  have indexData := List.mem_zipIdx' literalMember
  have atIndex := congrArg (fun values => values[literalIndex]?) normalized
  simpa [List.getElem?_map, List.getElem?_range, indexData.1,
    indexData.2] using atIndex

@[simp]
theorem normalizeLiteral_offset {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    (normalizeLiteral clauseIndex literalIndex source).offset =
      source.offset := by
  unfold normalizeLiteral
  split <;> rfl

/-- The normalized occurrence list has the same length as its source. -/
@[simp]
theorem normalizeClauseFrom_length {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    (normalizeClauseFrom clauseIndex literalStart source).length =
      source.length := by
  simp [normalizeClauseFrom]

@[simp]
theorem normalizeClause_length {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    (normalizeClause clauseIndex source).length = source.length := by
  simp [normalizeClause]

/-- The values of a normalized suffix are the requested polarity suffix. -/
theorem normalizeClauseFrom_values {Variable : Type*}
    (clauseIndex literalStart : Nat) (source : PeriodicClause Variable) :
    (normalizeClauseFrom clauseIndex literalStart source).map
        PeriodicLiteral.value =
      (List.range' literalStart source.length).map normalizedPolarity := by
  unfold normalizeClauseFrom
  rw [List.map_map]
  have functionEq :
      PeriodicLiteral.value ∘
          (fun tagged : PeriodicLiteral Variable × Nat =>
            normalizeLiteral clauseIndex tagged.2 tagged.1) =
        normalizedPolarity ∘ Prod.snd := by
    funext tagged
    exact normalizeLiteral_value clauseIndex tagged.2 tagged.1
  rw [functionEq, ← List.map_map, List.zipIdx_map_snd]

/-- Every normalized main clause has the requested polarity at every
terminal position. -/
theorem normalizeClause_polarityNormalized {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    ClausePolarityNormalized (normalizeClause clauseIndex source) := by
  unfold ClausePolarityNormalized
  rw [normalizeClause_length, normalizeClause,
    normalizeClauseFrom_values]
  rw [← List.range_eq_range']

/-- Every emitted binary complement clause uses false literals at both the
red and blue terminal positions. -/
theorem complementClause_polarityNormalized {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    ClausePolarityNormalized
      (complementClause clauseIndex literalIndex source) := by
  rfl

/-- All clauses emitted for one source clause obey the terminal-polarity
convention. -/
theorem clauseClauses_polarityNormalized {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      ClausePolarityNormalized generated := by
  intro generated generatedMember
  simp only [clauseClauses, List.mem_cons] at generatedMember
  rcases generatedMember with rfl | generatedMember
  · exact normalizeClause_polarityNormalized clauseIndex source
  · simp only [complementClauses, complementClausesFrom,
      List.mem_filterMap] at generatedMember
    rcases generatedMember with
      ⟨⟨literal, literalIndex⟩, literalMember, generatedEq⟩
    split at generatedEq
    · contradiction
    · simp only [Option.some.injEq] at generatedEq
      subst generated
      exact complementClause_polarityNormalized
        clauseIndex literalIndex literal

/-- The complete transformed formula obeys the requested polarity
convention. -/
theorem formula_polarityNormalized {Variable : Type*}
    (source : PeriodicCNF Variable) :
    FormulaPolarityNormalized (formula source) := by
  intro generated generatedMember
  simp only [formula, List.mem_flatMap] at generatedMember
  rcases generatedMember with ⟨tagged, taggedMember, generatedMember⟩
  exact clauseClauses_polarityNormalized tagged.2 tagged.1
    generated generatedMember

/-- Normalizing a clause preserves the paper's locality condition. -/
theorem normalizeClause_isLocal {Variable : Type*}
    (clauseIndex : Nat) {source : PeriodicClause Variable}
    (sourceLocal : source.IsLocal) :
    (normalizeClause clauseIndex source).IsLocal := by
  intro first firstMember second secondMember
  simp only [normalizeClause, normalizeClauseFrom,
    List.mem_map] at firstMember secondMember
  rcases firstMember with ⟨⟨sourceFirst, firstIndex⟩,
    sourceFirstMember, rfl⟩
  rcases secondMember with ⟨⟨sourceSecond, secondIndex⟩,
    sourceSecondMember, rfl⟩
  simp only [PeriodicClause.offsetDistance, normalizeLiteral_offset]
  exact sourceLocal sourceFirst
    (List.fst_mem_of_mem_zipIdx sourceFirstMember) sourceSecond
    (List.fst_mem_of_mem_zipIdx sourceSecondMember)

/-- A complement clause is local because its two literals have the same
offset. -/
theorem complementClause_isLocal {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    (complementClause clauseIndex literalIndex source).IsLocal := by
  simp [PeriodicClause.IsLocal, PeriodicClause.offsetDistance,
    complementClause, originalFalseLiteral, complementFalseLiteral]

/-- Every clause emitted for one local source clause remains local. -/
theorem clauseClauses_areLocal {Variable : Type*}
    (clauseIndex : Nat) {source : PeriodicClause Variable}
    (sourceLocal : source.IsLocal) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      generated.IsLocal := by
  intro generated generatedMember
  simp only [clauseClauses, List.mem_cons] at generatedMember
  rcases generatedMember with rfl | generatedMember
  · exact normalizeClause_isLocal clauseIndex sourceLocal
  · simp only [complementClauses, complementClausesFrom,
      List.mem_filterMap] at generatedMember
    rcases generatedMember with
      ⟨⟨literal, literalIndex⟩, literalMember, generatedEq⟩
    split at generatedEq
    · contradiction
    · simp only [Option.some.injEq] at generatedEq
      subst generated
      exact complementClause_isLocal clauseIndex literalIndex literal

/-- Polarity normalization preserves locality. -/
theorem formula_isLocal {Variable : Type*}
    {source : PeriodicCNF Variable} (sourceLocal : source.IsLocal) :
    (formula source).IsLocal := by
  intro generated generatedMember
  simp only [formula, List.mem_flatMap] at generatedMember
  rcases generatedMember with ⟨tagged, taggedMember, generatedMember⟩
  exact clauseClauses_areLocal tagged.2
    (sourceLocal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))
    generated generatedMember

/-- Normalizing a binary-or-ternary source clause emits only binary or
ternary clauses. -/
theorem clauseClauses_arityTwoOrThree {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (sourceArity : source.length = 2 ∨ source.length = 3) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      generated.length = 2 ∨ generated.length = 3 := by
  intro generated generatedMember
  simp only [clauseClauses, List.mem_cons] at generatedMember
  rcases generatedMember with rfl | generatedMember
  · simpa using sourceArity
  · simp only [complementClauses, complementClausesFrom,
      List.mem_filterMap] at generatedMember
    rcases generatedMember with
      ⟨⟨literal, literalIndex⟩, literalMember, generatedEq⟩
    split at generatedEq
    · contradiction
    · simp only [Option.some.injEq] at generatedEq
      subst generated
      exact Or.inl rfl

/-- Polarity normalization preserves the binary-or-ternary arity promise. -/
theorem formula_arityTwoOrThree {Variable : Type*}
    {source : PeriodicCNF Variable}
    (sourceArity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree (formula source) := by
  intro generated generatedMember
  simp only [formula, List.mem_flatMap] at generatedMember
  rcases generatedMember with ⟨tagged, taggedMember, generatedMember⟩
  exact clauseClauses_arityTwoOrThree tagged.2 tagged.1
    (sourceArity tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))
    generated generatedMember

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
