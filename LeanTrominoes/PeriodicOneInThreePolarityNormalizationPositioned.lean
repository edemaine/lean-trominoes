import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationOccurrences

/-!
# Positioned polarity normalization

For an incompatible literal occurrence, logical polarity normalization
replaces the original clause-variable incidence by the three-edge path

`source clause -- fresh variable -- complement clause -- original variable`.

This file lifts that replacement to `PositionedPeriodicCNF`.  The positions
of the two new vertices are parameters: the logical and occurrence proofs do
not depend on how a later planar drawing chooses subdivision points along the
old incidence route.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationPositioned

open PeriodicOneInThreePolarityNormalization

/-- The occurrence tag carried by a fresh complement variable. -/
abbrev FreshOccurrence (Variable : Type*) :=
  (Nat × Nat) × PeriodicLiteral Variable

/-- Physical prototype positions for the vertices introduced by polarity
normalization.  Values for already-compatible occurrences are harmless. -/
structure Positions (Variable : Type*) where
  freshVariable : FreshOccurrence Variable → Cell
  complementClause : FreshOccurrence Variable → Cell

/-- Extend an existing periodic variable placement with the supplied fresh
complement-variable positions. -/
def placement {Variable : Type*}
    (source : PeriodicVariablePlacement Variable)
    (positions : Positions Variable) :
    PeriodicVariablePlacement (PolarityNormalizedVariable Variable) where
  period := source.period
  position
    | Sum.inl atom => source.position atom
    | Sum.inr fresh => positions.freshVariable fresh

@[simp]
theorem placement_period {Variable : Type*}
    (source : PeriodicVariablePlacement Variable)
    (positions : Positions Variable) :
    (placement source positions).period = source.period := by
  rfl

@[simp]
theorem placement_original_position {Variable : Type*}
    (source : PeriodicVariablePlacement Variable)
    (positions : Positions Variable) (atom : Variable) :
    (placement source positions).position (Sum.inl atom) =
      source.position atom := by
  rfl

@[simp]
theorem placement_fresh_position {Variable : Type*}
    (source : PeriodicVariablePlacement Variable)
    (positions : Positions Variable)
    (fresh : FreshOccurrence Variable) :
    (placement source positions).position (Sum.inr fresh) =
      positions.freshVariable fresh := by
  rfl

/-- The normalized main clause retains its source clause vertex. -/
def normalizedClause {Variable : Type*}
    (clauseIndex : Nat) (source : PositionedPeriodicClause Variable) :
    PositionedPeriodicClause (PolarityNormalizedVariable Variable) where
  position := source.position
  literals := normalizeClause clauseIndex source.literals

/-- Position one binary complement clause at its supplied subdivision
vertex. -/
def positionedComplementClause {Variable : Type*}
    (positions : Positions Variable) (clauseIndex literalIndex : Nat)
    (source : PeriodicLiteral Variable) :
    PositionedPeriodicClause (PolarityNormalizedVariable Variable) where
  position :=
    positions.complementClause
      ((clauseIndex, literalIndex), source)
  literals := complementClause clauseIndex literalIndex source

/-- Positioned binary complement clauses for one literal suffix. -/
def positionedComplementClausesFrom {Variable : Type*}
    (positions : Positions Variable) (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    List
      (PositionedPeriodicClause
        (PolarityNormalizedVariable Variable)) :=
  (source.zipIdx literalStart).filterMap fun tagged =>
    if tagged.1.value = normalizedPolarity tagged.2 then
      none
    else
      some
        (positionedComplementClause positions clauseIndex
          tagged.2 tagged.1)

@[simp]
theorem positionedComplementClausesFrom_cons {Variable : Type*}
    (positions : Positions Variable) (clauseIndex literalStart : Nat)
    (literal : PeriodicLiteral Variable)
    (rest : PeriodicClause Variable) :
    positionedComplementClausesFrom positions clauseIndex literalStart
        (literal :: rest) =
      if literal.value = normalizedPolarity literalStart then
        positionedComplementClausesFrom positions clauseIndex
          (literalStart + 1) rest
      else
        positionedComplementClause positions clauseIndex literalStart
            literal ::
          positionedComplementClausesFrom positions clauseIndex
            (literalStart + 1) rest := by
  unfold positionedComplementClausesFrom
  by_cases compatible :
      literal.value = normalizedPolarity literalStart <;>
    simp [compatible]

/-- Erasing positions from the positioned complement clauses recovers the
logical complement-clause list exactly. -/
@[simp]
theorem positionedComplementClausesFrom_literals {Variable : Type*}
    (positions : Positions Variable) (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    (positionedComplementClausesFrom positions clauseIndex literalStart
        source).map PositionedPeriodicClause.literals =
      complementClausesFrom clauseIndex literalStart source := by
  induction source generalizing literalStart with
  | nil =>
      rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [positionedComplementClausesFrom_cons,
          complementClausesFrom_cons, compatible,
          induction (literalStart + 1)]
      · simp [positionedComplementClausesFrom_cons,
          complementClausesFrom_cons, compatible,
          positionedComplementClause,
          induction (literalStart + 1)]

/-- The positioned replacement block for one source clause. -/
def clauseBlock {Variable : Type*}
    (positions : Positions Variable) (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    List
      (PositionedPeriodicClause
        (PolarityNormalizedVariable Variable)) :=
  normalizedClause clauseIndex source ::
    positionedComplementClausesFrom positions clauseIndex 0
      source.literals

/-- Erasing one positioned replacement block gives the corresponding
logical polarity-normalization block. -/
@[simp]
theorem clauseBlock_literals {Variable : Type*}
    (positions : Positions Variable) (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    (clauseBlock positions clauseIndex source).map
        PositionedPeriodicClause.literals =
      clauseClauses clauseIndex source.literals := by
  simp [clauseBlock, normalizedClause, clauseClauses,
    complementClauses]

/-- Positioned polarity normalization with abstract subdivision positions. -/
def formula {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF (PolarityNormalizedVariable Variable) where
  clauses := source.clauses.zipIdx.flatMap fun tagged =>
    clauseBlock positions tagged.2 tagged.1

/-- Forgetting the new vertex positions recovers the verified logical
polarity-normalization formula exactly. -/
@[simp]
theorem erase_formula {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    (formula positions source).erase =
      PeriodicOneInThreePolarityNormalization.formula source.erase := by
  simp [formula, PositionedPeriodicCNF.erase,
    PeriodicOneInThreePolarityNormalization.formula,
    List.map_flatMap, List.zipIdx_map]
  rw [List.flatMap_map]
  simp [Prod.map]

/-- Positioned polarity normalization preserves exact-one satisfiability. -/
theorem satisfiable_iff {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    PeriodicOneInThree.Satisfiable (formula positions source).erase ↔
      PeriodicOneInThree.Satisfiable source.erase := by
  rw [erase_formula]
  exact PeriodicOneInThreePolarityNormalization.satisfiable_iff source.erase

/-- Positioned polarity normalization preserves locality. -/
theorem formula_isLocal {Variable : Type*}
    (positions : Positions Variable)
    {source : PositionedPeriodicCNF Variable}
    (sourceLocal : source.erase.IsLocal) :
    (formula positions source).erase.IsLocal := by
  rw [erase_formula]
  exact PeriodicOneInThreePolarityNormalization.formula_isLocal sourceLocal

/-- Positioned polarity normalization preserves binary-or-ternary arity. -/
theorem formula_arityTwoOrThree {Variable : Type*}
    (positions : Positions Variable)
    {source : PositionedPeriodicCNF Variable}
    (sourceArity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (formula positions source).erase := by
  rw [erase_formula]
  exact
    PeriodicOneInThreePolarityNormalization.formula_arityTwoOrThree
      sourceArity

/-- Every positioned output clause obeys the terminal-polarity convention. -/
theorem formula_polarityNormalized {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    PeriodicOneInThreePolarityNormalization.FormulaPolarityNormalized
      (formula positions source).erase := by
  rw [erase_formula]
  exact
    PeriodicOneInThreePolarityNormalization.formula_polarityNormalized
      source.erase

/-- Positioned polarity normalization preserves the occurrence-three
restriction. -/
theorem formula_occurrencesAtMostThree {Variable : Type*}
    [DecidableEq Variable]
    (positions : Positions Variable)
    {source : PositionedPeriodicCNF Variable}
    (sourceOccurrences : source.erase.OccurrencesAtMost 3) :
    (formula positions source).erase.OccurrencesAtMost 3 := by
  rw [erase_formula]
  exact
    PeriodicOneInThreePolarityNormalization.formula_occurrencesAtMostThree
      source.erase sourceOccurrences

end PeriodicOneInThreePolarityNormalizationPositioned
end LeanTrominoes
