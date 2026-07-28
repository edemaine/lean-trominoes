import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATSourceMembership
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation

/-!
# Clause shape under planar-SAT source translation

Period translation changes the physical variables and clause positions of a
local gadget, but not its presentation order or any clause arity.  Thus a
clause index and literal index valid in one source remain valid in every
physical translate of that source.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The clause-arity profile of an embedded finite formula, retaining clause
order while forgetting variables and positions. -/
def embeddedFormulaArityProfile
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable)) : List Nat :=
  formula.map fun clause => clause.literals.length

/-- Translating a planar-SAT clause source preserves its ordered clause-arity
profile. -/
theorem DrawingPlanarSATClauseSource.clauseFormula_arityProfile_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) :
    embeddedFormulaArityProfile
        ((source.periodTranslate formula shift).clauseFormula formula) =
      embeddedFormulaArityProfile
        (source.clauseFormula formula) := by
  cases source <;>
    simp [DrawingPlanarSATClauseSource.periodTranslate,
      DrawingPlanarSATClauseSource.clauseFormula,
      embeddedFormulaArityProfile,
      drawingPlanarSATCrossoverFormulaAt,
      drawingPlanarSATCarrierFormulaAt,
      drawingPlanarSATBendFormulaAt,
      drawingPlanarSATRoutedVariableFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      equalityInstance, routedClauseAt,
      clauseRouteOccurrencesAt_periodTranslate,
      EmbeddedClause.rename, EmbeddedClause.place,
      EmbeddedClause.map, List.map_map, Function.comp_def]

/-- Equal ordered arity profiles transfer any valid clause/literal index pair
to the target formula. -/
theorem exists_clauseLiteral_of_arityProfile_eq
    {Variable : Type*}
    (sourceFormula targetFormula :
      List (EmbeddedClause Variable))
    (profileEq :
      embeddedFormulaArityProfile targetFormula =
        embeddedFormulaArityProfile sourceFormula)
    (sourceClause : EmbeddedClause Variable)
    (clauseIndex : Nat)
    (sourceClauseMember :
      (sourceClause, clauseIndex) ∈ sourceFormula.zipIdx)
    (sourceLiteral : Variable × Bool)
    (literalIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx) :
    ∃ targetClause targetLiteral,
      (targetClause, clauseIndex) ∈ targetFormula.zipIdx ∧
        (targetLiteral, literalIndex) ∈
          targetClause.literals.zipIdx := by
  have sourceClauseLookup :
      sourceFormula[clauseIndex]? = some sourceClause :=
    (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember
  have sourceLiteralLookup :
      sourceClause.literals[literalIndex]? = some sourceLiteral :=
    (List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember
  have profileLookup :=
    congrArg (fun profile => profile[clauseIndex]?) profileEq
  simp only [embeddedFormulaArityProfile, List.getElem?_map,
    sourceClauseLookup, Option.map_some] at profileLookup
  rcases Option.map_eq_some_iff.mp profileLookup with
    ⟨targetClause, targetClauseLookup, targetLengthEq⟩
  have targetLiteralIndexLt :
      literalIndex < targetClause.literals.length := by
    have sourceLiteralIndexLt :
        literalIndex < sourceClause.literals.length :=
      (List.getElem?_eq_some_iff.mp sourceLiteralLookup).1
    simpa only [targetLengthEq] using sourceLiteralIndexLt
  let targetLiteral := targetClause.literals[literalIndex]
  refine ⟨targetClause, targetLiteral,
    (List.mem_zipIdx_iff_getElem?).mpr targetClauseLookup, ?_⟩
  apply (List.mem_zipIdx_iff_getElem?).mpr
  rw [List.getElem?_eq_getElem targetLiteralIndexLt]

/-- A clause and literal at recorded local indices have counterparts at the
same indices in every translated source. -/
theorem DrawingPlanarSATClauseSource.exists_periodTranslatedClauseLiteral
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (sourceClause : EmbeddedClause (PlanarSATVariable Variable))
    (sourceClauseMember :
      (sourceClause, source.localClauseIndex) ∈
        (source.clauseFormula formula).zipIdx)
    (sourceLiteral : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx) :
    ∃ targetClause targetLiteral,
      (targetClause,
          (source.periodTranslate formula shift).localClauseIndex) ∈
        ((source.periodTranslate formula shift).clauseFormula
          formula).zipIdx ∧
      (targetLiteral, literalIndex) ∈
        targetClause.literals.zipIdx := by
  rw [DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate]
  exact exists_clauseLiteral_of_arityProfile_eq
    (source.clauseFormula formula)
    ((source.periodTranslate formula shift).clauseFormula formula)
    (source.clauseFormula_arityProfile_periodTranslate formula shift)
    sourceClause source.localClauseIndex sourceClauseMember
    sourceLiteral literalIndex sourceLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
