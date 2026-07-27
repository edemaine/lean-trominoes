import LeanTrominoes.PlanarOneInThreeLocalDistinctness
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineInstantiation

/-!
# Uniform selection of composed Figure 9 drawings

The four certified Figure 9-plus-unit-elimination instances are packaged
behind one total selector.  For a width-three source clause the selected
drawing embeds exactly the actual two-stage positioned clause block, and
source-atom distinctness supplies its complete geometric certificate.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Select the composed drawing determined by a positioned source clause's
arity.  Inputs beyond width three use the ternary prefix as a total
fallback. -/
def instantiatedDrawing
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  match source.literals with
  | [] =>
      instantiatedZeroDrawing
        sourceClauseIndex figureNineClauseStart source
  | [first] =>
      instantiatedOneDrawing
        sourceClauseIndex figureNineClauseStart source first
  | [first, second] =>
      instantiatedTwoDrawing
        sourceClauseIndex figureNineClauseStart source first second
  | first :: second :: third :: _ =>
      instantiatedThreeDrawing
        sourceClauseIndex figureNineClauseStart source
        first second third

/-- For a width-three source, the selected drawing's formula is exactly the
actual composed positioned clause block. -/
theorem instantiatedDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).formula =
        composedClauseGadget
          sourceClauseIndex figureNineClauseStart source := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedZeroDrawing_formula
      sourceClauseIndex figureNineClauseStart
      ⟨sourcePosition, []⟩ rfl
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedOneDrawing_formula
        sourceClauseIndex figureNineClauseStart
        ⟨sourcePosition, [first]⟩ first rfl
    · rcases rest with _ | ⟨third, tail⟩
      · exact instantiatedTwoDrawing_formula
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second]⟩
          first second rfl
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        exact instantiatedThreeDrawing_formula
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second, third]⟩
          first second third rfl

/-- Width at most three and pairwise distinct source atoms make the selected
composed drawing valid. -/
theorem instantiatedDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup) :
    @EmbeddedCNFIncidenceDrawing.IsValid
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
      nestedVariableDecidableEq
      (instantiatedDrawing
        sourceClauseIndex figureNineClauseStart source) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedZeroDrawing_isValid
      sourceClauseIndex figureNineClauseStart
      ⟨sourcePosition, []⟩
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedOneDrawing_isValid
        sourceClauseIndex figureNineClauseStart
        ⟨sourcePosition, [first]⟩ first
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond : first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact instantiatedTwoDrawing_isValid
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second]⟩
          first second firstNeSecond
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        have pairwise :
            (first.atom ≠ second.atom ∧
              first.atom ≠ third.atom) ∧
            second.atom ≠ third.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact instantiatedThreeDrawing_isValid
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second, third]⟩
          first second third
          pairwise.1.1 pairwise.1.2 pairwise.2

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
