import LeanTrominoes.PlanarOneInThreeLocalDistinctness
import LeanTrominoes.PlanarOneInThreeNoUnitsInstantiation

/-!
# Uniform selection of positioned unit-elimination drawings

The unit-elimination layer already has certified drawings for empty, unit,
binary, and ternary positioned periodic source clauses.  This module
packages them behind one total arity selector and derives its exact formula
and validity interfaces from width three and per-clause atom distinctness.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnits

open PlanarThreeSAT

/-- Select the certified unit-elimination instance determined by a source
clause's arity.  Inputs beyond width three use the ternary prefix as a total
fallback. -/
def instantiatedDrawing
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable Variable) :=
  match source.literals with
  | [] => instantiatedEmptyDrawing clauseIndex source
  | [first] =>
      instantiatedUnitDrawing clauseIndex source first
  | [first, second] =>
      instantiatedTwoDrawing clauseIndex source first second
  | first :: second :: third :: _ =>
      instantiatedThreeDrawing clauseIndex source
        first second third

/-- For a width-three source, the selected drawing embeds exactly the actual
positioned unit-elimination output block. -/
theorem instantiatedDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3) :
    (instantiatedDrawing clauseIndex source).formula =
      (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
        clauseIndex source).map embedPositionedClause := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedEmptyDrawing_formula
      clauseIndex ⟨sourcePosition, []⟩ rfl
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedUnitDrawing_formula
        clauseIndex ⟨sourcePosition, [first]⟩ first rfl
    · rcases rest with _ | ⟨third, tail⟩
      · exact instantiatedTwoDrawing_formula
          clauseIndex
          ⟨sourcePosition, [first, second]⟩
          first second rfl
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        exact instantiatedThreeDrawing_formula
          clauseIndex
          ⟨sourcePosition, [first, second, third]⟩
          first second third rfl

/-- Width at most three and pairwise distinct source atoms make the selected
unit-elimination drawing valid. -/
theorem instantiatedDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup) :
    (instantiatedDrawing clauseIndex source).IsValid := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedEmptyDrawing_isValid
      clauseIndex ⟨sourcePosition, []⟩
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedUnitDrawing_isValid
        clauseIndex ⟨sourcePosition, [first]⟩ first
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond : first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact instantiatedTwoDrawing_isValid
          clauseIndex
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
          clauseIndex
          ⟨sourcePosition, [first, second, third]⟩
          first second third
          pairwise.1.1 pairwise.1.2 pairwise.2

/-- Every clause-scoped auxiliary keeps its declared local unit-elimination
coordinate under the uniform arity selector and the actual positioned
auxiliary scope. -/
theorem instantiatedDrawing_auxiliaryPosition
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    (instantiatedDrawing clauseIndex source).variablePosition
        (.inr ((clauseIndex, source.literals), kind)) =
      Cell.add
        (Cell.scale
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale
          source.position)
        (PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition
          kind) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · cases kind <;>
      simp [instantiatedDrawing, instantiatedEmptyDrawing,
        emptyLocalPosition,
        EmbeddedCNFIncidenceDrawing.rename,
        EmbeddedCNFIncidenceDrawing.translate]
  · rcases rest with _ | ⟨second, rest⟩
    · cases kind <;>
        simp [instantiatedDrawing, instantiatedUnitDrawing,
          unitLocalPosition,
          EmbeddedCNFIncidenceDrawing.rename,
          EmbeddedCNFIncidenceDrawing.translate]
    · rcases rest with _ | ⟨third, tail⟩
      · cases kind <;>
          simp [instantiatedDrawing, instantiatedTwoDrawing,
            twoLocalPosition,
            EmbeddedCNFIncidenceDrawing.rename,
            EmbeddedCNFIncidenceDrawing.translate]
      · cases kind <;>
          simp [instantiatedDrawing, instantiatedThreeDrawing,
            threeLocalPosition,
            EmbeddedCNFIncidenceDrawing.rename,
            EmbeddedCNFIncidenceDrawing.translate]

end PlanarOneInThreeNoUnits
end LeanTrominoes
