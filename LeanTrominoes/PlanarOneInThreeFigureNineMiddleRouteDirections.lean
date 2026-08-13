/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingMiddleRouteDirections
import LeanTrominoes.PlanarOneInThreePositionedInstantiation

/-!
# Middle-literal exits in Figure 9

Every literal-index-one Figure 9 route leaves its clause weakly toward
smaller `x`.  This is the one clause-side directional fact needed by the
unit-elimination head-replacement connector.
-/

namespace LeanTrominoes
namespace PlanarOneInThree

open PlanarThreeSAT

theorem figureNineDrawingFor_middleRoutesDoNotExitRight
    (first second third : Bool) :
    (figureNineDrawingFor first second third).MiddleRoutesDoNotExitRight := by
  cases first <;> cases second <;> cases third <;> native_decide

theorem figureNineTwoDrawingFor_middleRoutesDoNotExitRight
    (first second : Bool) :
    (figureNineTwoDrawingFor first second).MiddleRoutesDoNotExitRight := by
  cases first <;> cases second <;> native_decide

theorem figureNineOneDrawingFor_middleRoutesDoNotExitRight
    (first : Bool) :
    (figureNineOneDrawingFor first).MiddleRoutesDoNotExitRight := by
  cases first <;> native_decide

theorem figureNineZeroDrawing_middleRoutesDoNotExitRight :
    figureNineZeroDrawing.MiddleRoutesDoNotExitRight := by
  native_decide

theorem instantiatedThreeDrawing_middleRoutesDoNotExitRight
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool)
    (third : Variable) (thirdPolarity : Bool) :
    (instantiatedThreeDrawing position clauseIndex
      first firstPolarity second secondPolarity
      third thirdPolarity).MiddleRoutesDoNotExitRight := by
  unfold instantiatedThreeDrawing
  apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.translate
  exact
    (figureNineDrawingFor_middleRoutesDoNotExitRight
      firstPolarity secondPolarity thirdPolarity).rename
        (threeVariableMap clauseIndex
          (threeSourceClause position
            first firstPolarity second secondPolarity
            third thirdPolarity)
          first second third)
        (threeLocalPosition first second third)

theorem instantiatedTwoDrawing_middleRoutesDoNotExitRight
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool) :
    (instantiatedTwoDrawing position clauseIndex
      first firstPolarity second secondPolarity).MiddleRoutesDoNotExitRight := by
  unfold instantiatedTwoDrawing
  apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.translate
  exact
    (figureNineTwoDrawingFor_middleRoutesDoNotExitRight
      firstPolarity secondPolarity).rename
        (twoVariableMap clauseIndex
          (twoSourceClause position
            first firstPolarity second secondPolarity)
          first second)
        (twoLocalPosition first second)

theorem instantiatedOneDrawing_middleRoutesDoNotExitRight
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool) :
    (instantiatedOneDrawing position clauseIndex
      first firstPolarity).MiddleRoutesDoNotExitRight := by
  unfold instantiatedOneDrawing
  apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.translate
  exact
    (figureNineOneDrawingFor_middleRoutesDoNotExitRight
      firstPolarity).rename
        (oneVariableMap clauseIndex
          (oneSourceClause position first firstPolarity) first)
        (oneLocalPosition first)

theorem instantiatedZeroDrawing_middleRoutesDoNotExitRight
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat) :
    (instantiatedZeroDrawing (Variable := Variable)
      position clauseIndex).MiddleRoutesDoNotExitRight := by
  unfold instantiatedZeroDrawing
  apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.translate
  exact figureNineZeroDrawing_middleRoutesDoNotExitRight.rename
    (zeroVariableMap clauseIndex
      (zeroSourceClause (Variable := Variable) position))
    zeroLocalPosition

end PlanarOneInThree

namespace PlanarOneInThreePositioned

open PlanarThreeSAT

/-- Every positioned Figure 9 instance selected from a width-three source
has weak-left middle routes. -/
theorem instantiatedDrawing_middleRoutesDoNotExitRight
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3) :
    (instantiatedDrawing clauseIndex source).MiddleRoutesDoNotExitRight := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · unfold instantiatedDrawing instantiatedZeroDrawing rescopeDrawing
    apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.rename
    exact PlanarOneInThree.instantiatedZeroDrawing_middleRoutesDoNotExitRight
      (Variable := Variable) sourcePosition clauseIndex
  · rcases rest with _ | ⟨second, rest⟩
    · unfold instantiatedDrawing instantiatedOneDrawing rescopeDrawing
      apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.rename
      exact PlanarOneInThree.instantiatedOneDrawing_middleRoutesDoNotExitRight
        sourcePosition clauseIndex first.atom first.value
    · rcases rest with _ | ⟨third, tail⟩
      · unfold instantiatedDrawing instantiatedTwoDrawing rescopeDrawing
        apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.rename
        exact PlanarOneInThree.instantiatedTwoDrawing_middleRoutesDoNotExitRight
          sourcePosition clauseIndex
          first.atom first.value second.atom second.value
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        unfold instantiatedDrawing instantiatedThreeDrawing rescopeDrawing
        apply EmbeddedCNFIncidenceDrawing.MiddleRoutesDoNotExitRight.rename
        exact PlanarOneInThree.instantiatedThreeDrawing_middleRoutesDoNotExitRight
          sourcePosition clauseIndex
          first.atom first.value second.atom second.value
          third.atom third.value

end PlanarOneInThreePositioned
end LeanTrominoes
