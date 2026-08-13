/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTwoPointRoutes
import LeanTrominoes.PlanarOneInThreePositionedInstantiation

/-!
# Two-point auxiliary routes in Figure 9

Every Figure 9 route on an auxiliary variable that consists of one listed
segment is vertical.  Original-variable routes are deliberately excluded:
some boundary-port routes in the finite templates are horizontal, and the
global construction replaces those routes by longer inherited routes.

The finite template checks below transport through translation and both
logical-variable renamings used by positioned instantiation.
-/

namespace LeanTrominoes
namespace PlanarOneInThree

open PlanarThreeSAT

/-- The seven non-source roles in a finite Figure 9 template. -/
def FigureNineVariable.IsAuxiliary : FigureNineVariable → Prop
  | .sourceFirst | .sourceSecond | .sourceThird => False
  | .firstChoice | .secondChoice | .firstSlack | .secondSlack |
      .firstPadding | .secondPadding | .thirdPadding => True

instance (role : FigureNineVariable) : Decidable role.IsAuxiliary := by
  cases role <;> unfold FigureNineVariable.IsAuxiliary <;> infer_instance

/-- The right summand of the generated Figure 9 variable type. -/
def OneInThreeVariable.IsAuxiliary {Variable : Type*} :
    OneInThreeVariable Variable → Prop
  | .inl _ => False
  | .inr _ => True

instance {Variable : Type*} (atom : OneInThreeVariable Variable) :
    Decidable (OneInThreeVariable.IsAuxiliary atom) := by
  cases atom <;> unfold OneInThreeVariable.IsAuxiliary <;> infer_instance

theorem figureNineDrawingFor_twoPointAuxiliaryRoutesVertical
    (first second third : Bool) :
    (figureNineDrawingFor first second third).TwoPointRoutesVerticalOn
      FigureNineVariable.IsAuxiliary := by
  cases first <;> cases second <;> cases third <;> native_decide

theorem figureNineTwoDrawingFor_twoPointAuxiliaryRoutesVertical
    (first second : Bool) :
    (figureNineTwoDrawingFor first second).TwoPointRoutesVerticalOn
      FigureNineVariable.IsAuxiliary := by
  cases first <;> cases second <;> native_decide

theorem figureNineOneDrawingFor_twoPointAuxiliaryRoutesVertical
    (first : Bool) :
    (figureNineOneDrawingFor first).TwoPointRoutesVerticalOn
      FigureNineVariable.IsAuxiliary := by
  cases first <;> native_decide

theorem figureNineZeroDrawing_twoPointRoutesVertical :
    figureNineZeroDrawing.TwoPointRoutesVertical := by
  native_decide

theorem instantiatedThreeDrawing_twoPointAuxiliaryRoutesVertical
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool)
    (third : Variable) (thirdPolarity : Bool) :
    (instantiatedThreeDrawing position clauseIndex
      first firstPolarity second secondPolarity
      third thirdPolarity).TwoPointRoutesVerticalOn
        OneInThreeVariable.IsAuxiliary := by
  unfold instantiatedThreeDrawing
  apply EmbeddedCNFIncidenceDrawing.TwoPointRoutesVerticalOn.translate
  apply
    (figureNineDrawingFor_twoPointAuxiliaryRoutesVertical
      firstPolarity secondPolarity thirdPolarity).rename
        (threeVariableMap clauseIndex
          (threeSourceClause position
            first firstPolarity second secondPolarity
            third thirdPolarity)
          first second third)
        (threeLocalPosition first second third)
  · intro role auxiliary
    cases role <;>
      simp_all [FigureNineVariable.IsAuxiliary,
        OneInThreeVariable.IsAuxiliary, threeVariableMap]

theorem instantiatedTwoDrawing_twoPointAuxiliaryRoutesVertical
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool) :
    (instantiatedTwoDrawing position clauseIndex
      first firstPolarity second secondPolarity).TwoPointRoutesVerticalOn
        OneInThreeVariable.IsAuxiliary := by
  unfold instantiatedTwoDrawing
  apply EmbeddedCNFIncidenceDrawing.TwoPointRoutesVerticalOn.translate
  apply
    (figureNineTwoDrawingFor_twoPointAuxiliaryRoutesVertical
      firstPolarity secondPolarity).rename
        (twoVariableMap clauseIndex
          (twoSourceClause position
            first firstPolarity second secondPolarity)
          first second)
        (twoLocalPosition first second)
  · intro role auxiliary
    cases role <;>
      simp_all [FigureNineVariable.IsAuxiliary,
        OneInThreeVariable.IsAuxiliary, twoVariableMap]

theorem instantiatedOneDrawing_twoPointAuxiliaryRoutesVertical
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool) :
    (instantiatedOneDrawing position clauseIndex
      first firstPolarity).TwoPointRoutesVerticalOn
        OneInThreeVariable.IsAuxiliary := by
  unfold instantiatedOneDrawing
  apply EmbeddedCNFIncidenceDrawing.TwoPointRoutesVerticalOn.translate
  apply
    (figureNineOneDrawingFor_twoPointAuxiliaryRoutesVertical
      firstPolarity).rename
        (oneVariableMap clauseIndex
          (oneSourceClause position first firstPolarity) first)
        (oneLocalPosition first)
  · intro role auxiliary
    cases role <;>
      simp_all [FigureNineVariable.IsAuxiliary,
        OneInThreeVariable.IsAuxiliary, oneVariableMap]

theorem instantiatedZeroDrawing_twoPointAuxiliaryRoutesVertical
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat) :
    (instantiatedZeroDrawing (Variable := Variable)
      position clauseIndex).TwoPointRoutesVerticalOn
        OneInThreeVariable.IsAuxiliary := by
  unfold instantiatedZeroDrawing
  have renamedVertical := figureNineZeroDrawing_twoPointRoutesVertical.rename
    (zeroVariableMap clauseIndex
      (zeroSourceClause (Variable := Variable) position))
    zeroLocalPosition
  have translatedVertical := renamedVertical.translate
    (Cell.scale gadgetScale position)
  intro incidenceIndex _auxiliary
  exact translatedVertical incidenceIndex

end PlanarOneInThree

namespace PlanarOneInThreePositioned

open PlanarThreeSAT

/-- Rescoping preserves whether a generated variable is auxiliary. -/
theorem rescopeEquiv_auxiliary
    {Variable : Type*} [DecidableEq Variable]
    (oldScope newScope : Nat × PeriodicClause Variable)
    (atom : OneInThreeVariable Variable) :
    PlanarOneInThree.OneInThreeVariable.IsAuxiliary
        (rescopeEquiv oldScope newScope atom) →
      PlanarOneInThree.OneInThreeVariable.IsAuxiliary atom := by
  cases atom <;>
    simp [PlanarOneInThree.OneInThreeVariable.IsAuxiliary,
      rescopeEquiv]

/-- Every positioned Figure 9 instance selected from a width-three source
has vertical two-point routes on auxiliary variables. -/
theorem instantiatedDrawing_twoPointAuxiliaryRoutesVertical
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3) :
    (instantiatedDrawing clauseIndex source).TwoPointRoutesVerticalOn
      PlanarOneInThree.OneInThreeVariable.IsAuxiliary := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · unfold instantiatedDrawing instantiatedZeroDrawing rescopeDrawing
    apply
      (PlanarOneInThree.instantiatedZeroDrawing_twoPointAuxiliaryRoutesVertical
        (Variable := Variable) sourcePosition clauseIndex).rename
    exact rescopeEquiv_auxiliary _ _
  · rcases rest with _ | ⟨second, rest⟩
    · unfold instantiatedDrawing instantiatedOneDrawing rescopeDrawing
      apply
        (PlanarOneInThree.instantiatedOneDrawing_twoPointAuxiliaryRoutesVertical
          sourcePosition clauseIndex first.atom first.value).rename
      exact rescopeEquiv_auxiliary _ _
    · rcases rest with _ | ⟨third, tail⟩
      · unfold instantiatedDrawing instantiatedTwoDrawing rescopeDrawing
        apply
          (PlanarOneInThree.instantiatedTwoDrawing_twoPointAuxiliaryRoutesVertical
            sourcePosition clauseIndex
            first.atom first.value second.atom second.value).rename
        exact rescopeEquiv_auxiliary _ _
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        unfold instantiatedDrawing instantiatedThreeDrawing rescopeDrawing
        apply
          (PlanarOneInThree.instantiatedThreeDrawing_twoPointAuxiliaryRoutesVertical
            sourcePosition clauseIndex
            first.atom first.value second.atom second.value
            third.atom third.value).rename
        exact rescopeEquiv_auxiliary _ _

end PlanarOneInThreePositioned
end LeanTrominoes
