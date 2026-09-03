/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingClauseSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeCanonical
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixData

/-! # Semantics of finite Figure 9 route-prefix descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open UnaryProgramClauseProfile
open FormulaShapeDirectionOrdering

/-- On a genuine nonempty width-three clause, forgetting the directed
descriptor recovers its exact finite literal profile. -/
theorem clauseProfile_ofClause
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    clauseProfile (DirectedClauseProfile.ofClause
        routes clauseIndex clause) =
      FormulaShapeOfFormula.clauseProfile
        (ClauseProfileOccurrenceSplit.literalProfiles
          clause.literals) := by
  rcases clause with ⟨position, literals⟩
  dsimp only at nonempty width ⊢
  cases literals with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil =>
          simp [DirectedClauseProfile.ofClause, annotatedLiterals,
            DirectedClauseProfile.ofList, clauseProfile,
            FormulaShapeDirectionOrdering.literalProfile,
            FormulaShapeOfFormula.clauseProfile,
            ClauseProfileOccurrenceSplit.literalProfiles]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [DirectedClauseProfile.ofClause, annotatedLiterals,
                DirectedClauseProfile.ofList, clauseProfile,
                FormulaShapeDirectionOrdering.literalProfile,
                FormulaShapeOfFormula.clauseProfile,
                ClauseProfileOccurrenceSplit.literalProfiles]
          | cons third rest =>
              cases rest with
              | nil =>
                  simp [DirectedClauseProfile.ofClause, annotatedLiterals,
                    DirectedClauseProfile.ofList, clauseProfile,
                    FormulaShapeDirectionOrdering.literalProfile,
                    FormulaShapeOfFormula.clauseProfile,
                    ClauseProfileOccurrenceSplit.literalProfiles]
              | cons fourth rest =>
                  simp only [List.length_cons] at width
                  omega

/-- Sorting a genuine directed clause profile and then forgetting its route
directions gives the canonical finite profile of the correspondingly
clockwise-reordered positioned clause. -/
theorem clauseProfile_orderedDirectedProfile_ofClause
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    clauseProfile
        (orderedDirectedProfile
          (DirectedClauseProfile.ofClause routes clauseIndex clause)) =
      FormulaShapeOfFormula.clauseProfile
        (ClauseProfileOccurrenceSplit.literalProfiles
          (PositionedPeriodicCNF.orderClauseByRouteDirection
            routes clauseIndex clause).literals) := by
  apply ClauseProfile.literals_injective
  rw [clauseProfile_orderedDirectedProfile,
    DirectedClauseProfile.orderedProfile_ofClause_literals
      routes clauseIndex clause nonempty width]
  exact (FormulaShapeOfFormula.clauseProfile_literals
    (ClauseProfileOccurrenceSplit.literalProfiles
      (PositionedPeriodicCNF.orderClauseByRouteDirection
        routes clauseIndex clause).literals)
    (by
      apply List.ne_nil_of_length_pos
      simpa [ClauseProfileOccurrenceSplit.literalProfiles,
        PositionedPeriodicCNF.orderClauseByRouteDirection_length] using
          (List.length_pos_iff.mpr nonempty))
    (by
      simpa [ClauseProfileOccurrenceSplit.literalProfiles,
        PositionedPeriodicCNF.orderClauseByRouteDirection_length] using width)).symm

/-- At every genuine source-literal slot, the reconstructed fan has exactly
the semantic first direction.  Inactive directions are intentionally left at
the finite fallback because no connector can inspect them. -/
theorem exitFanData_direction_ofClause
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (width : clause.literals.length ≤ 3)
    (literalIndex : Nat) (literalIndexLt : literalIndex < clause.literals.length) :
    let slot : Fin 3 := ⟨literalIndex, lt_of_lt_of_le literalIndexLt width⟩
    (exitFanData (DirectedClauseProfile.ofClause
        routes clauseIndex clause)).direction slot =
      (PositionedPeriodicCNF.clauseExitFanData
        clause clauseIndex routes).direction slot := by
  rcases clause with ⟨position, literals⟩
  dsimp only at width literalIndexLt ⊢
  cases literals with
  | nil => simp at literalIndexLt
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [List.length_cons, List.length_nil] at literalIndexLt
          have indexEq : literalIndex = 0 := by omega
          subst literalIndex
          simp [DirectedClauseProfile.ofClause, annotatedLiterals,
            DirectedClauseProfile.ofList, exitFanData,
            DirectedClauseProfile.taggedLiterals,
            PositionedPeriodicCNF.clauseExitFanData]
      | cons second rest =>
          cases rest with
          | nil =>
              simp only [List.length_cons, List.length_nil] at literalIndexLt
              have indexCases : literalIndex = 0 ∨ literalIndex = 1 := by
                omega
              rcases indexCases with indexEq | indexEq <;>
                subst literalIndex <;>
                simp [DirectedClauseProfile.ofClause, annotatedLiterals,
                  DirectedClauseProfile.ofList, exitFanData,
                  DirectedClauseProfile.taggedLiterals,
                  PositionedPeriodicCNF.clauseExitFanData]
          | cons third rest =>
              cases rest with
              | nil =>
                  simp only [List.length_cons, List.length_nil]
                    at literalIndexLt
                  have indexCases :
                      literalIndex = 0 ∨ literalIndex = 1 ∨
                        literalIndex = 2 := by
                    omega
                  rcases indexCases with indexEq | indexEq | indexEq <;>
                    subst literalIndex <;>
                    simp [DirectedClauseProfile.ofClause, annotatedLiterals,
                      DirectedClauseProfile.ofList, exitFanData,
                      DirectedClauseProfile.taggedLiterals,
                      PositionedPeriodicCNF.clauseExitFanData]
              | cons fourth rest =>
                  simp only [List.length_cons] at width
                  omega

/-- Therefore every active reconstructed extended connector is exactly the
semantic connector used by the inherited Figure 9 route. -/
theorem exitFanData_extendedRoute_ofClause
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (width : clause.literals.length ≤ 3)
    (literalIndex : Nat)
    (literalIndexLt : literalIndex < clause.literals.length) :
    let slot : Fin 3 := ⟨literalIndex, lt_of_lt_of_le literalIndexLt width⟩
    (exitFanData (DirectedClauseProfile.ofClause
        routes clauseIndex clause)).extendedRoute slot =
      (PositionedPeriodicCNF.clauseExitFanData
        clause clauseIndex routes).extendedRoute slot := by
  dsimp only
  have directionEq := exitFanData_direction_ofClause
    routes clauseIndex clause width literalIndex literalIndexLt
  simp only [PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.extendedRoute]
  unfold PlanarOneInThreeNoUnitsFigureNine.ComposedClauseExitFanData.route
  rw [directionEq]

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
