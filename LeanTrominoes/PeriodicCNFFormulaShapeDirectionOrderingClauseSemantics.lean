/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingSemantics
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-! # Clause semantics of finite direction-aware shape ordering -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

open ClauseProfileOccurrenceSplit

theorem DirectedClauseProfile.taggedLiterals_ofList
    (items : List (UnaryProgramClauseProfile.LiteralProfile × AxisDirection))
    (nonempty : items ≠ []) (width : items.length ≤ 3) :
    (DirectedClauseProfile.ofList items).taggedLiterals = items := by
  cases items with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil => cases first; rfl
      | cons second rest =>
          cases rest with
          | nil => cases first; cases second; rfl
          | cons third rest =>
              cases rest with
              | nil => cases first; cases second; cases third; rfl
              | cons fourth rest =>
                  simp only [List.length_cons] at width
                  omega

@[simp] theorem annotatedLiterals_length {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    (annotatedLiterals routes clauseIndex clause).length =
      clause.literals.length := by
  simp [annotatedLiterals]

theorem DirectedClauseProfile.ofClause_taggedLiterals
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    (DirectedClauseProfile.ofClause routes clauseIndex clause).taggedLiterals =
      annotatedLiterals routes clauseIndex clause := by
  apply DirectedClauseProfile.taggedLiterals_ofList
  · simpa [annotatedLiterals] using nonempty
  · simpa only [annotatedLiterals_length] using width

/-- Sorting the finite annotated profile uses exactly the same comparison and
stable order as sorting the source clause's tagged literals. -/
theorem DirectedClauseProfile.orderedLiterals_ofClause
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    (DirectedClauseProfile.ofClause
        routes clauseIndex clause).orderedLiterals =
      literalProfiles
        (PositionedPeriodicCNF.orderClauseByRouteDirection
          routes clauseIndex clause).literals := by
  let annotate : PeriodicLiteral Variable × Nat →
      UnaryProgramClauseProfile.LiteralProfile × AxisDirection :=
    fun taggedLiteral =>
      (literalProfile taggedLiteral.1,
        AxisDirection.polylineFirstDirection
          (routes clauseIndex taggedLiteral.2))
  have mappedSort := List.map_insertionSort
    (r := PositionedPeriodicCNF.clauseLiteralDirectionLE
      (Variable := Variable) routes clauseIndex)
    (s := directionLE) annotate clause.literals.zipIdx (by
      intro first firstMember second secondMember
      simp [PositionedPeriodicCNF.clauseLiteralDirectionLE,
        PositionedPeriodicCNF.clauseLiteralDirectionRank,
        directionLE, annotate])
  have mappedProfiles := congrArg (List.map Prod.fst) mappedSort
  unfold DirectedClauseProfile.orderedLiterals
  rw [DirectedClauseProfile.ofClause_taggedLiterals
    routes clauseIndex clause nonempty width]
  change
    ((clause.literals.zipIdx.map annotate).insertionSort
      directionLE).map Prod.fst = _
  rw [← mappedProfiles]
  simp only [List.map_map]
  unfold PositionedPeriodicCNF.orderClauseByRouteDirection
    PositionedPeriodicCNF.clauseLiteralOrder literalProfiles
  rw [List.map_map]
  rfl

@[simp] theorem DirectedClauseProfile.orderedProfile_ofClause_literals
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    (DirectedClauseProfile.ofClause
        routes clauseIndex clause).orderedProfile.literals =
      literalProfiles
        (PositionedPeriodicCNF.orderClauseByRouteDirection
          routes clauseIndex clause).literals := by
  rw [DirectedClauseProfile.orderedProfile_literals]
  exact DirectedClauseProfile.orderedLiterals_ofClause
    routes clauseIndex clause nonempty width

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
