/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceTailData

/-! # Route-tail order for binary clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineSourceTail

open FormulaShapeDirectionOrdering
open PeriodicOrthocrossing
open UnaryProgramClauseProfile

/-- For a two-literal clause, its binary direction profile and its two
presentation-order tails determine the clockwise tail list. -/
theorem orderedTailDirections_eq_of_binary_profile
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable)
    (firstProfile secondProfile : LiteralProfile)
    (firstDirection secondDirection : AxisDirection)
    (firstTail secondTail : List AxisDirection)
    (profileEq :
      DirectedClauseProfile.ofClause routes clauseIndex clause =
        .binary firstProfile firstDirection
          secondProfile secondDirection)
    (lengthEq : clause.literals.length = 2)
    (firstTailEq :
      Gadget.unitSubdivisionDirections
          (routes clauseIndex 0).tail = firstTail)
    (secondTailEq :
      Gadget.unitSubdivisionDirections
          (routes clauseIndex 1).tail = secondTail) :
    orderedTailDirections routes clauseIndex clause =
      if firstDirection.clockwiseRank ≤ secondDirection.clockwiseRank then
        [firstTail, secondTail]
      else
        [secondTail, firstTail] := by
  rcases clause with ⟨position, literals⟩
  dsimp only at lengthEq ⊢
  cases literals with
  | nil => simp at lengthEq
  | cons firstLiteral rest =>
      cases rest with
      | nil => simp at lengthEq
      | cons secondLiteral rest =>
          cases rest with
          | nil =>
              change DirectedClauseProfile.binary
                  (literalProfile firstLiteral)
                  (AxisDirection.polylineFirstDirection
                    (routes clauseIndex 0))
                  (literalProfile secondLiteral)
                  (AxisDirection.polylineFirstDirection
                    (routes clauseIndex 1)) =
                DirectedClauseProfile.binary firstProfile firstDirection
                  secondProfile secondDirection at profileEq
              cases profileEq
              simp [orderedTailDirections, orderedAnnotatedTails,
                annotatedTails, directionLE, AnnotatedTail.key,
                FormulaShapeDirectionOrdering.directionLE,
                firstTailEq, secondTailEq]
              split <;> simp_all
          | cons thirdLiteral rest => simp at lengthEq

end FormulaShapeFigureNineSourceTail
end PeriodicCNF
end LeanTrominoes
