/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelData
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineBinaryTailSemantics

/-! # Binary route-tail order in clockwise-relabeler form -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineSourceTail

open FormulaShapeDirectionOrdering
open PeriodicOrthocrossing
open UnaryProgramClauseProfile

/-- The rank comparison used by semantic clockwise ordering is exactly the
binary formatter's swap predicate. -/
theorem orderedTailDirections_eq_of_binary_profile_swap
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable)
    (firstProfile secondProfile : LiteralProfile)
    (firstDirection secondDirection : AxisDirection)
    (firstTail secondTail : List AxisDirection)
    (profileEq :
      DirectedClauseProfile.ofClause routes clauseIndex clause =
        .binary firstProfile firstDirection secondProfile secondDirection)
    (lengthEq : clause.literals.length = 2)
    (firstTailEq :
      Gadget.unitSubdivisionDirections (routes clauseIndex 0).tail =
        firstTail)
    (secondTailEq :
      Gadget.unitSubdivisionDirections (routes clauseIndex 1).tail =
        secondTail) :
    orderedTailDirections routes clauseIndex clause =
      if BinaryRouteTailRecordClockwiseRelabel.profileNeedsSwap
          (.binary firstProfile firstDirection secondProfile secondDirection)
      then [secondTail, firstTail]
      else [firstTail, secondTail] := by
  rw [orderedTailDirections_eq_of_binary_profile routes clauseIndex clause
    firstProfile secondProfile firstDirection secondDirection
    firstTail secondTail profileEq lengthEq firstTailEq secondTailEq]
  by_cases ordered : firstDirection.clockwiseRank ≤
      secondDirection.clockwiseRank
  · have notSwap : ¬ secondDirection.clockwiseRank <
        firstDirection.clockwiseRank := by omega
    simp [ordered, BinaryRouteTailRecordClockwiseRelabel.profileNeedsSwap,
      notSwap]
  · have swap : secondDirection.clockwiseRank <
        firstDirection.clockwiseRank := by omega
    simp [ordered, BinaryRouteTailRecordClockwiseRelabel.profileNeedsSwap,
      swap]

end FormulaShapeFigureNineSourceTail
end PeriodicCNF
end LeanTrominoes
