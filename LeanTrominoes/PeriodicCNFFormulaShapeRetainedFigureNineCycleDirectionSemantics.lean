/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionData
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockClause
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockStartFixed
import LeanTrominoes.RetainedAngularFanFinalCycleFirstDirections

/-! # Finite semantics of retained Figure 9 implication-cycle directions -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT
open OccurrenceSplitRing

/-- At a genuine stable source-variable index, the index-based and atom-based
views of the final routed Figure 7 block are identical. -/
theorem routedCycleClauseDescriptorsAt_eq_for
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {atom : WrappedPeriodicPlanarSATVariable Variable}
    {atomIndex : Nat}
    (atomMember :
      (atom, atomIndex) ∈
        (sourceVariables
          (sourceScaledForFigureSeven source).erase).zipIdx) :
    routedCycleClauseDescriptorsAt source atomIndex =
      routedCycleClauseDescriptorsFor source atom := by
  let atoms :=
    sourceVariables (sourceScaledForFigureSeven source).erase
  have atomsNodup : atoms.Nodup := by
    unfold atoms PeriodicThreeSATThree.sourceVariables
    exact List.nodup_dedup _
  have blockStartEq :=
    cycleBlockStart_eq_copiesPerVariable_mul_index
      atoms atomsNodup atomMember
  have routesEq :
      routedCycleRoutesAt source atomIndex =
        routedCycleRoutesFor source atom := by
    funext localClauseIndex literalIndex
    simp [routedCycleRoutesAt, routedCycleRoutesFor, atoms, blockStartEq]
  unfold routedCycleClauseDescriptorsAt
    routedCycleClauseDescriptorsFor
  rw [routesEq]

/-- One genuine source atom's globally indexed final cycle descriptor block
is exactly the common finite local Figure 7 descriptor block. -/
theorem routedCycleClauseDescriptorsFor_eq_cycleClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (atomMember :
      atom ∈ sourceVariables
        (sourceScaledForFigureSeven source).erase) :
    routedCycleClauseDescriptorsFor source atom =
      FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  unfold routedCycleClauseDescriptorsFor
    FormulaShapeFixedEightDirection.cycleClauseDescriptors
  apply List.map_congr_left
  rintro ⟨localClause, localClauseIndex⟩ localClauseMember
  have embeddedMember := localClauseMember
  rw [FormulaShapeFixedEightDirection.localCycleFormula,
    List.zipIdx_map] at embeddedMember
  rcases List.mem_map.mp embeddedMember with
    ⟨taggedEmbedded, taggedEmbeddedMember, taggedEmbeddedEq⟩
  have localClauseIndexEq :
      taggedEmbedded.2 = localClauseIndex :=
    congrArg Prod.snd taggedEmbeddedEq
  have localClauseEq :
      FormulaShapeFixedEightDirection.localCycleClause taggedEmbedded.1 =
        localClause :=
    congrArg Prod.fst taggedEmbeddedEq
  subst localClauseIndex
  subst localClause
  let actualClause :=
    positionedLocalCycleClause
      (placementScaledForFigureSeven source) atom taggedEmbedded.1
  have localIndex :
      taggedEmbedded.2 <
        (PeriodicEightOccurrenceSplit.cycleClausesFor atom).length := by
    simpa [OccurrenceSplitRing.cycleClausesFor_eq_cycleFormula] using
      List.snd_lt_of_mem_zipIdx taggedEmbeddedMember
  have globalClauseMember :
      (actualClause,
          cycleBlockStart
              (sourceVariables
                (sourceScaledForFigureSeven source).erase)
              atom +
            taggedEmbedded.2) ∈
        (allCycleClauses
          (sourceScaledForFigureSeven source)
          (placementScaledForFigureSeven source)).zipIdx := by
    exact positionedLocalCycleClause_mem_at_cycleBlockStart
      (sourceScaledForFigureSeven source)
      (placementScaledForFigureSeven source)
      atom atomMember taggedEmbeddedMember
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  unfold FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zipIdx]
  · intro literalIndex leftBound rightBound
    have literalIndexLt :
        literalIndex < taggedEmbedded.1.literals.length := by
      simpa [FormulaShapeFixedEightDirection.localCycleClause] using
        rightBound
    have actualLiteralIndexLt :
        literalIndex < actualClause.literals.length := by
      simpa [actualClause, positionedLocalCycleClause,
        periodicCycleClause] using literalIndexLt
    let actualLiteral :=
      actualClause.literals[literalIndex]'actualLiteralIndexLt
    have actualLiteralMember :
        (actualLiteral, literalIndex) ∈
          actualClause.literals.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
      exact ⟨actualLiteralIndexLt, rfl⟩
    have directionEq :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycleBlockStart_firstDirection
        source atom atomMember taggedEmbedded.2 literalIndex
        localIndex globalClauseMember actualLiteralMember
    simp only [FormulaShapeFixedEightDirection.localCycleClause,
      List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    apply Prod.ext
    · rfl
    · simpa [routedCycleRoutesFor, copiedClauseCount,
        sourceScaledForFigureSeven, placementScaledForFigureSeven,
        routesScaledForFigureSeven, occurrencePortsForFigureSeven,
        actualClause] using directionEq

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
