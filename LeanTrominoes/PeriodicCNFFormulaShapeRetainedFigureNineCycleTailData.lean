/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionFinite
import LeanTrominoes.RetainedAngularFanFinalCycleDirections

/-! # Finite local tail table for retained Figure Seven cycle routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineCycleTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNineSourceTail
open FormulaShapeFixedEightDirection
open FormulaShapeRetainedFigureNineDirection
open Gadget
open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT

/-- Finite local Figure Seven incidence annotation with the complete inherited
tail word already expressed in the final physical scale. -/
def localAnnotatedTails
    (clauseIndex : Nat) (clause : PositionedPeriodicClause RingVertex) :
    List AnnotatedTail :=
  clause.literals.zipIdx.map fun taggedLiteral =>
    let route := cycleRoutes clauseIndex taggedLiteral.2
    { profile := literalProfile taggedLiteral.1
      firstDirection := AxisDirection.polylineFirstDirection route
      sourceTailDirections :=
        (unitSubdivisionDirections
          (scalePolyline retainedTerminalFanRoutingRefinement route)).tail }

/-- Stable clockwise dynamic tails of one local Figure Seven clause. -/
def localOrderedTailDirections
    (clauseIndex : Nat) (clause : PositionedPeriodicClause RingVertex) :
    List (List AxisDirection) :=
  ((localAnnotatedTails clauseIndex clause).insertionSort
      FormulaShapeFigureNineSourceTail.directionLE).map
    AnnotatedTail.sourceTailDirections

private theorem annotatedTail_ext
    (first second : AnnotatedTail)
    (profile : first.profile = second.profile)
    (firstDirection : first.firstDirection = second.firstDirection)
    (tail : first.sourceTailDirections = second.sourceTailDirections) :
    first = second := by
  cases first
  cases second
  simp_all

/-- One constant tail-table block for the nine local implication clauses. -/
def localTailTables : List (List (List AxisDirection)) :=
  localCycleFormula.clauses.zipIdx.map fun taggedClause =>
    localOrderedTailDirections taggedClause.2 taggedClause.1

@[simp] theorem localTailTables_length :
    localTailTables.length = FormulaShapeFixedEight.copiesPerVariable := by
  simp [localTailTables, localCycleFormula,
    OccurrenceSplitRing.cycleFormula,
    OccurrenceSplitRing.presentedCycleVertices,
    OccurrenceSplitRing.cycleVertices,
    FormulaShapeFixedEight.copiesPerVariable]

/-- For one genuine source atom and local clause, the public normalized route
family yields exactly the common finite annotated-tail list. -/
theorem annotatedTails_scaledPositionedLocalCycleClause_eq_local
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (atomMember :
      atom ∈ sourceVariables (sourceScaledForFigureSeven source).erase)
    {embeddedClause : EmbeddedClause RingVertex}
    {localClauseIndex : Nat}
    (embeddedMember :
      (embeddedClause, localClauseIndex) ∈ cycleFormula.zipIdx) :
    let actualClause :=
      (positionedLocalCycleClause
        (placementScaledForFigureSeven source) atom embeddedClause).scale
          retainedTerminalFanRoutingRefinement
    annotatedTails
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (copiedClauseCount source +
          (cycleBlockStart
              (sourceVariables (sourceScaledForFigureSeven source).erase)
              atom + localClauseIndex))
        actualClause =
      localAnnotatedTails localClauseIndex
        (localCycleClause embeddedClause) := by
  dsimp only
  let actualClause :=
    (positionedLocalCycleClause
      (placementScaledForFigureSeven source) atom embeddedClause).scale
        retainedTerminalFanRoutingRefinement
  have localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor atom).length := by
    simpa [OccurrenceSplitRing.cycleClausesFor_eq_cycleFormula] using
      List.snd_lt_of_mem_zipIdx embeddedMember
  have globalClauseMember :
      (positionedLocalCycleClause
          (placementScaledForFigureSeven source) atom embeddedClause,
        cycleBlockStart
            (sourceVariables (sourceScaledForFigureSeven source).erase)
            atom + localClauseIndex) ∈
        (allCycleClauses
          (sourceScaledForFigureSeven source)
          (placementScaledForFigureSeven source)).zipIdx :=
    positionedLocalCycleClause_mem_at_cycleBlockStart
      (sourceScaledForFigureSeven source)
      (placementScaledForFigureSeven source)
      atom atomMember embeddedMember
  unfold annotatedTails localAnnotatedTails
  apply List.ext_getElem
  · simp [localCycleClause,
      positionedLocalCycleClause, periodicCycleClause]
  · intro literalIndex leftBound rightBound
    have embeddedLiteralIndexLt :
        literalIndex < embeddedClause.literals.length := by
      simpa [localCycleClause] using rightBound
    have actualLiteralIndexLt :
        literalIndex < actualClause.literals.length := by
      simpa [actualClause, positionedLocalCycleClause,
        periodicCycleClause] using embeddedLiteralIndexLt
    let actualLiteral :=
      actualClause.literals[literalIndex]'actualLiteralIndexLt
    have actualLiteralMember :
        (actualLiteral, literalIndex) ∈ actualClause.literals.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
      exact ⟨actualLiteralIndexLt, rfl⟩
    have firstDirection :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycleBlockStart_firstDirection
        source atom atomMember localClauseIndex literalIndex
        localIndex globalClauseMember actualLiteralMember
    have tailDirections :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycleBlockStart_tailDirections
        source atom atomMember localClauseIndex literalIndex
        localIndex globalClauseMember actualLiteralMember
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    apply annotatedTail_ext
    · simp [localCycleClause,
        positionedLocalCycleClause, periodicCycleClause, literalProfile]
      intro equal
      have firstCoordinate := congrArg Prod.fst equal
      norm_num at firstCoordinate
    · simpa [actualClause, copiedClauseCount,
        sourceScaledForFigureSeven, placementScaledForFigureSeven,
        routesScaledForFigureSeven, occurrencePortsForFigureSeven] using
        firstDirection
    · simpa [actualClause, copiedClauseCount,
        sourceScaledForFigureSeven, placementScaledForFigureSeven,
        routesScaledForFigureSeven, occurrencePortsForFigureSeven] using
        tailDirections

/-- Stable sorting therefore produces the same finite clockwise tail row for
each actual positioned cycle clause. -/
theorem orderedTailDirections_scaledPositionedLocalCycleClause_eq_local
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (atomMember :
      atom ∈ sourceVariables (sourceScaledForFigureSeven source).erase)
    {embeddedClause : EmbeddedClause RingVertex}
    {localClauseIndex : Nat}
    (embeddedMember :
      (embeddedClause, localClauseIndex) ∈ cycleFormula.zipIdx) :
    let actualClause :=
      (positionedLocalCycleClause
        (placementScaledForFigureSeven source) atom embeddedClause).scale
          retainedTerminalFanRoutingRefinement
    orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (copiedClauseCount source +
          (cycleBlockStart
              (sourceVariables (sourceScaledForFigureSeven source).erase)
              atom + localClauseIndex))
        actualClause =
      localOrderedTailDirections localClauseIndex
        (localCycleClause embeddedClause) := by
  dsimp only
  unfold orderedTailDirections orderedAnnotatedTails
    localOrderedTailDirections
  rw [annotatedTails_scaledPositionedLocalCycleClause_eq_local
    source atom atomMember embeddedMember]

/-- Every genuine indexed source-variable block reduces to the same constant
nine-clause local tail table. -/
theorem indexedCycleTailTableBlock_eq_local
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {taggedAtom : WrappedPeriodicPlanarSATVariable Variable × Nat}
    (atomMember :
      taggedAtom ∈
        (sourceVariables
          (sourceScaledForFigureSeven source).erase).zipIdx) :
    FormulaShapeRetainedFigureNineSourceTail.indexedCycleTailTableBlock
        source taggedAtom =
      localTailTables := by
  let atoms :=
    sourceVariables (sourceScaledForFigureSeven source).erase
  have atomsNodup : atoms.Nodup := by
    unfold atoms PeriodicThreeSATThree.sourceVariables
    exact List.nodup_dedup _
  have blockStartEq :=
    cycleBlockStart_eq_copiesPerVariable_mul_index
      atoms atomsNodup atomMember
  rcases taggedAtom with ⟨atom, atomIndex⟩
  unfold FormulaShapeRetainedFigureNineSourceTail.indexedCycleTailTableBlock
    localTailTables localCycleFormula
  dsimp only
  rw [PeriodicEightOccurrenceSplitPositioned.cycleClausesFor_eq_cycleFormula,
    List.map_map, List.zipIdx_map, List.zipIdx_map,
    List.map_map, List.map_map]
  rw [List.zipIdx_eq_map_add, List.map_map]
  apply List.map_congr_left
  rintro ⟨embeddedClause, localClauseIndex⟩ embeddedMember
  simpa [atoms, blockStartEq, Nat.add_assoc] using
    orderedTailDirections_scaledPositionedLocalCycleClause_eq_local
      source atom
      (List.fst_mem_of_mem_zipIdx atomMember)
      embeddedMember

/-- The complete semantic cycle-tail suffix is one copy of the constant local
table for every retained source variable. -/
theorem cycleTailTables_eq_finite
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShapeRetainedFigureNineSourceTail.cycleTailTables source =
      (sourceVariables
        (sourceScaledForFigureSeven source).erase).flatMap
          (fun _ => localTailTables) := by
  rw [FormulaShapeRetainedFigureNineSourceTail.cycleTailTables_eq_indexedBlocks]
  let atoms :=
    sourceVariables (sourceScaledForFigureSeven source).erase
  have indexedEq :
      atoms.zipIdx.flatMap
          (FormulaShapeRetainedFigureNineSourceTail.indexedCycleTailTableBlock
            source) =
        atoms.zipIdx.flatMap (fun _ => localTailTables) := by
    exact List.flatMap_congr
      (l := atoms.zipIdx)
      (f := FormulaShapeRetainedFigureNineSourceTail.indexedCycleTailTableBlock
        source)
      (g := fun _ => localTailTables) (by
        intro taggedAtom member
        exact indexedCycleTailTableBlock_eq_local source member)
  exact indexedEq.trans
    (FormulaShapeRetainedFigureNineDirection.zipIdx_flatMap_const
      atoms localTailTables)

/-- Constant finite flat record block for one retained variable's complete
Figure Seven implication ring. -/
def localRecordTokens :
    List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token :=
  FormulaShapeFigureNinePolarityRouteTailRecord.sourceRecordTokens
    FormulaShapeFixedEightDirection.cycleClauseDescriptors
    localTailTables

private theorem localTailTables_length_eq_clauseCount :
    localTailTables.length =
      FormulaShapeFigureNinePolarityRouteTailRecord.sourceClauseCount
        FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  rw [localTailTables_length]
  native_decide

/-- Pairing the repeated finite descriptor and tail-table streams commutes
with their shared variable-block boundary. -/
theorem sourceRecordTokens_repeatedCycleBlocks {Value : Type}
    (values : List Value) :
    FormulaShapeFigureNinePolarityRouteTailRecord.sourceRecordTokens
        (values.flatMap fun _ =>
          FormulaShapeFixedEightDirection.cycleClauseDescriptors)
        (values.flatMap fun _ => localTailTables) =
      values.flatMap fun _ => localRecordTokens := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.flatMap_cons]
      rw [FormulaShapeFigureNinePolarityRouteTailRecord.sourceRecordTokens_append
        FormulaShapeFixedEightDirection.cycleClauseDescriptors
        (values.flatMap fun _ =>
          FormulaShapeFixedEightDirection.cycleClauseDescriptors)
        localTailTables (values.flatMap fun _ => localTailTables)
        localTailTables_length_eq_clauseCount]
      rw [induction]
      rfl

/-- The semantic cycle-record suffix is the constant finite local record block
repeated once per stable retained source variable. -/
theorem cycleRecordTokens_eq_finite
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShapeRetainedFigureNineSourceTailRecord.cycleRecordTokens source =
      (sourceVariables
        (sourceScaledForFigureSeven source).erase).flatMap
          (fun _ => localRecordTokens) := by
  unfold FormulaShapeRetainedFigureNineSourceTailRecord.cycleRecordTokens
  rw [FormulaShapeRetainedFigureNineDirection.routedCycleClauseDescriptors_eq_finiteCycleClauseDescriptors]
  unfold FormulaShapeRetainedFigureNineDirection.finiteCycleClauseDescriptors
  rw [cycleTailTables_eq_finite]
  exact sourceRecordTokens_repeatedCycleBlocks _

end FormulaShapeRetainedFigureNineCycleTail
end PeriodicCNF
end LeanTrominoes
