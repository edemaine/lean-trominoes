/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeSourcePrefixSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceCrossClauseOtherTargetSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels

/-!
# Translating final coordinated direct-source routes

A semantic period shift of a final direct route is represented by translating
the checked atlas choice's component origin in the unscaled retained source.
The atlas positioning map then supplies exactly the fully refined physical
translation of the public route.  This keeps translated direct-route proofs
inside the existing finite geometric model.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The physical period translation of the final fixed-eight drawing is the
direct-atlas positioning offset of the corresponding retained-source period
translation. -/
theorem retainedFinalPhysicalTranslation_eq_directSourceFanPositioningOffset
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (relativeTranslate : Cell) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate =
      retainedDirectSourceFanPositioningOffset
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate) := by
  simp [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    retainedAngularFanSourceScaledRefinedPlacement,
    retainedAngularFanRefinedPlacement,
    PeriodicEightOccurrenceSplitPositioned.placement,
    retainedDirectSourceFanPositioningOffset,
    PeriodicVariablePlacement.translation,
    finalCoordinatedPlacement,
    retainedTerminalFanTotalRefinement_eq,
    retainedTerminalFanRoutingRefinement,
    retainedAngularFanSourceClearanceFactor,
    PeriodicEightOccurrenceSplitPositioned.refinementScale, Cell.scale]
  constructor <;> ring

/-- Translating a direct choice's origin translates the two endpoints of its
represented retained source segment. -/
theorem RetainedDirectSourceRouteChoice.translateOrigin_sourceSegment
    (choice : RetainedDirectSourceRouteChoice)
    (offset : Cell) :
    (choice.translateOrigin offset).sourceSegment =
      GridSegment.translate offset choice.sourceSegment := by
  rcases choice with ⟨origin, kind, index⟩
  rcases origin with ⟨originX, originY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [RetainedDirectSourceRouteChoice.translateOrigin,
    RetainedDirectSourceRouteChoice.sourceSegment,
    GridSegment.translate, Cell.add]
  constructor <;> constructor <;> ring

/-- A translated successful direct occurrence is exactly the complete Figure
7 route of the same atlas entry with its origin shifted by the corresponding
retained-source period vector. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoute_translate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (relativeTranslate : Cell) :
    translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choice
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) =
      (choice.translateOrigin
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)).completeFigure7Route
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex) := by
  rw [retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty choice clauseMember literalMember choiceLookup]
  rw [RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route]
  rw [retainedFinalPhysicalTranslation_eq_directSourceFanPositioningOffset]

/-- The same translation model at the public total incidence-route
interface. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_translate_of_choice_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (relativeTranslate : Cell) :
    translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) =
      (choice.translateOrigin
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)).completeFigure7Route
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex) := by
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_completeFigure7Route_of_choice_some
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice clauseMember literalMember choiceLookup]
  rw [RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route]
  rw [retainedFinalPhysicalTranslation_eq_directSourceFanPositioningOffset]

end PeriodicOrthocrossing
end LeanTrominoes
