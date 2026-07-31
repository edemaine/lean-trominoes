import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoicePairs
import LeanTrominoes.RetainedAngularFanDirectSourceSpokeSeparation

/-!
# Figure 7 spokes for checked direct-source route choices

A checked direct-source choice positions both its coordinated prefix and
the Figure 7 spoke centered at that prefix's selected local endpoint.  This
module lifts the finite prefix--spoke certificate through the common
component translation and then through the raw metadata selector.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- The Figure 7 spoke selected by a checked direct-source choice, positioned
in the choice's physical component coordinates. -/
def RetainedDirectSourceRouteChoice.figure7Spoke
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) : List Cell :=
  translatePolyline
    (retainedDirectSourceFanPositioningOffset choice.origin)
    (retainedDirectSourceFigure7SpokeAt
      choice.kind choice.index slot)

/-- A metadata-selected atlas pair inherits both directed prefix--spoke
separation statements after positioning at a common component origin. -/
theorem
    RetainedDirectSourcePrefixPairSelection.positionedCompleteRoutes_crossFigure7Spokes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (origin : Cell)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesStrictlyAvoidEachOther
        (retainedDirectSourcePositionedFanCompleteRouteAt
          origin selection.kind selection.firstIndex firstSlot)
        (translatePolyline
          (retainedDirectSourceFanPositioningOffset origin)
          (retainedDirectSourceFigure7SpokeAt
            selection.kind selection.secondIndex secondSlot)) ∧
      RoutesStrictlyAvoidEachOther
        (translatePolyline
          (retainedDirectSourceFanPositioningOffset origin)
          (retainedDirectSourceFigure7SpokeAt
            selection.kind selection.firstIndex firstSlot))
        (retainedDirectSourcePositionedFanCompleteRouteAt
          origin selection.kind selection.secondIndex secondSlot) := by
  have separated :=
    retainedDirectSourceFanCompleteRoutes_crossSpokes_strictlyAvoid
      selection.kind selection.firstIndex selection.secondIndex
      selection.indicesDifferent firstSlot secondSlot
  exact
    ⟨separated.1.map_add
        (retainedDirectSourceFanPositioningOffset origin),
      separated.2.map_add
        (retainedDirectSourceFanPositioningOffset origin)⟩

/-- Successful checked choices for distinct literals of one raw direct
source have both directed prefix--spoke interactions strictly separated. -/
theorem retainedDirectSourceRouteChoices_crossFigure7Spokes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (source : DrawingPlanarSATClauseSource Variable)
    (firstLiteralIndex secondLiteralIndex : Nat)
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    (firstLookup :
      retainedDirectSourceRouteChoice?
          formula source firstLiteralIndex =
        some firstChoice)
    (secondLookup :
      retainedDirectSourceRouteChoice?
          formula source secondLiteralIndex =
        some secondChoice)
    (firstMatches :
      firstChoice.Matches formula source firstLiteralIndex)
    (secondMatches :
      secondChoice.Matches formula source secondLiteralIndex)
    (indicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesStrictlyAvoidEachOther
        (firstChoice.completeRoute firstSlot)
        (secondChoice.figure7Spoke secondSlot) ∧
      RoutesStrictlyAvoidEachOther
        (firstChoice.figure7Spoke firstSlot)
        (secondChoice.completeRoute secondSlot) := by
  cases source with
  | crossover crossing localClauseIndex =>
      simp only [retainedDirectSourceRouteChoice?] at firstLookup secondLookup
      split at firstLookup
      next localClauseIndexLt =>
        simp only [localClauseIndexLt, ↓reduceDIte] at secondLookup
        split at firstLookup
        next firstLiteralIndexLt =>
          simp only [Option.some.injEq] at firstLookup
          subst firstChoice
          split at secondLookup
          next secondLiteralIndexLt =>
            simp only [Option.some.injEq] at secondLookup
            subst secondChoice
            let kind : RetainedDirectClauseKind :=
              .crossover ⟨localClauseIndex, localClauseIndexLt⟩
            let firstIndex :
                Fin (retainedDirectSourcePrefixChoices kind).length :=
              ⟨firstLiteralIndex, firstLiteralIndexLt⟩
            let secondIndex :
                Fin (retainedDirectSourcePrefixChoices kind).length :=
              ⟨secondLiteralIndex, secondLiteralIndexLt⟩
            let selection :
                RetainedDirectSourcePrefixPairSelection
                  formula (.crossover crossing localClauseIndex)
                  firstLiteralIndex secondLiteralIndex := {
              kind := kind
              firstIndex := firstIndex
              secondIndex := secondIndex
              indicesDifferent := by
                intro equal
                exact indicesDifferent (congrArg Fin.val equal)
              firstDirection_eq := by
                simpa [RetainedDirectSourceRouteChoice.Matches,
                  DrawingPlanarSATClauseSource.incidenceDrawing,
                  DrawingPlanarSATClauseSource.localClauseIndex,
                  kind, firstIndex] using firstMatches
              secondDirection_eq := by
                simpa [RetainedDirectSourceRouteChoice.Matches,
                  DrawingPlanarSATClauseSource.incidenceDrawing,
                  DrawingPlanarSATClauseSource.localClauseIndex,
                  kind, secondIndex] using secondMatches
            }
            simpa [RetainedDirectSourceRouteChoice.completeRoute,
              RetainedDirectSourceRouteChoice.figure7Spoke,
              selection, kind, firstIndex, secondIndex] using
              selection.positionedCompleteRoutes_crossFigure7Spokes_strictlyAvoid
                (crossingMacroOrigin crossing) firstSlot secondSlot
          next => contradiction
        next => contradiction
      next => contradiction
  | carrier link localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at firstLookup
  | bend routeBend localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at firstLookup
  | routedClause site =>
      simp only [retainedDirectSourceRouteChoice?] at firstLookup secondLookup
      split at firstLookup
      next firstLiteralIndexLt =>
        simp only [Option.some.injEq] at firstLookup
        subst firstChoice
        split at secondLookup
        next secondLiteralIndexLt =>
          simp only [Option.some.injEq] at secondLookup
          subst secondChoice
          let firstPortIndex :
              Fin (routedClausePortLiterals formula site).length :=
            ⟨firstLiteralIndex, firstLiteralIndexLt⟩
          let secondPortIndex :
              Fin (routedClausePortLiterals formula site).length :=
            ⟨secondLiteralIndex, secondLiteralIndexLt⟩
          let firstArm :=
            ((routedClausePortLiterals formula site).get
              firstPortIndex).1
          let secondArm :=
            ((routedClausePortLiterals formula site).get
              secondPortIndex).1
          have armsDifferent : firstArm ≠ secondArm := by
            intro armsEqual
            let firstMappedIndex :
                Fin ((routedClausePortLiterals
                  formula site).map Prod.fst).length :=
              ⟨firstLiteralIndex, by
                simpa using firstLiteralIndexLt⟩
            let secondMappedIndex :
                Fin ((routedClausePortLiterals
                  formula site).map Prod.fst).length :=
              ⟨secondLiteralIndex, by
                simpa using secondLiteralIndexLt⟩
            have mappedValuesEqual :
                ((routedClausePortLiterals
                  formula site).map Prod.fst).get firstMappedIndex =
                ((routedClausePortLiterals
                  formula site).map Prod.fst).get secondMappedIndex := by
              simpa [firstMappedIndex, secondMappedIndex,
                firstArm, secondArm, firstPortIndex,
                secondPortIndex] using armsEqual
            have mappedIndicesEqual :
                firstMappedIndex = secondMappedIndex :=
              (routedClausePortLiterals_ports_nodup
                formula degree site).injective_get
                  mappedValuesEqual
            exact indicesDifferent
              (congrArg Fin.val mappedIndicesEqual)
          let firstIndex :=
            retainedDirectRoutedClauseArmIndex firstArm
          let secondIndex :=
            retainedDirectRoutedClauseArmIndex secondArm
          let selection :
              RetainedDirectSourcePrefixPairSelection
                formula (.routedClause site)
                firstLiteralIndex secondLiteralIndex := {
            kind := .routedClause
            firstIndex := firstIndex
            secondIndex := secondIndex
            indicesDifferent := by
              intro equal
              exact armsDifferent
                (retainedDirectRoutedClauseArmIndex_injective equal)
            firstDirection_eq := by
              simpa [RetainedDirectSourceRouteChoice.Matches,
                DrawingPlanarSATClauseSource.incidenceDrawing,
                DrawingPlanarSATClauseSource.localClauseIndex,
                firstArm, firstPortIndex, firstIndex] using firstMatches
            secondDirection_eq := by
              simpa [RetainedDirectSourceRouteChoice.Matches,
                DrawingPlanarSATClauseSource.incidenceDrawing,
                DrawingPlanarSATClauseSource.localClauseIndex,
                secondArm, secondPortIndex, secondIndex] using secondMatches
          }
          simpa [RetainedDirectSourceRouteChoice.completeRoute,
            RetainedDirectSourceRouteChoice.figure7Spoke,
            selection, firstArm, secondArm, firstPortIndex,
            secondPortIndex, firstIndex, secondIndex] using
            selection.positionedCompleteRoutes_crossFigure7Spokes_strictlyAvoid
              (routedClauseOrigin formula site) firstSlot secondSlot
        next => contradiction
      next => contradiction
  | routedVariable site armIndex arm link localClauseIndex =>
      simp only [retainedDirectSourceRouteChoice?] at firstLookup secondLookup
      split at firstLookup
      next localClauseIndexLt =>
        simp only [localClauseIndexLt, ↓reduceDIte] at secondLookup
        split at firstLookup
        next firstLiteralIndexLt =>
          simp only [Option.some.injEq] at firstLookup
          subst firstChoice
          split at secondLookup
          next secondLiteralIndexLt =>
            simp only [Option.some.injEq] at secondLookup
            subst secondChoice
            let kind : RetainedDirectClauseKind :=
              .duplicator arm ⟨localClauseIndex, localClauseIndexLt⟩
            let firstIndex :
                Fin (retainedDirectSourcePrefixChoices kind).length :=
              ⟨firstLiteralIndex, firstLiteralIndexLt⟩
            let secondIndex :
                Fin (retainedDirectSourcePrefixChoices kind).length :=
              ⟨secondLiteralIndex, secondLiteralIndexLt⟩
            let selection :
                RetainedDirectSourcePrefixPairSelection
                  formula
                  (.routedVariable
                    site armIndex arm link localClauseIndex)
                  firstLiteralIndex secondLiteralIndex := {
              kind := kind
              firstIndex := firstIndex
              secondIndex := secondIndex
              indicesDifferent := by
                intro equal
                exact indicesDifferent (congrArg Fin.val equal)
              firstDirection_eq := by
                simpa [RetainedDirectSourceRouteChoice.Matches,
                  DrawingPlanarSATClauseSource.incidenceDrawing,
                  DrawingPlanarSATClauseSource.localClauseIndex,
                  kind, firstIndex] using firstMatches
              secondDirection_eq := by
                simpa [RetainedDirectSourceRouteChoice.Matches,
                  DrawingPlanarSATClauseSource.incidenceDrawing,
                  DrawingPlanarSATClauseSource.localClauseIndex,
                  kind, secondIndex] using secondMatches
            }
            simpa [RetainedDirectSourceRouteChoice.completeRoute,
              RetainedDirectSourceRouteChoice.figure7Spoke,
              selection, kind, firstIndex, secondIndex] using
              selection.positionedCompleteRoutes_crossFigure7Spokes_strictlyAvoid
                (routedVariableOrigin formula site)
                firstSlot secondSlot
          next => contradiction
        next => contradiction
      next => contradiction

end PeriodicEightOccurrenceSplit
end LeanTrominoes
