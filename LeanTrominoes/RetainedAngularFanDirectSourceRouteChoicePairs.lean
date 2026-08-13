/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice

/-!
# Pairwise separation for checked direct-source route choices

Two distinct literal positions selected from the same direct planar-SAT
source must land in distinct entries of one coordinated finite atlas.  This
module reconstructs that common pair selection from the two independent
total lookups and exposes the atlas's separation theorem for their complete
routes.

The routed-clause case needs the original incidence-degree-three hypothesis:
its port list is duplicate-free, so distinct literal positions select
distinct physical arms.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Successful checked choices for distinct literals of one source have
separated complete routes, with their heads as the only permitted contact. -/
theorem retainedDirectSourceRouteChoices_completeRoutes_separated
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
    RoutesAvoidEachOther
        (firstChoice.completeRoute firstSlot)
        (secondChoice.completeRoute secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (firstChoice.completeRoute firstSlot)
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
              selection, kind, firstIndex, secondIndex] using
              selection.positionedCompleteRoutes_separated
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
            selection, firstArm, secondArm, firstPortIndex,
            secondPortIndex, firstIndex, secondIndex] using
            selection.positionedCompleteRoutes_separated
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
              selection, kind, firstIndex, secondIndex] using
              selection.positionedCompleteRoutes_separated
                (routedVariableOrigin formula site)
                firstSlot secondSlot
          next => contradiction
        next => contradiction
      next => contradiction

end PeriodicEightOccurrenceSplit
end LeanTrominoes
