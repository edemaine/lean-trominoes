/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.OccurrenceSplitAngularFanSpokeSeparation
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineStrictSeparationCheck
import Mathlib.Tactic.FinCases
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceRouteHull
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceTailSeparation

/-!
# Direct-source prefixes versus Figure 7 spokes

The coordinated direct-source atlas routes each literal from its common
clause gate to the boundary of its selected occurrence macrocell.  This
module places the actual factor-eight Figure 7 spoke at that same local
center and exhaustively certifies both directed cross interactions for
every pair of different atlas entries and every pair of occurrence slots.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The factor-eight Figure 7 spoke centered at the local endpoint of one
direct-source atlas entry. -/
def retainedDirectSourceFigure7SpokeAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : List Cell :=
  translatePolyline
    (Cell.sub
      (retainedDirectSourceFanCenterAt kind index)
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
    (scalePolyline retainedTerminalFanRoutingRefinement
      (spokeRoute (angularPortOfIndex slot.val)))

/-- Both directed prefix--spoke interactions are contact-free for every
pair of different entries in one direct-clause atlas. -/
def RetainedDirectClauseKind.SourceFigure7SpokesCrossSeparated
    (kind : RetainedDirectClauseKind) : Prop :=
  ∀ (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length),
    firstIndex ≠ secondIndex →
    ∀ firstSlot secondSlot : RetainedTerminalSlot,
      RoutesStrictlyAvoidEachOther
          (retainedDirectSourceFanCompleteRouteAt
            kind firstIndex firstSlot)
          (retainedDirectSourceFigure7SpokeAt
            kind secondIndex secondSlot) ∧
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceFigure7SpokeAt
            kind firstIndex firstSlot)
          (retainedDirectSourceFanCompleteRouteAt
            kind secondIndex secondSlot)

instance (kind : RetainedDirectClauseKind) :
    Decidable kind.SourceFigure7SpokesCrossSeparated := by
  unfold
    RetainedDirectClauseKind.SourceFigure7SpokesCrossSeparated
  let firstDecidable :
      ∀ firstIndex :
        Fin (retainedDirectSourcePrefixChoices kind).length,
        Decidable
          (∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            firstIndex ≠ secondIndex →
            ∀ firstSlot secondSlot : RetainedTerminalSlot,
              RoutesStrictlyAvoidEachOther
                  (retainedDirectSourceFanCompleteRouteAt
                    kind firstIndex firstSlot)
                  (retainedDirectSourceFigure7SpokeAt
                    kind secondIndex secondSlot) ∧
                RoutesStrictlyAvoidEachOther
                  (retainedDirectSourceFigure7SpokeAt
                    kind firstIndex firstSlot)
                  (retainedDirectSourceFanCompleteRouteAt
                    kind secondIndex secondSlot)) :=
    fun firstIndex => by
      letI :
          ∀ secondIndex :
            Fin (retainedDirectSourcePrefixChoices kind).length,
            Decidable
              (firstIndex ≠ secondIndex →
              ∀ firstSlot secondSlot : RetainedTerminalSlot,
                RoutesStrictlyAvoidEachOther
                    (retainedDirectSourceFanCompleteRouteAt
                      kind firstIndex firstSlot)
                    (retainedDirectSourceFigure7SpokeAt
                      kind secondIndex secondSlot) ∧
                  RoutesStrictlyAvoidEachOther
                    (retainedDirectSourceFigure7SpokeAt
                      kind firstIndex firstSlot)
                    (retainedDirectSourceFanCompleteRouteAt
                      kind secondIndex secondSlot)) :=
        fun _ => inferInstance
      exact Fintype.decidableForallFintype
  letI := firstDecidable
  exact Fintype.decidableForallFintype

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private def spokeSeparationNormals (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length) : List Cell :=
  [(1, 0), (0, 1), (1, 1), (1, -1)] ++
    retainedDirectSourcePairCandidateNormals kind firstIndex secondIndex

private def spokeSeparationCheck (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length)
    (firstSlot secondSlot : RetainedTerminalSlot) : Bool :=
  let first := retainedDirectSourceCompleteRouteHull kind firstIndex firstSlot
  let second := retainedDirectSourceFigure7SpokeAt kind secondIndex secondSlot
  (spokeSeparationNormals kind firstIndex secondIndex).any fun normal =>
    decide (routeLinearMaximum normal first < routeLinearMinimum normal second ∨
      routeLinearMaximum normal second < routeLinearMinimum normal first)

private theorem spokeSeparationCheck_sound (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (checked : spokeSeparationCheck kind firstIndex secondIndex firstSlot secondSlot = true) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceFanCompleteRouteAt kind firstIndex firstSlot)
      (retainedDirectSourceFigure7SpokeAt kind secondIndex secondSlot) := by
  simp only [spokeSeparationCheck, List.any_eq_true, decide_eq_true_eq] at checked
  obtain ⟨normal, _, separated⟩ := checked
  let hull := retainedDirectSourceCompleteRouteHull kind firstIndex firstSlot
  let spoke := retainedDirectSourceFigure7SpokeAt kind secondIndex secondSlot
  have bounded (p : Cell)
      (hp : p ∈ retainedDirectSourceFanCompleteRouteAt kind firstIndex firstSlot) :=
    retainedDirectSourceCompleteRouteHull_linearBounds kind firstIndex firstSlot
      normal (routeLinearMinimum normal hull) (routeLinearMaximum normal hull)
      (fun p hp => ⟨routeLinearMinimum_le_linearValue normal hull hp,
        linearValue_le_routeLinearMaximum normal hull hp⟩) hp
  rcases separated with before | after
  · exact routesStrictlyAvoidEachOther_of_linear_separated normal (routeLinearMaximum normal hull)
      (fun p hp => (bounded p hp).2)
      (fun p hp => lt_of_lt_of_le before (routeLinearMinimum_le_linearValue normal spoke hp))
  · exact (routesStrictlyAvoidEachOther_of_linear_separated normal (routeLinearMaximum normal spoke)
      (fun p hp => linearValue_le_routeLinearMaximum normal spoke hp)
      (fun p hp => lt_of_lt_of_le after (bounded p hp).1)).symm

private def crossSpokesCheck (kind : RetainedDirectClauseKind) : Bool :=
  finiteAll fun firstIndex : Fin (retainedDirectSourcePrefixChoices kind).length =>
    finiteAll fun secondIndex : Fin (retainedDirectSourcePrefixChoices kind).length =>
      guardedCheck (firstIndex ≠ secondIndex)
        (finiteAll fun firstSlot : RetainedTerminalSlot =>
          finiteAll fun secondSlot : RetainedTerminalSlot =>
            spokeSeparationCheck kind firstIndex secondIndex firstSlot secondSlot)

private theorem crossSpokesCheck_correct_case0 :
    crossSpokesCheck (.crossover 0) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case1 :
    crossSpokesCheck (.crossover 1) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case2 :
    crossSpokesCheck (.crossover 2) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case3 :
    crossSpokesCheck (.crossover 3) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case4 :
    crossSpokesCheck (.crossover 4) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case5 :
    crossSpokesCheck (.crossover 5) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case6 :
    crossSpokesCheck (.crossover 6) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case7 :
    crossSpokesCheck (.crossover 7) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case8 :
    crossSpokesCheck (.crossover 8) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case9 :
    crossSpokesCheck (.crossover 9) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case10 :
    crossSpokesCheck (.crossover 10) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case11 :
    crossSpokesCheck (.crossover 11) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case12 :
    crossSpokesCheck (.crossover 12) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case13 :
    crossSpokesCheck (.crossover 13) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case14 :
    crossSpokesCheck (.crossover 14) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case15 :
    crossSpokesCheck (.crossover 15) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case16 :
    crossSpokesCheck (.crossover 16) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case17 :
    crossSpokesCheck (.crossover 17) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case18 :
    crossSpokesCheck (.crossover 18) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case19 :
    crossSpokesCheck (.crossover 19) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case20 :
    crossSpokesCheck (.crossover 20) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case21 :
    crossSpokesCheck (.crossover 21) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case22 :
    crossSpokesCheck (.crossover 22) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case23 :
    crossSpokesCheck (.crossover 23) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case24 :
    crossSpokesCheck (.crossover 24) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case25 :
    crossSpokesCheck (.crossover 25) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case26 :
    crossSpokesCheck (.duplicator .left 0) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case27 :
    crossSpokesCheck (.duplicator .left 1) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case28 :
    crossSpokesCheck (.duplicator .middle 0) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case29 :
    crossSpokesCheck (.duplicator .middle 1) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case30 :
    crossSpokesCheck (.duplicator .right 0) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case31 :
    crossSpokesCheck (.duplicator .right 1) = true := by
  decide +kernel

private theorem crossSpokesCheck_correct_case32 :
    crossSpokesCheck .routedClause = true := by
  decide +kernel

private theorem crossSpokesCheck_correct (kind : RetainedDirectClauseKind) :
    crossSpokesCheck kind = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact crossSpokesCheck_correct_case0
    · exact crossSpokesCheck_correct_case1
    · exact crossSpokesCheck_correct_case2
    · exact crossSpokesCheck_correct_case3
    · exact crossSpokesCheck_correct_case4
    · exact crossSpokesCheck_correct_case5
    · exact crossSpokesCheck_correct_case6
    · exact crossSpokesCheck_correct_case7
    · exact crossSpokesCheck_correct_case8
    · exact crossSpokesCheck_correct_case9
    · exact crossSpokesCheck_correct_case10
    · exact crossSpokesCheck_correct_case11
    · exact crossSpokesCheck_correct_case12
    · exact crossSpokesCheck_correct_case13
    · exact crossSpokesCheck_correct_case14
    · exact crossSpokesCheck_correct_case15
    · exact crossSpokesCheck_correct_case16
    · exact crossSpokesCheck_correct_case17
    · exact crossSpokesCheck_correct_case18
    · exact crossSpokesCheck_correct_case19
    · exact crossSpokesCheck_correct_case20
    · exact crossSpokesCheck_correct_case21
    · exact crossSpokesCheck_correct_case22
    · exact crossSpokesCheck_correct_case23
    · exact crossSpokesCheck_correct_case24
    · exact crossSpokesCheck_correct_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact crossSpokesCheck_correct_case26
      · exact crossSpokesCheck_correct_case27
    | middle =>
      fin_cases index
      · exact crossSpokesCheck_correct_case28
      · exact crossSpokesCheck_correct_case29
    | right =>
      fin_cases index
      · exact crossSpokesCheck_correct_case30
      · exact crossSpokesCheck_correct_case31
  | routedClause => exact crossSpokesCheck_correct_case32

/-- Kernel certificate for the direct-source/Figure 7 cross interactions. -/
theorem retainedDirectSourceFigure7SpokesCrossSeparated :
    ∀ kind : RetainedDirectClauseKind,
      kind.SourceFigure7SpokesCrossSeparated := by
  intro kind firstIndex secondIndex different firstSlot secondSlot
  have checked := crossSpokesCheck_correct kind
  simp only [crossSpokesCheck, finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact ⟨spokeSeparationCheck_sound kind firstIndex secondIndex firstSlot secondSlot
      (checked firstIndex secondIndex different firstSlot secondSlot),
    (spokeSeparationCheck_sound kind secondIndex firstIndex secondSlot firstSlot
      (checked secondIndex firstIndex (Ne.symm different) secondSlot firstSlot)).symm⟩

/-- Public pointwise form of the exhaustive cross-separation certificate. -/
theorem retainedDirectSourceFanCompleteRoutes_crossSpokes_strictlyAvoid
    (kind : RetainedDirectClauseKind)
    (firstIndex secondIndex :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          kind firstIndex firstSlot)
        (retainedDirectSourceFigure7SpokeAt
          kind secondIndex secondSlot) ∧
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFigure7SpokeAt
          kind firstIndex firstSlot)
        (retainedDirectSourceFanCompleteRouteAt
          kind secondIndex secondSlot) :=
  retainedDirectSourceFigure7SpokesCrossSeparated
    kind firstIndex secondIndex indicesDifferent
      firstSlot secondSlot

end PeriodicEightOccurrenceSplit
end LeanTrominoes
