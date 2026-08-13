/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridors

/-!
# Finite geometry of one three-lane ribbon turn

Global ribbon separation has two parts.  Corridors belonging to distinct
source features are separated by refinement-scale clearance; strands inside
one source corridor reduce to finitely many local direction patterns.

This file certifies the latter kernel.  For every genuine straight or
quarter-turn pattern (immediate reversals are excluded), the standard red,
green, and blue lanes are individually simple and pairwise continuously
separated, including listed-point/interior contacts.
-/

namespace LeanTrominoes

namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- Three source points realizing one local directed straight or turn at
the origin. -/
def standardRibbonTurnSource
    (incoming outgoing : AxisDirection) : List Cell :=
  [Cell.sub (0, 0) incoming.step, (0, 0), outgoing.step]

/-- One standard colored lane through a local direction pattern. -/
def standardRibbonTurnRoute
    (incoming outgoing : AxisDirection)
    (color : WireColor) : List Cell :=
  let factor := standardThreeStrandLayout.factor
  let distance := standardRibbonLaneDistance color
  let sourceStart := Cell.sub (0, 0) incoming.step
  let sourceFinish := outgoing.step
  let first := ribbonPoint factor distance incoming sourceStart
  let incomingAtTurn :=
    ribbonPoint factor distance incoming (0, 0)
  let outgoingAtTurn :=
    ribbonPoint factor distance outgoing (0, 0)
  let middle :=
    ribbonCornerMiddle factor distance (0, 0) incoming outgoing
  let last := ribbonPoint factor distance outgoing sourceFinish
  if incoming = outgoing then
    [first, incomingAtTurn, last]
  else if outgoing = incoming.opposite then
    [first, incomingAtTurn, outgoingAtTurn, last]
  else if incoming.TurnsRight outgoing then
    [first, middle, last]
  else
    [first, incomingAtTurn, middle, outgoingAtTurn, last]

/-- Every standard lane through a legal local source pattern is simple. -/
theorem standardRibbonTurnRoute_simple
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (standardRibbonTurnRoute incoming outgoing color) := by
  cases incoming <;> cases outgoing <;> cases color <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.opposite] <;>
    native_decide

/-- Different colors in one legal local source pattern have exact
continuous separation. -/
theorem standardRibbonTurnRoutes_avoidEachOther
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    {first second : WireColor}
    (different : first ≠ second) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (standardRibbonTurnRoute incoming outgoing first)
      (standardRibbonTurnRoute incoming outgoing second) := by
  cases incoming <;> cases outgoing <;>
    cases first <;> cases second <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.opposite] <;>
    native_decide

/-- The complete local three-lane bundle certificate. -/
def StandardRibbonTurnBundleIsSeparated
    (incoming outgoing : AxisDirection) : Prop :=
  (∀ color,
      LocalIncidenceDrawing.RouteIsSimple
        (standardRibbonTurnRoute incoming outgoing color)) ∧
    ∀ first second,
      first ≠ second →
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          (standardRibbonTurnRoute incoming outgoing first)
          (standardRibbonTurnRoute incoming outgoing second)

theorem standardRibbonTurnBundle_isSeparated
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite) :
    StandardRibbonTurnBundleIsSeparated incoming outgoing :=
  ⟨standardRibbonTurnRoute_simple
      incomingGenuine outgoingGenuine noReverse,
    fun _ _ different =>
      standardRibbonTurnRoutes_avoidEachOther
        incomingGenuine outgoingGenuine noReverse different⟩

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
