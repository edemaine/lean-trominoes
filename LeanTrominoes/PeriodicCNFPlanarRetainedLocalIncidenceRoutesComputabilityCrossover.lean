/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityBasic

/-!
# Computability of retained planar-SAT local incidence routes

Proof-free route lookup for the retained crossover, clause, variable, carrier,
and corner gadgets.
-/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PeriodicOrthocrossing

open PlanarThreeSAT

theorem CornerPort.ofDirection_primrec :
    Primrec CornerPort.ofDirection :=
  Primrec.dom_finite CornerPort.ofDirection

theorem AxisDirection.opposite_primrec :
    Primrec AxisDirection.opposite :=
  Primrec.dom_finite AxisDirection.opposite

theorem RouteBend.incomingPort_primrec :
    Primrec RouteBend.incomingPort := by
  have direction : Primrec fun routeBend : RouteBend =>
      AxisDirection.between routeBend.incomingStart routeBend.bend :=
    AxisDirection.between_primrec.comp
      RouteBend.incomingStart_primrec RouteBend.bend_primrec
  exact (CornerPort.ofDirection_primrec.comp
    (AxisDirection.opposite_primrec.comp direction)).of_eq fun _ => rfl

theorem RouteBend.outgoingPort_primrec :
    Primrec RouteBend.outgoingPort := by
  exact (CornerPort.ofDirection_primrec.comp
    (AxisDirection.between_primrec.comp
      RouteBend.bend_primrec
      RouteBend.outgoingFinish_primrec)).of_eq fun _ => rfl

private theorem mapRoute_primrec
    {Input : Type*} [Primcodable Input]
    (route : Input → List Cell)
    (transform : Input → Cell → Cell)
    (routePrimrec : Primrec route)
    (transformPrimrec : Primrec fun input : Input × Cell =>
      transform input.1 input.2) :
    Primrec fun input : Input =>
      (route input).map (transform input) :=
  Primrec.list_map routePrimrec transformPrimrec.to₂

abbrev CrossoverRouteInput (Variable : Type*) :=
  ((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat

def crossoverRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : CrossoverRouteInput Variable) : List Cell :=
  (drawingPlanarSATCrossoverIncidenceDrawing
    input.1.1.1 input.1.1.2).routes input.1.2 input.2

theorem crossoverRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (crossoverRoute (Variable := Variable)) := by
  change Primrec fun input : CrossoverRouteInput Variable =>
    (drawingPlanarSATCrossoverIncidenceDrawing
      input.1.1.1 input.1.1.2).routes input.1.2 input.2
  have base : Primrec fun input :
      ((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat =>
      crossoverStraightIncidenceDrawing.routes input.1.2 input.2 :=
    crossoverStraightRoutes_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have origin : Primrec fun input :
      ((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat =>
      crossingMacroOrigin input.1.1.2 :=
    crossingMacroOrigin_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have transform : Primrec fun input :
      (((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat) ×
        Cell =>
      Cell.add (crossingMacroOrigin input.1.1.1.2) input.2 :=
    Computability.cell_add_primrec.comp
      (origin.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map base transform.to₂


end PeriodicOrthocrossing
end LeanTrominoes
