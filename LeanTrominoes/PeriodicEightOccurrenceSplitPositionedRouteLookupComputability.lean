/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCopiedRouteComputability

/-!
# Computable lookup for positioned fixed-eight routes

This module combines the copied-clause lookup with the fixed Figure 7 cycle
routes, and identifies the resulting proof-free computation with the existing
certified angular-splice route family.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

set_option maxHeartbeats 1000000

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- The proof-free total fixed-eight route lookup is computable. -/
theorem canonicalAngularSplicedIncidenceRoutesData_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (ports : Input → OccurrencePorts)
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (ports input.1.1).port input.1.2 input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      copies input.1 input.2) :
    Computable fun input : (Input × Nat) × Nat =>
      canonicalAngularSplicedIncidenceRoutesData
        (source input.1.1) (sourcePlacement input.1.1)
        (ports input.1.1) (copies input.1.1)
        input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have occurrenceClausesPrimrec : Primrec fun input =>
      occurrenceClauses (source input) (ports input) :=
    occurrenceClauses_primrec source ports sourcePrimrec portsPrimrec
  have occurrenceCount : Primrec fun input : Query =>
      (occurrenceClauses
        (source input.1.1) (ports input.1.1)).length :=
    Primrec.list_length.comp
      (occurrenceClausesPrimrec.comp (Primrec.fst.comp Primrec.fst))
  have occurrenceBranch : PrimrecPred fun input : Query =>
      input.1.2 <
        (occurrenceClauses
          (source input.1.1) (ports input.1.1)).length :=
    Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst) occurrenceCount
  have copied := canonicalAngularCopiedIncidenceRoutesData_computable
    source sourcePlacement ports copies sourcePrimrec periodPrimrec
    positionPrimrec portsPrimrec copiesPrimrec
  have cycleIndex : Primrec fun input : Query =>
      input.1.2 -
        (occurrenceClauses
          (source input.1.1) (ports input.1.1)).length :=
    Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) occurrenceCount
  have cycle : Primrec fun input : Query =>
      allCycleRoutes (source input.1.1) (sourcePlacement input.1.1)
        (input.1.2 -
          (occurrenceClauses
            (source input.1.1) (ports input.1.1)).length)
        input.2 :=
    allCycleRoutes_primrec
      source sourcePlacement sourcePrimrec positionPrimrec |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst) cycleIndex)
          Primrec.snd)
  exact (Computable.cond occurrenceBranch.decide.to_comp
    copied cycle.to_comp).of_eq fun input => by
      simp only [Bool.cond_decide,
        canonicalAngularSplicedIncidenceRoutesData]

/-- The existing proof-carrying canonical route family is computable. -/
theorem canonicalAngularSplicedIncidenceRoutes_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (order : (input : Input) → OccurrenceOrder (source input).erase)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (occurrencePortsOfAngularOrder
        (source input.1.1).erase (order input.1.1)).port
          input.1.2 input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      (order input.1).copies input.2) :
    Computable fun input : (Input × Nat) × Nat =>
      canonicalAngularSplicedIncidenceRoutes
        (source input.1.1) (sourcePlacement input.1.1)
        (order input.1.1) input.1.2 input.2 := by
  have computed := canonicalAngularSplicedIncidenceRoutesData_computable
    source sourcePlacement
    (fun input => occurrencePortsOfAngularOrder
      (source input).erase (order input))
    (fun input => (order input).copies)
    sourcePrimrec periodPrimrec positionPrimrec
    portsPrimrec copiesPrimrec
  exact computed.of_eq fun input =>
    congrFun
      (congrFun
        (canonicalAngularSplicedIncidenceRoutes_eq_data
          (source input.1.1) (sourcePlacement input.1.1)
          (order input.1.1)).symm
        input.1.2)
      input.2

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
