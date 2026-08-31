/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks
import LeanTrominoes.RetainedAngularFanFinalCarrierStartData

/-! # Tagged-link families for final retained carriers -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierTaggedLinkFamilyDataThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Tagged implication directions of all retained final-carrier links. -/
def finalCarrierTaggedLinkValues
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (EqualityLink CarrierNode × Bool) :=
  (retainedDrawingCompleteCarrierLinks
    (PeriodicThreeSATThree.formula source).incidenceGraph).product
      [true, false]

/-- Tagged retained-carrier implications indexed from an explicit global
start. -/
def finalCarrierTaggedLinksFrom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (start : Nat) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  (finalCarrierTaggedLinkValues source).zipIdx start

/-- Tagged retained-carrier implications at their global positions after the
crossover prefix. -/
def finalCarrierTaggedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  finalCarrierTaggedLinksFrom source (finalCarrierStart source)

end LeanTrominoes.PeriodicEightOccurrenceSplit
