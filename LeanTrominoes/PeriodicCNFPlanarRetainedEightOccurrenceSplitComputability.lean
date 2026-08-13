/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplit
import LeanTrominoes.PeriodicCNFPlanarRetainedGaugedRoutesComputability
import LeanTrominoes.PeriodicThreeSATThreeAngularOrderComputability

/-!
# Computability of the retained fixed-eight occurrence split

The computable, gauged retained incidence routes determine the angular order
of the genuine occurrences around each variable.  This module proves that the
corresponding east-first eight-port lookup and the resulting occurrence-split
formula are primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1200000

theorem retainedDrawingAngularOccurrencePorts_port_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      (retainedDrawingAngularOccurrencePorts input.1.1).port
        input.1.2 input.2 := by
  exact (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder_port_primrec
    (Input := PeriodicCNF Variable)
    (Variable := WrappedPeriodicPlanarSATVariable Variable)
    retainedPlanarSATFormula
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    retainedPlanarSATFormula_primrec
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec).of_eq
      fun input => congrArg
        (fun ports => ports.port input.1.2 input.2)
        (retainedDrawingAngularOccurrencePorts_eq input.1.1).symm

theorem retainedDrawingEightOccurrenceSplitFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDrawingEightOccurrenceSplitFormula :
      PeriodicCNF Variable → _) := by
  exact (PeriodicEightOccurrenceSplit.angularFormula_primrec
    (Input := PeriodicCNF Variable)
    (Variable := WrappedPeriodicPlanarSATVariable Variable)
    retainedPlanarSATFormula
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    retainedPlanarSATFormula_primrec
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec).of_eq
      fun input =>
        (retainedDrawingEightOccurrenceSplitFormula_eq input).symm

theorem retainedDrawingEightOccurrenceSplitFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedDrawingEightOccurrenceSplitFormula :
      PeriodicCNF Variable → _) :=
  retainedDrawingEightOccurrenceSplitFormula_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes
