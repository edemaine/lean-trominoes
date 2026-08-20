/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidencePrefixComputability
import LeanTrominoes.PeriodicCNFStripHorizontalVariableRoutePrefixQueryComputability
import LeanTrominoes.PeriodicCNFStripHorizontalVariableOccurrenceRouteQueryComputability
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedOccurrenceTripleQueryComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteComputability
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

/-! # Computability of complete variable-module incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableTypedIncidenceRouteComputed_primrec :
    Primrec horizontalVariableTypedIncidenceRouteComputed := by
  have isRouted : PrimrecPred fun
      input : HorizontalVariableTypedIncidenceRouteInput =>
      input.1.2 = horizontalRoutedOccurrenceTripleQueryComputed input :=
    Primrec.eq.comp
      (Primrec.snd.comp Primrec.fst)
      horizontalRoutedOccurrenceTripleQueryComputed_primrec
  have prefixRoute : Primrec fun
      input : HorizontalVariableTypedIncidenceRouteInput =>
      horizontalVariableIncidencePrefixComputed
        (horizontalVariableRoutePrefixQueryComputed input) :=
    horizontalVariableIncidencePrefixComputed_primrec.comp
      horizontalVariableRoutePrefixQueryComputed_primrec
  have occurrenceRoute : Primrec fun
      input : HorizontalVariableTypedIncidenceRouteInput =>
      horizontalOccurrenceCoordinatedRouteComputed
        (horizontalVariableOccurrenceRouteQueryComputed input) :=
    horizontalOccurrenceCoordinatedRouteComputed_primrec.comp
      horizontalVariableOccurrenceRouteQueryComputed_primrec
  have joined : Primrec fun
      input : HorizontalVariableTypedIncidenceRouteInput =>
      joinAtEndpoint
        (horizontalVariableIncidencePrefixComputed
          (horizontalVariableRoutePrefixQueryComputed input))
        (horizontalOccurrenceCoordinatedRouteComputed
          (horizontalVariableOccurrenceRouteQueryComputed input)) :=
    PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
      prefixRoute occurrenceRoute
  exact (Primrec.ite isRouted joined prefixRoute).of_eq fun input => by
    simp [horizontalVariableTypedIncidenceRouteComputed]

end PeriodicCNFStripReduction
end LeanTrominoes
