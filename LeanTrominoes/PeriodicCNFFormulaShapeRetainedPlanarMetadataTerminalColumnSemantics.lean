/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalDataSemantics

/-! # Local semantics of retained carrier and bend terminal columns -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

/-- The carrier terminal block is exactly the four actual local incidence
routes, in the two-clause presentation order. -/
theorem carrier_routeTerminalDataBlock_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks source.incidenceGraph) :
    [classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.carrier link 0).incidenceDrawing source).routes
            0 0)),
      classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.carrier link 0).incidenceDrawing source).routes
            0 1)),
      classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.carrier link 1).incidenceDrawing source).routes
            1 0)),
      classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.carrier link 1).incidenceDrawing source).routes
            1 1))] =
      carrierLensRouteTerminalDataBlock link.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second)) := by
  simp only [carrierLensRouteTerminalDataBlock,
    List.cons.injEq, and_true]
  constructor
  · exact carrier_routeTerminalData_eq source wellFormed degree isLocal
      link linkMember 0 0
  constructor
  · exact carrier_routeTerminalData_eq source wellFormed degree isLocal
      link linkMember 0 1
  constructor
  · exact carrier_routeTerminalData_eq source wellFormed degree isLocal
      link linkMember 1 0
  · exact carrier_routeTerminalData_eq source wellFormed degree isLocal
      link linkMember 1 1

/-- The bend terminal block is exactly its four translated corner-table
routes, again in clause-major order. -/
theorem bend_routeTerminalDataBlock_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    [classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.bend routeBend 0).incidenceDrawing
            source).routes 0 0)),
      classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.bend routeBend 0).incidenceDrawing
            source).routes 0 1)),
      classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.bend routeBend 1).incidenceDrawing
            source).routes 1 0)),
      classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.bend routeBend 1).incidenceDrawing
            source).routes 1 1))] =
      bendRouteTerminalDataBlock
        routeBend.incomingPort routeBend.outgoingPort := by
  simp only [bendRouteTerminalDataBlock,
    List.cons.injEq, and_true]
  constructor
  · exact bend_routeTerminalData_eq source routeBend 0 0
  constructor
  · exact bend_routeTerminalData_eq source routeBend 0 1
  constructor
  · exact bend_routeTerminalData_eq source routeBend 1 0
  · exact bend_routeTerminalData_eq source routeBend 1 1

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
