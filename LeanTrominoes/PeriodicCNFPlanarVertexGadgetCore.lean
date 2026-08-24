/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarIncidences
import LeanTrominoes.PeriodicCNFPlanarIncidenceVertexPositionData
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableSiteOccurrenceData
import LeanTrominoes.PeriodicCNFPlanarSATNodeData

/-! # Shared data for routed SAT vertex gadgets -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A lifted clause vertex is named by its protoclauses index and cell. -/
abbrev ClauseRouteSite := Nat × Cell

/-- Whether a metadata-rich endpoint is the clause end of its incidence
route. -/
def CNFRouteEndpoint.isClauseEnd {Variable : Type*}
    (endpoint : CNFRouteEndpoint Variable) : Bool :=
  decide (endpoint.endpoint.endKind = .source)

/-- Whether a metadata-rich endpoint is the variable end of its incidence
route. -/
def CNFRouteEndpoint.isVariableEnd {Variable : Type*}
    (endpoint : CNFRouteEndpoint Variable) : Bool :=
  decide (endpoint.endpoint.endKind = .target)

/-- Carrier-node variable reached by a routed SAT endpoint. -/
def CNFRouteEndpoint.planarNode {Variable : Type*}
    (endpoint : CNFRouteEndpoint Variable) : PlanarSATNode Variable :=
  .carrier endpoint.endpoint.carrierNode

/-- Lifted clause site reached by the source end of an incidence route. -/
def CNFRouteEndpoint.clauseSite {Variable : Type*}
    (endpoint : CNFRouteEndpoint Variable) : ClauseRouteSite :=
  endpoint.occurrence.clauseOccurrence

/-- Lifted variable site reached by the target end of an incidence route. -/
def CNFRouteEndpoint.variableSite {Variable : Type*}
    (endpoint : CNFRouteEndpoint Variable) : VariableRouteSite Variable :=
  endpoint.occurrence.variableOccurrence

end PeriodicOrthocrossing
end LeanTrominoes
