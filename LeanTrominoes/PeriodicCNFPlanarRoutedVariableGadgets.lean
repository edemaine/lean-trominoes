/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarIncidenceVertexPositionData
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableSiteOccurrenceData
import LeanTrominoes.PeriodicCNFPlanarSATNodeData
import LeanTrominoes.PlanarThreeSATDuplicatorArm

/-! # Variable gadgets at routed SAT vertices -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Distinct routed terminal nodes at one lifted variable vertex, in global
edge order.  Set-normalization is semantically inert and makes the active
duplicator arms syntactically collision-free. -/
def routedVariableNodes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (PlanarSATNode Variable) :=
  ((variableRouteOccurrencesAt formula site).map fun occurrence =>
    PlanarSATNode.carrier
      (.terminal (occurrence.targetTerminal formula))).dedup

/-- Three total duplicator ports at one lifted variable vertex.  Missing
ports still project to the center in the semantic interface, but no clauses
are generated for those inactive arms. -/
def routedVariablePorts
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    DuplicatorPorts (PlanarSATNode Variable) :=
  let center : PlanarSATNode Variable := .atom site
  let endpoints := routedVariableNodes formula site
  ⟨center,
    endpoints.getD 0 center,
    endpoints.getD 1 center,
    endpoints.getD 2 center⟩

/-- Position the Figure 8(a) duplicator at a lifted variable vertex. -/
def routedVariableOrigin
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) : Cell :=
  liftedIncidenceVertexMacroOrigin formula
    (.variable site.1) site.2

/-- Classify a segment terminal by the routed-variable port at its local
macrocell endpoint. -/
def SegmentTerminal.duplicatorArm
    (terminal : SegmentTerminal) : DuplicatorArm :=
  let localPosition :=
    segmentTerminalLocalPosition
      terminal.indexed.segment terminal.endpoint
  if localPosition = DuplicatorArm.left.portPosition then
    .left
  else if localPosition = DuplicatorArm.middle.portPosition then
    .middle
  else
    .right

/-- Classify an external routed node by its physical terminal arm.  The
fallback is unreachable for active routed-variable link endpoints. -/
def PlanarSATNode.duplicatorArm
    {Variable : Type*} : PlanarSATNode Variable → DuplicatorArm
  | .carrier (.terminal terminal) => terminal.duplicatorArm
  | _ => .right

/-- The two implication-clause positions for one active routed arm. -/
def routedVariableEqualityPositions
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm) : EqualityPositions :=
  let origin := routedVariableOrigin formula site
  let localPositions := duplicatorArmEqualityPositions arm
  ⟨Cell.add origin localPositions.forward,
    Cell.add origin localPositions.backward⟩

/-- The active (at most three) equality arms of one routed variable
duplicator. -/
def routedVariableLinksAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (EqualityLink (PlanarSATNode Variable)) :=
  equalityTakeThreeLinks
    (routedVariableNodes formula site) (.atom site)
    fun node _ =>
      routedVariableEqualityPositions formula site
        node.duplicatorArm

/-- The active Figure 8(a) subgadget at one lifted variable vertex. -/
def routedVariableFormulaAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (EmbeddedClause (PlanarSATNode Variable)) :=
  equalityFamily (routedVariableLinksAt formula site)

/-- All active routed variable subgadgets in the neighboring block. -/
def drawingRoutedVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATNode Variable)) :=
  (drawingVariableRouteSites formula).flatMap
    (routedVariableFormulaAt formula)

end PeriodicOrthocrossing
end LeanTrominoes
