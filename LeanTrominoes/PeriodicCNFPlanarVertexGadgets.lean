/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarIncidences
import LeanTrominoes.PlanarThreeSATDuplicatorArm

/-!
# Clause and variable gadgets at routed SAT vertices

The planar route core ends at the vertices of the CNF incidence graph.
Clause vertices reuse the original signed clause, with each literal atom
replaced by its incoming route terminal.  Variable vertices receive the
Figure 8(a) three-way duplicator, padded by its center variable when their
degree is below three.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- External variables of the routed planar SAT construction: carrier nodes
along protoedge routes, plus one central Boolean at each lifted variable
vertex. -/
inductive PlanarSATNode (Variable : Type*)
  | carrier (node : CarrierNode)
  | atom (occurrence : Variable × Cell)
  deriving DecidableEq, Repr

/-- A lifted clause vertex is named by its protoclauses index and cell. -/
abbrev ClauseRouteSite := Nat × Cell

/-- A lifted variable vertex is named by its atom and cell. -/
abbrev VariableRouteSite (Variable : Type*) := Variable × Cell

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

/-- All routed endpoints incident to clause vertices. -/
def drawingClauseRouteEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (CNFRouteEndpoint Variable) :=
  (drawingCNFRouteEndpoints formula).filter
    CNFRouteEndpoint.isClauseEnd

/-- All routed endpoints incident to variable vertices. -/
def drawingVariableRouteEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (CNFRouteEndpoint Variable) :=
  (drawingCNFRouteEndpoints formula).filter
    CNFRouteEndpoint.isVariableEnd

/-- The finite lifted clause sites represented in the neighboring block. -/
def drawingClauseRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List ClauseRouteSite :=
  formula.clauses.zipIdx.flatMap fun taggedClause =>
    neighborTranslations.map fun translate =>
      (taggedClause.2, translate)

/-- The finite lifted variable sites represented in the neighboring block. -/
def drawingVariableRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (VariableRouteSite Variable) :=
  ((drawingCNFRouteOccurrences formula).map
    CNFRouteOccurrence.variableOccurrence).dedup

/-- Incidence-route occurrences at one lifted clause vertex, in original
literal order. -/
def clauseRouteOccurrencesAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (site : ClauseRouteSite) :
    List (CNFRouteOccurrence Variable) :=
  ((PeriodicCNF.incidencesWithMetadata formula).zipIdx.filter
      fun taggedIncidence =>
        taggedIncidence.1.clauseIndex = site.1).map
    fun taggedIncidence =>
      ⟨taggedIncidence.1, taggedIncidence.2, site.2⟩

/-- Incidence-route occurrences at one lifted variable vertex, in global
edge order. -/
def variableRouteOccurrencesAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (CNFRouteOccurrence Variable) :=
  ((drawingCNFRouteOccurrences formula).filter fun occurrence =>
    occurrence.variableOccurrence = site).insertionSort fun first second =>
      first.edgeIndex ≤ second.edgeIndex

/-- Clause endpoints at one lifted clause vertex, in original literal order. -/
def clauseRouteEndpointsAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (site : ClauseRouteSite) :
    List (CNFRouteEndpoint Variable) :=
  ((drawingClauseRouteEndpoints formula).filter fun endpoint =>
    endpoint.clauseSite = site).insertionSort fun first second =>
      first.occurrence.incidence.literalIndex ≤
        second.occurrence.incidence.literalIndex

/-- Variable endpoints at one lifted variable vertex, in global edge order. -/
def variableRouteEndpointsAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (CNFRouteEndpoint Variable) :=
  ((drawingVariableRouteEndpoints formula).filter fun endpoint =>
    endpoint.variableSite = site).insertionSort fun first second =>
      first.occurrence.edgeIndex ≤ second.occurrence.edgeIndex

/-- Drawing-grid position of a lifted incidence-graph vertex. -/
def liftedIncidenceVertexPosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (vertex : CNFVertex Variable) (translate : Cell) : Cell :=
  let graph := PeriodicCNF.incidenceGraph formula
  Cell.add
    (PeriodicGridDrawing.vertexPosition graph (drawing graph) vertex)
    ((drawing graph).periodTranslation translate)

/-- Macro-grid origin surrounding a lifted incidence-graph vertex. -/
def liftedIncidenceVertexMacroOrigin
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (vertex : CNFVertex Variable) (translate : Cell) : Cell :=
  Cell.scale planarMacroScale
    (liftedIncidenceVertexPosition formula vertex translate)

/-- The original signed clause, attached to the carrier node of each
incoming incidence route. -/
def routedClauseAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (site : ClauseRouteSite) :
    EmbeddedClause (PlanarSATNode Variable) where
  position :=
    Cell.add
      (liftedIncidenceVertexMacroOrigin formula
        (.clause site.1) site.2) (10, 10)
  literals :=
    (clauseRouteOccurrencesAt formula site).map fun occurrence =>
      (.carrier (.terminal (occurrence.sourceTerminal formula)),
        occurrence.incidence.literal.value)

/-- All routed original clauses in the neighboring block. -/
def drawingRoutedClauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATNode Variable)) :=
  (drawingClauseRouteSites formula).map
    (routedClauseAt formula)

/-- Satisfaction of the routed clause family is exactly satisfaction of
every listed routed clause. -/
theorem drawingRoutedClauseFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATNode Variable → Bool) :
    FormulaHolds assignment (drawingRoutedClauseFormula formula) ↔
      ∀ site ∈ drawingClauseRouteSites formula,
        ClauseHolds assignment (routedClauseAt formula site) := by
  unfold FormulaHolds drawingRoutedClauseFormula
  constructor
  · intro holds site siteMem
    exact holds (routedClauseAt formula site)
      (List.mem_map.mpr ⟨site, siteMem, rfl⟩)
  · intro holds clause clauseMem
    rcases List.mem_map.mp clauseMem with
      ⟨site, siteMem, clauseEq⟩
    subst clause
    exact holds site siteMem

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
  ((routedVariableNodes formula site).take 3).zipIdx.map
    fun taggedNode =>
      ⟨taggedNode.1, .atom site,
        routedVariableEqualityPositions formula site
          taggedNode.1.duplicatorArm⟩

/-- The active Figure 8(a) subgadget at one lifted variable vertex. -/
def routedVariableFormulaAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (EmbeddedClause (PlanarSATNode Variable)) :=
  equalityFamily (routedVariableLinksAt formula site)

/-- Active-arm satisfaction is equivalent to the original total three-port
interface: inactive `getD` ports equal the center definitionally. -/
theorem routedVariableFormulaAt_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATNode Variable → Bool)
    (site : VariableRouteSite Variable) :
    FormulaHolds assignment
        (routedVariableFormulaAt formula site) ↔
      assignment (routedVariablePorts formula site).left =
          assignment (.atom site) ∧
        assignment (routedVariablePorts formula site).top =
          assignment (.atom site) ∧
        assignment (routedVariablePorts formula site).right =
          assignment (.atom site) := by
  rw [routedVariableFormulaAt, equalityFamily_holds_iff]
  let endpoints := routedVariableNodes formula site
  change
    (∀ link ∈
        (endpoints.take 3).zipIdx.map fun taggedNode =>
          (⟨taggedNode.1, .atom site,
            routedVariableEqualityPositions
              formula site taggedNode.1.duplicatorArm⟩ :
            EqualityLink (PlanarSATNode Variable)),
      assignment link.first = assignment link.second) ↔
      assignment (endpoints.getD 0 (.atom site)) =
          assignment (.atom site) ∧
        assignment (endpoints.getD 1 (.atom site)) =
          assignment (.atom site) ∧
        assignment (endpoints.getD 2 (.atom site)) =
          assignment (.atom site)
  cases endpoints with
  | nil =>
      simp
  | cons first rest =>
      cases rest with
      | nil =>
          simp
      | cons second rest =>
          cases rest with
          | nil =>
              simp
          | cons third rest =>
              simp

/-- All active routed variable subgadgets in the neighboring block. -/
def drawingRoutedVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATNode Variable)) :=
  (drawingVariableRouteSites formula).flatMap
    (routedVariableFormulaAt formula)

/-- The variable family holds exactly when all three (possibly padded) route
ports agree with the central lifted atom at every represented site. -/
theorem drawingRoutedVariableFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATNode Variable → Bool) :
    FormulaHolds assignment (drawingRoutedVariableFormula formula) ↔
      ∀ site ∈ drawingVariableRouteSites formula,
        assignment (routedVariablePorts formula site).left =
            assignment (.atom site) ∧
          assignment (routedVariablePorts formula site).top =
            assignment (.atom site) ∧
          assignment (routedVariablePorts formula site).right =
            assignment (.atom site) := by
  rw [drawingRoutedVariableFormula,
    formulaHolds_flatMap_iff]
  constructor
  · intro holds site siteMem
    exact
      (routedVariableFormulaAt_holds_iff
        formula assignment site).mp
        (holds site siteMem)
  · intro holds site siteMem
    exact
      (routedVariableFormulaAt_holds_iff
        formula assignment site).mpr
        (holds site siteMem)

end PeriodicOrthocrossing
end LeanTrominoes
