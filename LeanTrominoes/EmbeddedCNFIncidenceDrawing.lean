import LeanTrominoes.LocalIncidenceDrawing
import LeanTrominoes.PlanarThreeSATGadgets

/-!
# Finite embedded-CNF incidence drawings

The routed planar-SAT reduction is assembled from finite positioned CNF
gadgets.  This file packages the geometric data common to those gadgets:
one physical position per variable and one indexed polyline per literal
occurrence.  All geometric predicates quantify through finite `Fin` types,
so a fixed gadget can discharge them with `native_decide`.

The planarity predicate is continuous for axis-aligned segments.  It rejects
overlapping route interiors, route points in another route's interior,
non-endpoint contacts, graph vertices in route interiors, and coincident
graph vertices.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- One literal occurrence in a finite embedded formula, retaining both
levels of presentation indices. -/
structure EmbeddedCNFIncidence (Variable : Type*) where
  clause : EmbeddedClause Variable
  clauseIndex : Nat
  literal : Variable × Bool
  literalIndex : Nat
  deriving DecidableEq, Repr

/-- Literal occurrences in clause-major, literal-minor presentation order. -/
def embeddedCNFIncidences {Variable : Type*}
    (formula : List (EmbeddedClause Variable)) :
    List (EmbeddedCNFIncidence Variable) :=
  formula.zipIdx.flatMap fun taggedClause =>
    taggedClause.1.literals.zipIdx.map fun taggedLiteral =>
      ⟨taggedClause.1, taggedClause.2,
        taggedLiteral.1, taggedLiteral.2⟩

/-- Membership in the flattened incidence list is exactly membership at
both levels of the embedded formula's indexed presentation. -/
theorem mem_embeddedCNFIncidences_iff
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (incidence : EmbeddedCNFIncidence Variable) :
    incidence ∈ embeddedCNFIncidences formula ↔
      (incidence.clause, incidence.clauseIndex) ∈ formula.zipIdx ∧
        (incidence.literal, incidence.literalIndex) ∈
          incidence.clause.literals.zipIdx := by
  constructor
  · intro incidenceMember
    rcases List.mem_flatMap.mp incidenceMember with
      ⟨taggedClause, taggedClauseMember, incidenceMember⟩
    rcases List.mem_map.mp incidenceMember with
      ⟨taggedLiteral, taggedLiteralMember, incidenceEqual⟩
    subst incidence
    exact ⟨taggedClauseMember, taggedLiteralMember⟩
  · rintro ⟨clauseMember, literalMember⟩
    apply List.mem_flatMap.mpr
    refine
      ⟨(incidence.clause, incidence.clauseIndex),
        clauseMember, ?_⟩
    exact List.mem_map.mpr
      ⟨(incidence.literal, incidence.literalIndex),
        literalMember, by cases incidence; rfl⟩

/-- A finite embedded formula together with its physical variable positions
and one total indexed route family.  Out-of-range route values are harmless:
all predicates inspect only `embeddedCNFIncidences`. -/
structure EmbeddedCNFIncidenceDrawing (Variable : Type*) where
  formula : List (EmbeddedClause Variable)
  variablePosition : Variable → Cell
  routes : Nat → Nat → List Cell

namespace EmbeddedCNFIncidenceDrawing

/-- The drawing's finite metadata-rich incidence list. -/
def incidences {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    List (EmbeddedCNFIncidence Variable) :=
  embeddedCNFIncidences drawing.formula

/-- Select one genuine incidence through a finite index. -/
def incidenceAt {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (index : Fin drawing.incidences.length) :
    EmbeddedCNFIncidence Variable :=
  drawing.incidences.get index

/-- Select the route belonging to one metadata-rich occurrence. -/
def routeAt {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (incidence : EmbeddedCNFIncidence Variable) : List Cell :=
  drawing.routes incidence.clauseIndex incidence.literalIndex

/-- Every genuine route starts at its clause and ends at its variable. -/
def RoutesMatch {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ index : Fin drawing.incidences.length,
    let incidence := drawing.incidenceAt index
    (drawing.routeAt incidence).head? =
        some incidence.clause.position ∧
      (drawing.routeAt incidence).getLast? =
        some (drawing.variablePosition incidence.literal.1)

instance {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.RoutesMatch := by
  unfold RoutesMatch incidenceAt incidences routeAt
  infer_instance

/-- Every segment of every genuine incidence route is axis-aligned. -/
def IsOrthogonal {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    let route := drawing.routeAt (drawing.incidenceAt incidenceIndex)
    ∀ segmentIndex : Fin (gridPolylineSegments route).length,
      ((gridPolylineSegments route).get segmentIndex).IsAxisAligned

instance {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.IsOrthogonal := by
  unfold IsOrthogonal incidenceAt incidences routeAt
  infer_instance

/-- No two segment interiors from the two routes meet in the continuous
plane. -/
def SegmentInteriorsDisjoint (first second : List Cell) : Prop :=
  ∀ firstIndex : Fin (gridPolylineSegments first).length,
    ∀ secondIndex : Fin (gridPolylineSegments second).length,
      ¬GridSegment.InteriorsMeet
        ((gridPolylineSegments first).get firstIndex)
        ((gridPolylineSegments second).get secondIndex)

instance (first second : List Cell) :
    Decidable (SegmentInteriorsDisjoint first second) := by
  unfold SegmentInteriorsDisjoint
  infer_instance

/-- No listed point of `first` lies in a segment interior of `second`. -/
def RoutePointsAvoidInteriors (first second : List Cell) : Prop :=
  ∀ pointIndex : Fin first.length,
    ∀ segmentIndex : Fin (gridPolylineSegments second).length,
      ¬((gridPolylineSegments second).get segmentIndex).InteriorContains
        (first.get pointIndex)

instance (first second : List Cell) :
    Decidable (RoutePointsAvoidInteriors first second) := by
  unfold RoutePointsAvoidInteriors
  infer_instance

/-- A listed route point is one of the route's two advertised endpoints. -/
def RoutePointIsEndpoint (route : List Cell) (point : Cell) : Prop :=
  route.head? = some point ∨ route.getLast? = some point

instance (route : List Cell) (point : Cell) :
    Decidable (RoutePointIsEndpoint route point) := by
  unfold RoutePointIsEndpoint
  infer_instance

/-- Any listed point shared by two routes is an endpoint of both. -/
def RoutesMeetOnlyAtEndpoints (first second : List Cell) : Prop :=
  ∀ firstPointIndex : Fin first.length,
    ∀ secondPointIndex : Fin second.length,
      first.get firstPointIndex = second.get secondPointIndex →
        RoutePointIsEndpoint first (first.get firstPointIndex) ∧
          RoutePointIsEndpoint second (second.get secondPointIndex)

instance (first second : List Cell) :
    Decidable (RoutesMeetOnlyAtEndpoints first second) := by
  unfold RoutesMeetOnlyAtEndpoints
  infer_instance

/-- Complete continuous separation condition for two distinct routes. -/
def RoutesAvoidEachOther (first second : List Cell) : Prop :=
  SegmentInteriorsDisjoint first second ∧
    RoutePointsAvoidInteriors first second ∧
    RoutePointsAvoidInteriors second first ∧
    RoutesMeetOnlyAtEndpoints first second

instance (first second : List Cell) :
    Decidable (RoutesAvoidEachOther first second) := by
  unfold RoutesAvoidEachOther
  infer_instance

/-- Distinct formula variables in their first-occurrence order. -/
def variableVertices {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : List Variable :=
  (drawing.formula.flatMap fun clause =>
    clause.literals.map Prod.fst).dedup

/-- All graph-vertex positions, variables first and clauses second. -/
def vertexPositions {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : List Cell :=
  drawing.variableVertices.map drawing.variablePosition ++
    drawing.formula.map EmbeddedClause.position

/-- No finite graph vertex lies in any genuine route interior. -/
def VerticesAvoidRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ vertexIndex : Fin drawing.vertexPositions.length,
    ∀ incidenceIndex : Fin drawing.incidences.length,
      let route := drawing.routeAt (drawing.incidenceAt incidenceIndex)
      ∀ segmentIndex : Fin (gridPolylineSegments route).length,
        ¬((gridPolylineSegments route).get segmentIndex).InteriorContains
          (drawing.vertexPositions.get vertexIndex)

instance {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.VerticesAvoidRouteInteriors := by
  unfold VerticesAvoidRouteInteriors vertexPositions variableVertices
    incidenceAt incidences routeAt
  infer_instance

/-- Exact finite continuous-planarity certificate for an embedded CNF.
Different literal occurrences remain different routes even when they have
the same logical variable endpoint. -/
def IsPlanar {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  (∀ incidenceIndex : Fin drawing.incidences.length,
    LocalIncidenceDrawing.RouteIsSimple
      (drawing.routeAt (drawing.incidenceAt incidenceIndex))) ∧
  (∀ firstIndex secondIndex : Fin drawing.incidences.length,
    firstIndex ≠ secondIndex →
      RoutesAvoidEachOther
        (drawing.routeAt (drawing.incidenceAt firstIndex))
        (drawing.routeAt (drawing.incidenceAt secondIndex))) ∧
  drawing.VerticesAvoidRouteInteriors ∧
  drawing.vertexPositions.Nodup

instance {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.IsPlanar := by
  unfold IsPlanar
  infer_instance

/-- Complete finite geometric certificate used by fixed planar-SAT
gadgets. -/
def IsValid {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  drawing.RoutesMatch ∧ drawing.IsOrthogonal ∧ drawing.IsPlanar

instance {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.IsValid := by
  unfold IsValid
  infer_instance

end EmbeddedCNFIncidenceDrawing

/-- Membership-style endpoint condition used by the input-dependent routed
SAT assembly. -/
def EmbeddedPhysicalIncidenceRoutesMatch
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell)
    (routes : Nat → Nat → List Cell) : Prop :=
  ∀ clause clauseIndex,
    (clause, clauseIndex) ∈ formula.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
          (routes clauseIndex literalIndex).head? =
              some clause.position ∧
            (routes clauseIndex literalIndex).getLast? =
              some (variablePosition literal.1)

/-- The finitely decidable endpoint certificate implies the convenient
membership-style endpoint condition. -/
theorem EmbeddedCNFIncidenceDrawing.physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (routesMatch : drawing.RoutesMatch) :
    EmbeddedPhysicalIncidenceRoutesMatch
      drawing.formula drawing.variablePosition drawing.routes := by
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences := by
    exact (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨index, incidenceEqual⟩
  have endpoints := routesMatch index
  change
    (drawing.routeAt incidence).head? =
        some incidence.clause.position ∧
      (drawing.routeAt incidence).getLast? =
        some (drawing.variablePosition incidence.literal.1)
  simp only [EmbeddedCNFIncidenceDrawing.incidenceAt] at endpoints
  exact incidenceEqual ▸ endpoints

/-- Conversely, the membership-style endpoint condition establishes the
finite drawing's `RoutesMatch` field. -/
theorem EmbeddedCNFIncidenceDrawing.routesMatch_of_physical
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (routesMatch :
      EmbeddedPhysicalIncidenceRoutesMatch
        drawing.formula drawing.variablePosition drawing.routes) :
    drawing.RoutesMatch := by
  intro index
  let incidence := drawing.incidenceAt index
  have incidenceMember :
      incidence ∈ drawing.incidences :=
    List.get_mem drawing.incidences index
  have indexedMembers :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mp incidenceMember
  exact routesMatch
    incidence.clause incidence.clauseIndex indexedMembers.1
    incidence.literal incidence.literalIndex indexedMembers.2

/-- Direct geometric segment from a clause vertex to a variable vertex.
This route is intentionally not required to be axis-aligned: it records the
full terminal ray used to choose the cyclic order before high-degree
variables are occurrence-split. -/
def straightIncidenceRoute (source target : Cell) : List Cell :=
  [source, target]

/-- Total presentation-indexed family of direct embedded-CNF incidences. -/
def straightIncidenceRoutes
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    Nat → Nat → List Cell :=
  fun clauseIndex literalIndex =>
    match formula[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            straightIncidenceRoute
              clause.position (variablePosition literal.1)

/-- Every genuine indexed direct route has its advertised physical
endpoints. -/
theorem straightIncidenceRoutes_physicalRoutesMatch
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    EmbeddedPhysicalIncidenceRoutesMatch
      formula variablePosition
      (straightIncidenceRoutes formula variablePosition) := by
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [straightIncidenceRoutes, straightIncidenceRoute,
    clauseLookup, literalLookup]

/-- Direct incidences packaged as a finite drawing.  Its endpoint field is
always valid; orthogonality and planarity are deliberately deferred until
after occurrence splitting. -/
def straightIncidenceDrawing
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    EmbeddedCNFIncidenceDrawing Variable where
  formula := formula
  variablePosition := variablePosition
  routes := straightIncidenceRoutes formula variablePosition

/-- The packaged direct incidence drawing satisfies `RoutesMatch`. -/
theorem straightIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    (straightIncidenceDrawing formula variablePosition).RoutesMatch := by
  apply
    EmbeddedCNFIncidenceDrawing.routesMatch_of_physical
  exact straightIncidenceRoutes_physicalRoutesMatch
    formula variablePosition

end PlanarThreeSAT
end LeanTrominoes
