import LeanTrominoes.OrthogonalPolylineSymmetries
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Orthogonal prefixes of embedded-CNF incidence routes

The retained planar-SAT construction permits a nonorthogonal final ray at a
route's variable endpoint.  Everything before that final ray is rectilinear.
This file packages exactly that intermediate route-shape invariant for finite
embedded-CNF drawings.

The invariant is preserved by translation and logical-variable renaming.  It
also follows either from full drawing orthogonality or from using direct
two-point incidence routes, whose `dropLast` prefixes are singletons.
-/

namespace LeanTrominoes

namespace PeriodicOrthocrossing

/-- Removing a polyline's final point preserves its orthogonality. -/
theorem OrthogonalPolyline.dropLast
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points) :
    OrthogonalPolyline points.dropLast :=
  List.IsChain.dropLast orthogonal

end PeriodicOrthocrossing

namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

open PeriodicOrthocrossing

/-- Every genuine route is rectilinear before its final point. -/
def RoutePrefixesOrthogonal
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    OrthogonalPolyline
      (drawing.routeAt
        (drawing.incidenceAt incidenceIndex)).dropLast

/-- Every genuine route is either fully rectilinear or is a direct-style
route with a singleton prefix. -/
def RoutesOrthogonalOrSingletonPrefix
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    let route :=
      drawing.routeAt
        (drawing.incidenceAt incidenceIndex)
    OrthogonalPolyline route ∨
      route.dropLast.length = 1

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.RoutePrefixesOrthogonal := by
  unfold RoutePrefixesOrthogonal OrthogonalPolyline
    incidenceAt incidences routeAt
  infer_instance

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.RoutesOrthogonalOrSingletonPrefix := by
  unfold RoutesOrthogonalOrSingletonPrefix OrthogonalPolyline
    incidenceAt incidences routeAt
  infer_instance

/-- Full drawing orthogonality implies prefix orthogonality. -/
theorem RoutePrefixesOrthogonal.of_isOrthogonal
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (orthogonal : drawing.IsOrthogonal) :
    drawing.RoutePrefixesOrthogonal := by
  intro incidenceIndex
  apply OrthogonalPolyline.dropLast
  rw [orthogonalPolyline_iff_segments]
  intro segment segmentMember
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, rfl⟩
  exact orthogonal incidenceIndex segmentIndex

/-- Full drawing orthogonality selects the first branch of the route-shape
dichotomy. -/
theorem RoutesOrthogonalOrSingletonPrefix.of_isOrthogonal
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (orthogonal : drawing.IsOrthogonal) :
    drawing.RoutesOrthogonalOrSingletonPrefix := by
  intro incidenceIndex
  left
  rw [orthogonalPolyline_iff_segments]
  intro segment segmentMember
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, rfl⟩
  exact orthogonal incidenceIndex segmentIndex

/-- Translation preserves route-prefix orthogonality. -/
theorem RoutePrefixesOrthogonal.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (orthogonal : drawing.RoutePrefixesOrthogonal)
    (offset : Cell) :
    (drawing.translate offset).RoutePrefixesOrthogonal := by
  intro translatedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
  simpa only [translatePolyline, List.map_dropLast] using
    (orthogonal originalIndex).translate offset

/-- Translation preserves the orthogonal-or-singleton-prefix dichotomy. -/
theorem RoutesOrthogonalOrSingletonPrefix.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (shape : drawing.RoutesOrthogonalOrSingletonPrefix)
    (offset : Cell) :
    (drawing.translate
      offset).RoutesOrthogonalOrSingletonPrefix := by
  intro translatedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
  rcases shape originalIndex with
    orthogonal | singleton
  · exact Or.inl (orthogonal.translate offset)
  · right
    rw [← List.map_dropLast, List.length_map]
    exact singleton

/-- Logical-variable renaming changes no route prefix coordinates. -/
theorem RoutePrefixesOrthogonal.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (orthogonal : drawing.RoutePrefixesOrthogonal)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename
      variableMap targetPosition).RoutePrefixesOrthogonal := by
  intro renamedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact orthogonal originalIndex

/-- Logical-variable renaming preserves the route-shape dichotomy. -/
theorem RoutesOrthogonalOrSingletonPrefix.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (shape : drawing.RoutesOrthogonalOrSingletonPrefix)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename
      variableMap targetPosition).RoutesOrthogonalOrSingletonPrefix := by
  intro renamedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact shape originalIndex

/-- Prefix orthogonality can be pulled back through a logical rename because
renaming leaves all route coordinates unchanged. -/
theorem RoutePrefixesOrthogonal.of_rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (orthogonal :
      (drawing.rename
        variableMap targetPosition).RoutePrefixesOrthogonal) :
    drawing.RoutePrefixesOrthogonal := by
  intro originalIndex
  let renamedIndex :
      Fin (drawing.rename
        variableMap targetPosition).incidences.length :=
    ⟨originalIndex.val, by
      simpa only [rename_incidences_length] using
        originalIndex.isLt⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  have renamedPrefix := orthogonal renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
    at renamedPrefix
  exact renamedPrefix

/-- The route-shape dichotomy can be pulled back through a logical rename. -/
theorem RoutesOrthogonalOrSingletonPrefix.of_rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (shape :
      (drawing.rename variableMap
        targetPosition).RoutesOrthogonalOrSingletonPrefix) :
    drawing.RoutesOrthogonalOrSingletonPrefix := by
  intro originalIndex
  let renamedIndex :
      Fin (drawing.rename
        variableMap targetPosition).incidences.length :=
    ⟨originalIndex.val, by
      simpa only [rename_incidences_length] using
        originalIndex.isLt⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  have renamedShape := shape renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
    at renamedShape
  exact renamedShape

/-- Membership-style form of route-prefix orthogonality. -/
theorem routePrefixesOrthogonal_iff
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    drawing.RoutePrefixesOrthogonal ↔
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ drawing.formula.zipIdx →
          ∀ literal literalIndex,
            (literal, literalIndex) ∈ clause.literals.zipIdx →
              OrthogonalPolyline
                (drawing.routes
                  clauseIndex literalIndex).dropLast := by
  constructor
  · intro orthogonal clause clauseIndex clauseMember
      literal literalIndex literalMember
    let incidence : EmbeddedCNFIncidence Variable :=
      ⟨clause, clauseIndex, literal, literalIndex⟩
    have incidenceMember :
        incidence ∈ drawing.incidences := by
      exact
        (mem_embeddedCNFIncidences_iff
          drawing.formula incidence).mpr
          ⟨clauseMember, literalMember⟩
    rcases List.mem_iff_get.mp incidenceMember with
      ⟨incidenceIndex, incidenceEqual⟩
    have routeOrthogonal := orthogonal incidenceIndex
    have incidenceAtEqual :
        drawing.incidenceAt incidenceIndex =
          incidence := incidenceEqual
    rw [incidenceAtEqual] at routeOrthogonal
    exact routeOrthogonal
  · intro orthogonal incidenceIndex
    let incidence :=
      drawing.incidenceAt incidenceIndex
    have incidenceMember :
        incidence ∈ drawing.incidences :=
      List.get_mem drawing.incidences incidenceIndex
    have indexedMembers :=
      (mem_embeddedCNFIncidences_iff
        drawing.formula incidence).mp incidenceMember
    exact orthogonal
      incidence.clause incidence.clauseIndex
        indexedMembers.1
      incidence.literal incidence.literalIndex
        indexedMembers.2

/-- Membership-style form of the orthogonal-or-singleton-prefix
dichotomy. -/
theorem routesOrthogonalOrSingletonPrefix_iff
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    drawing.RoutesOrthogonalOrSingletonPrefix ↔
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ drawing.formula.zipIdx →
          ∀ literal literalIndex,
            (literal, literalIndex) ∈ clause.literals.zipIdx →
              OrthogonalPolyline
                  (drawing.routes
                    clauseIndex literalIndex) ∨
                (drawing.routes
                  clauseIndex literalIndex).dropLast.length = 1 := by
  constructor
  · intro shape clause clauseIndex clauseMember
      literal literalIndex literalMember
    let incidence : EmbeddedCNFIncidence Variable :=
      ⟨clause, clauseIndex, literal, literalIndex⟩
    have incidenceMember :
        incidence ∈ drawing.incidences := by
      exact
        (mem_embeddedCNFIncidences_iff
          drawing.formula incidence).mpr
          ⟨clauseMember, literalMember⟩
    rcases List.mem_iff_get.mp incidenceMember with
      ⟨incidenceIndex, incidenceEqual⟩
    have routeShape := shape incidenceIndex
    have incidenceAtEqual :
        drawing.incidenceAt incidenceIndex =
          incidence := incidenceEqual
    rw [incidenceAtEqual] at routeShape
    exact routeShape
  · intro shape incidenceIndex
    let incidence :=
      drawing.incidenceAt incidenceIndex
    have incidenceMember :
        incidence ∈ drawing.incidences :=
      List.get_mem drawing.incidences incidenceIndex
    have indexedMembers :=
      (mem_embeddedCNFIncidences_iff
        drawing.formula incidence).mp incidenceMember
    exact shape
      incidence.clause incidence.clauseIndex
        indexedMembers.1
      incidence.literal incidence.literalIndex
        indexedMembers.2

/-- Every direct two-point incidence route has a singleton, hence orthogonal,
prefix. -/
theorem straightIncidenceDrawing_routePrefixesOrthogonal
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    (straightIncidenceDrawing
      formula variablePosition).RoutePrefixesOrthogonal := by
  rw [routePrefixesOrthogonal_iff]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  change (clause, clauseIndex) ∈ formula.zipIdx
    at clauseMember
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [straightIncidenceDrawing, straightIncidenceRoutes,
    straightIncidenceRoute, clauseLookup, literalLookup,
    OrthogonalPolyline]

/-- Direct two-point incidence drawings select the singleton-prefix branch
of the route-shape dichotomy. -/
theorem straightIncidenceDrawing_routesOrthogonalOrSingletonPrefix
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell) :
    (straightIncidenceDrawing
      formula variablePosition).RoutesOrthogonalOrSingletonPrefix := by
  rw [routesOrthogonalOrSingletonPrefix_iff]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  change (clause, clauseIndex) ∈ formula.zipIdx
    at clauseMember
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  right
  simp [straightIncidenceDrawing, straightIncidenceRoutes,
    straightIncidenceRoute, clauseLookup, literalLookup]

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
