import LeanTrominoes.EmbeddedCNFIncidenceDrawingOrthogonalPrefixes
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing

/-!
# Orthogonal prefixes of local retained planar-SAT routes

The five local component families in the retained planar-SAT construction
share a useful route-shape invariant:

* carrier lenses and bend corners are fully orthogonal;
* crossover routes, routed-variable arms, and routed source-clause routes are
  direct two-point segments.

Consequently every route is orthogonal after removing its final point.  This
is the exact shape fact needed before proving separation of rasterized route
prefixes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- Every placed crossover route has an orthogonal singleton prefix. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_routePrefixesOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverIncidenceDrawing
      formula crossing).RoutePrefixesOrthogonal := by
  unfold drawingPlanarSATCrossoverIncidenceDrawing
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.rename
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.translate
  simpa [crossoverStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePrefixesOrthogonal
      crossoverFormula CrossoverVariable.position

/-- Every placed routed-variable arm has orthogonal singleton prefixes. -/
theorem drawingPlanarSATRoutedVariableIncidenceDrawing_routePrefixesOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).RoutePrefixesOrthogonal := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.rename
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.translate
  simpa [duplicatorArmStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePrefixesOrthogonal
      (duplicatorArmFormula arm)
      (DuplicatorArmVariable.position arm)

/-- Every placed routed source-clause ray has an orthogonal singleton
prefix. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_routePrefixesOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).RoutePrefixesOrthogonal := by
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.of_rename
    planarSATRoutedClauseArm
    (routedClauseArmPosition formula site)
  rw [drawingPlanarSATRoutedClauseIncidenceDrawing_rename]
  apply EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.translate
  simpa [routedClausePortStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePrefixesOrthogonal
      (routedClausePortFormula
        (routedClausePortLiterals formula site))
      DuplicatorArm.portPosition

namespace DrawingPlanarSATClauseMetadata

/-- Every retained-valid metadata-selected local component has orthogonal
route prefixes. -/
theorem retainedLocalDrawingRoutePrefixesOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula) :
    (metadata.source.incidenceDrawing
      formula).RoutePrefixesOrthogonal := by
  cases metadata with
  | mk clause source =>
    cases source with
    | crossover crossing localClauseIndex =>
        exact
          drawingPlanarSATCrossoverIncidenceDrawing_routePrefixesOrthogonal
            formula crossing
    | carrier link localClauseIndex =>
        exact
          EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.of_isOrthogonal
            (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
              wellFormed degree isLocal valid.1).2.1
    | bend routeBend localClauseIndex =>
        exact
          EmbeddedCNFIncidenceDrawing.RoutePrefixesOrthogonal.of_isOrthogonal
            (drawingPlanarSATBendCornerIncidenceDrawing_isValid
              wellFormed degree isLocal valid.1).2.1
    | routedClause site =>
        exact
          drawingPlanarSATRoutedClauseIncidenceDrawing_routePrefixesOrthogonal
            formula site
    | routedVariable site armIndex arm link localClauseIndex =>
        exact
          drawingPlanarSATRoutedVariableIncidenceDrawing_routePrefixesOrthogonal
            formula site arm link

end DrawingPlanarSATClauseMetadata

/-- The complete metadata-selected finite retained drawing has orthogonal
route prefixes. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_routePrefixesOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).RoutePrefixesOrthogonal := by
  rw [EmbeddedCNFIncidenceDrawing.routePrefixesOrthogonal_iff]
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing_formula]
    at clauseMember
  rcases retainedDrawingPlanarSATClauseMetadata_lookup_valid
      formula clauseMember with
    ⟨metadata, metadataLookup, clauseEqual, valid⟩
  subst clause
  have localClauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  have localOrthogonal :=
    metadata.retainedLocalDrawingRoutePrefixesOrthogonal
      wellFormed degree isLocal valid
  have selected :=
    (EmbeddedCNFIncidenceDrawing.routePrefixesOrthogonal_iff
      (metadata.source.incidenceDrawing formula)).mp
        localOrthogonal
        metadata.clause
        metadata.source.localClauseIndex
        localClauseMember
        literal literalIndex literalMember
  simpa
      [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
        retainedDrawingPlanarSATLocalIncidenceRoutes,
        metadataLookup] using selected

end PeriodicOrthocrossing
end LeanTrominoes
