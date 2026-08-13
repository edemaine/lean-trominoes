/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedEmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing

/-!
# Retained-ray certificates for local planar-SAT routes

Each retained planar-SAT clause carries metadata selecting one of five local
geometric components.  This file proves that every genuine route of each
selected component is supported by the combined retained-ray rasterizer:

* carrier lenses and bend corners are already orthogonal;
* crossover routes and routed-variable arms use the eight compass rays;
* routed source clauses use the three additional certified slopes.

The componentwise result is then lifted through the metadata lookup to the
complete finite retained planar-SAT incidence drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- Every placed crossover route uses a retained compass ray. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_routesRetainedRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverIncidenceDrawing
      formula crossing).RoutesRetainedRay := by
  unfold drawingPlanarSATCrossoverIncidenceDrawing
  apply EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.rename
  apply EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.translate
  apply EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.of_routesOctilinear
  simpa [crossoverStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routesOctilinear
        crossoverFormula
        CrossoverVariable.position
        crossoverFormula_embeddedTerminalPortsValid

/-- Every placed routed-variable arm uses a retained compass ray. -/
theorem drawingPlanarSATRoutedVariableIncidenceDrawing_routesRetainedRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).RoutesRetainedRay := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
  apply EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.rename
  apply EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.translate
  apply EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.of_routesOctilinear
  simpa [duplicatorArmStraightIncidenceDrawing] using
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routesOctilinear
        (duplicatorArmFormula arm)
        (DuplicatorArmVariable.position arm)
        (duplicatorArmFormula_embeddedTerminalPortsValid arm)

/-- Every placed routed source-clause route uses one of the three certified
exceptional retained rays. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_routesRetainedRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).RoutesRetainedRay := by
  apply EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.of_rename
    planarSATRoutedClauseArm
    (routedClauseArmPosition formula site)
  rw [drawingPlanarSATRoutedClauseIncidenceDrawing_rename]
  exact
    (routedClausePortStraightIncidenceDrawing_routesRetainedRay
      (routedClausePortLiterals formula site)).translate
        (routedClauseOrigin formula site)

namespace DrawingPlanarSATClauseMetadata

/-- Every retained-valid metadata-selected local component has only
retained-ray routes. -/
theorem retainedLocalDrawingRoutesRetainedRay
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
      formula).RoutesRetainedRay := by
  cases metadata with
  | mk clause source =>
    cases source with
    | crossover crossing localClauseIndex =>
        exact
          drawingPlanarSATCrossoverIncidenceDrawing_routesRetainedRay
            formula crossing
    | carrier link localClauseIndex =>
        exact
          EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.of_isOrthogonal
            (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
              wellFormed degree isLocal valid.1).2.1
    | bend routeBend localClauseIndex =>
        exact
          EmbeddedCNFIncidenceDrawing.RoutesRetainedRay.of_isOrthogonal
            (drawingPlanarSATBendCornerIncidenceDrawing_isValid
              wellFormed degree isLocal valid.1).2.1
    | routedClause site =>
        exact
          drawingPlanarSATRoutedClauseIncidenceDrawing_routesRetainedRay
            formula site
    | routedVariable site armIndex arm link localClauseIndex =>
        exact
          drawingPlanarSATRoutedVariableIncidenceDrawing_routesRetainedRay
            formula site arm link

end DrawingPlanarSATClauseMetadata

/-- The complete metadata-selected finite retained drawing uses only
retained-ray route segments. -/
theorem retainedDrawingPlanarSATLocalIncidenceDrawing_routesRetainedRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).RoutesRetainedRay := by
  rw [EmbeddedCNFIncidenceDrawing.routesRetainedRay_iff]
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
  have localRetained :=
    metadata.retainedLocalDrawingRoutesRetainedRay
      wellFormed degree isLocal valid
  have selected :=
    (EmbeddedCNFIncidenceDrawing.routesRetainedRay_iff
      (metadata.source.incidenceDrawing formula)).mp
        localRetained
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
