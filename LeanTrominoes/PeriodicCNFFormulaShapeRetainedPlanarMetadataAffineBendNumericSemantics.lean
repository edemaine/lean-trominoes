/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendBaseSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorBendGeometry
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineBendTemplateSemantics

/-! # Numeric-route semantics of the affine retained-bend scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Evaluating the untranslated templates of a matching route shape gives
exactly the semantic untranslated bend list. -/
theorem RouteShape.map_evalPair_baseBendTemplates
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches pair.1) :
    shape.baseBendTemplates.map
        (fun template => template.evalPair .first pair) =
      routeBends pair.1.edgeIndex (0, 0) pair.1.route := by
  unfold RouteShape.baseBendTemplates routeBends
  rw [bendTemplatesAux_map_evalPair]
  rw [shape.map_evalPair_points .first pair shapeMatches]
  rfl

/-- Every untranslated template selected for a listed numeric route evaluates
to a bend with genuine incoming and outgoing directions. -/
theorem RouteShape.baseBendTemplate_directionsGenuine
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (shape : RouteShape)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula)
    (shapeMatches : shape.Matches descriptor)
    {template : BendTemplate}
    (templateMember : template ∈ shape.baseBendTemplates) :
    (AxisDirection.between
        (template.incomingStart.evalPair (descriptor, descriptor))
        (template.bend.evalPair (descriptor, descriptor))).IsGenuine ∧
      (AxisDirection.between
        (template.bend.evalPair (descriptor, descriptor))
        (template.outgoingFinish.evalPair
          (descriptor, descriptor))).IsGenuine := by
  have evaluatedMember :
      template.evalPair .first (descriptor, descriptor) ∈
        routeBends descriptor.edgeIndex (0, 0) descriptor.route := by
    rw [← shape.map_evalPair_baseBendTemplates
      (descriptor, descriptor) shapeMatches]
    exact List.mem_map_of_mem templateMember
  have geometry :=
    PeriodicCNF.numericRouteDescriptor_routeBend_cornerGeometry
      formula wellFormed degree isLocal descriptorMember (0, 0)
      evaluatedMember
  constructor
  · exact AxisDirection.between_isGenuine_of_axisAligned
      geometry.incomingAligned
  · exact AxisDirection.between_isGenuine_of_axisAligned
      geometry.outgoingAligned

/-- On the diagonal pair of a listed numeric route, the base affine scan is
exactly the canonical descriptor expansion of its untranslated bend list. -/
theorem affineBaseBendDescriptorBlock_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (shape : RouteShape)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula)
    (shapeMatches : shape.Matches descriptor) :
    affineBaseBendDescriptorBlock
        (descriptorPairTokens (descriptor, descriptor)) =
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          canonicalBendDescriptorBlock
            routeBend.incomingPort routeBend.outgoingPort false := by
  rw [affineBaseBendDescriptorBlock_eq_of_matches
    shape (descriptor, descriptor) rfl shapeMatches]
  · rw [← shape.map_evalPair_baseBendTemplates
      (descriptor, descriptor) shapeMatches,
      List.flatMap_map]
  · intro template templateMember
    exact (shape.baseBendTemplate_directionsGenuine
      formula wellFormed degree isLocal descriptor descriptorMember
      shapeMatches templateMember).1
  · intro template templateMember
    exact (shape.baseBendTemplate_directionsGenuine
      formula wellFormed degree isLocal descriptor descriptorMember
      shapeMatches templateMember).2

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
