/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionNumericSemantics
import LeanTrominoes.RetainedAngularFanFallbackPrefixDirectionScalingCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Scaling compiled retained-bend fallback prefixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine
namespace BendRoutePrefixDirectionScaling

open Computability Turing Gadget PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

/-- Route-delimited fixed-clearance expansion of one bend source prefix. -/
def scaledDelimitedBendRouteDirections
    (directions : List AxisDirection) : List BendRouteDirectionToken :=
  delimitedBendRouteDirections (repeatDirections 1152 directions)

/-- Four explicitly scaled source-prefix words for one fixed corner equality
drawing. -/
def canonicalScaledBendRoutePrefixDirectionBlock
    (firstPort secondPort : CornerPort) : List BendRouteDirectionToken :=
  scaledDelimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 0 0) ++
    scaledDelimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 0 1) ++
    scaledDelimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 1 0) ++
    scaledDelimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 1 1)

def blockOutput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteDirectionToken :=
  FallbackPrefixDirectionScaling.output
    (affineBaseBendRoutePrefixDirectionBlock tokens)

def streamOutput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteDirectionToken :=
  FallbackPrefixDirectionScaling.output
    (affineBaseBendRoutePrefixDirectionStream tokens)

/-- Scaling the finite four-prefix table produces its explicit 1152-scaled
counterpart. -/
@[simp] theorem output_canonicalBendRoutePrefixDirectionBlock
    (firstPort secondPort : CornerPort) :
    FallbackPrefixDirectionScaling.output
        (canonicalBendRoutePrefixDirectionBlock firstPort secondPort) =
      canonicalScaledBendRoutePrefixDirectionBlock
        firstPort secondPort := by
  unfold canonicalBendRoutePrefixDirectionBlock
    canonicalScaledBendRoutePrefixDirectionBlock
    scaledDelimitedBendRouteDirections
  rw [FallbackPrefixDirectionScaling.output_append,
    FallbackPrefixDirectionScaling.output_append,
    FallbackPrefixDirectionScaling.output_append]
  unfold delimitedBendRouteDirections
  rw [FallbackPrefixDirectionScaling.output_delimitedDirections,
    FallbackPrefixDirectionScaling.output_delimitedDirections,
    FallbackPrefixDirectionScaling.output_delimitedDirections,
    FallbackPrefixDirectionScaling.output_delimitedDirections]

/-- On a listed numeric route's diagonal pair, the scaled compiler emits
exactly four fixed-clearance source prefixes for every semantic bend. -/
theorem blockOutput_numeric_diagonal
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
    blockOutput (descriptorPairTokens (descriptor, descriptor)) =
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          canonicalScaledBendRoutePrefixDirectionBlock
            routeBend.incomingPort routeBend.outgoingPort := by
  unfold blockOutput
  rw [affineBaseBendRoutePrefixDirectionBlock_numeric_diagonal
    formula wellFormed degree isLocal shape descriptor descriptorMember
    shapeMatches]
  rw [FallbackPrefixDirectionScaling.output_flatMap]
  simp only [output_canonicalBendRoutePrefixDirectionBlock]

/-- Affine bend selection followed by fixed prefix scaling is
polynomial-time computable. -/
noncomputable def blockOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id blockOutput := by
  let selected :=
    affineBaseBendRoutePrefixDirectionBlockComputableInPolyTime
  let scaled := TM2CompositionMachine.computableInPolyTime selected
    FallbackPrefixDirectionScaling.outputComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun tokens => FallbackPrefixDirectionScaling.output
      (affineBaseBendRoutePrefixDirectionBlock tokens))
  exact scaled

/-- Scaling the complete affine bend-prefix stream is polynomial-time
computable. -/
noncomputable def streamOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id streamOutput := by
  let selected :=
    affineBaseBendRoutePrefixDirectionStreamComputableInPolyTime
  let scaled := TM2CompositionMachine.computableInPolyTime selected
    FallbackPrefixDirectionScaling.outputComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun tokens => FallbackPrefixDirectionScaling.output
      (affineBaseBendRoutePrefixDirectionStream tokens))
  exact scaled

end BendRoutePrefixDirectionScaling
end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
