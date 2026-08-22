/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTranslatedSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendOffDiagonalSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorNodup
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Numeric descriptor-stream semantics of the affine retained-bend scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- On canonical pair records, the bend block map is the pair-major
concatenation of its local affine blocks. -/
@[simp]
theorem affineBendDescriptorStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    affineBendDescriptorStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        affineBendDescriptorBlock (descriptorPairTokens pair) := by
  unfold affineBendDescriptorStream
  rw [mappedOutput_encodeDescriptorPairs]

/-- For numeric incidence descriptors, the edge-index test reduces the
row-major descriptor square to its diagonal. -/
theorem numericRouteDescriptorSquare_flatMap_eq_diagonal
    {Variable Output : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (function : RouteDescriptor × RouteDescriptor → List Output)
    (offDiagonal :
      ∀ first ∈ PeriodicCNF.numericRouteDescriptors formula,
        ∀ second ∈ PeriodicCNF.numericRouteDescriptors formula,
          first.edgeIndex ≠ second.edgeIndex →
            function (first, second) = []) :
    ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
        (PeriodicCNF.numericRouteDescriptors formula)).flatMap function =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        function (descriptor, descriptor) := by
  change
    ((PeriodicCNF.numericRouteDescriptors formula).flatMap fun first =>
      (PeriodicCNF.numericRouteDescriptors formula).map fun second =>
        (first, second)).flatMap function = _
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro first firstMember
  rw [List.flatMap_map]
  rw [flatMap_eq_of_unique
    (PeriodicCNF.numericRouteDescriptors formula)
    (fun second => function (first, second)) first
    (PeriodicCNF.numericRouteDescriptors_nodup formula)
    firstMember]
  intro second secondMember secondNe
  apply offDiagonal first firstMember second secondMember
  intro edgeIndexEq
  exact secondNe
    (PeriodicCNF.numericRouteDescriptors_eq_of_edgeIndex_eq
      formula secondMember firstMember edgeIndexEq.symm)

/-- The affine bend scan over the canonical numeric descriptor square is
exactly the route-major, translation-major semantic bend descriptor stream. -/
theorem affineBendDescriptorStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineBendDescriptorStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (neighborTranslations.flatMap fun translate =>
          routeBends descriptor.edgeIndex translate descriptor.route).flatMap
            fun routeBend =>
              canonicalBendDescriptorBlock
                routeBend.incomingPort routeBend.outgoingPort false := by
  rw [affineBendDescriptorStream_encodeDescriptorPairs]
  rw [numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair =>
      affineBendDescriptorBlock (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact affineBendDescriptorBlock_numeric_diagonal
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first firstMember second secondMember edgeIndexNe
    exact affineBendDescriptorBlock_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
