/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTerminalColumnNumericSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendStreamSemantics

/-! # Stream semantics of retained-bend terminal columns -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

@[simp] theorem affineBaseBendPortStream_encodeDescriptorPairs
    {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    affineBaseBendPortStream block (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        affineBaseBendPortBlock block (descriptorPairTokens pair) := by
  unfold affineBaseBendPortStream
  rw [mappedOutput_encodeDescriptorPairs]

/-- On numeric route descriptors, the pair-major selector emits exactly one
fixed port block per untranslated semantic bend. -/
theorem affineBaseBendPortStream_numericRouteDescriptors
    {Variable Output : Type} [DecidableEq Variable]
    (block : CornerPort → CornerPort → List Output)
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineBaseBendPortStream block
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            block routeBend.incomingPort routeBend.outgoingPort := by
  rw [affineBaseBendPortStream_encodeDescriptorPairs]
  rw [numericRouteDescriptorSquare_flatMap_eq_diagonal formula
    (fun pair =>
      affineBaseBendPortBlock block (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
        formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact affineBaseBendPortBlock_numeric_diagonal block
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first firstMember second secondMember edgeIndexNe
    exact affineBaseBendPortBlock_eq_nil_of_edgeIndex_ne
      block (first, second) edgeIndexNe

@[simp] theorem affineBaseBendTerminalDirectionStream_eq_portStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    affineBaseBendTerminalDirectionStream tokens =
      affineBaseBendPortStream
        canonicalBendTerminalDirectionBlock tokens := by
  rfl

@[simp] theorem affineBaseBendTerminalRadialStream_eq_portStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    affineBaseBendTerminalRadialStream tokens =
      affineBaseBendPortStream
        canonicalBendTerminalRadialBlock tokens := by
  rfl

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

