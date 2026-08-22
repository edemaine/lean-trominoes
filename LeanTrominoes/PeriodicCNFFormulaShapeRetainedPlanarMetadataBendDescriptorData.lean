/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRouteDirections
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorData

/-! # Finite retained bend descriptor templates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- Whether the second endpoint of a normalized bend link is in the next
horizontal period slice. -/
def bendLinkNextSlice
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) : Bool :=
  carrierLinkNextSlice source
    (routeBend.equalityLink source.incidenceGraph)

/-- The finite direction-aware descriptor of one routed-bend implication. -/
def bendClauseDescriptor
    (firstPort secondPort : CornerPort)
    (nextSlice forward : Bool) :
    FormulaShapeDirectionOrdering.Token :=
  match forward with
  | true =>
      .clause (.binary
        ⟨false, true⟩ (bendRouteFirstDirection firstPort secondPort 0 0)
        ⟨nextSlice, false⟩
          (bendRouteFirstDirection firstPort secondPort 0 1))
  | false =>
      .clause (.binary
        ⟨false, false⟩ (bendRouteFirstDirection firstPort secondPort 1 0)
        ⟨nextSlice, true⟩
          (bendRouteFirstDirection firstPort secondPort 1 1))

/-- Fixed two-token block determined by a bend's two ordered compass ports
and normalized relative-slice bit. -/
def canonicalBendDescriptorBlock
    (firstPort secondPort : CornerPort)
    (nextSlice : Bool) :
    List FormulaShapeDirectionOrdering.Token :=
  [bendClauseDescriptor firstPort secondPort nextSlice true,
    bendClauseDescriptor firstPort secondPort nextSlice false]

@[simp] theorem canonicalBendDescriptorBlock_length
    (firstPort secondPort : CornerPort)
    (nextSlice : Bool) :
    (canonicalBendDescriptorBlock
      firstPort secondPort nextSlice).length = 2 :=
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
