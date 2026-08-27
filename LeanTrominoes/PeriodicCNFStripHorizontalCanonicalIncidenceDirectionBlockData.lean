/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseCompactContractedRouteRasterSourceCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalContractedDirectionBlockListData

/-! # Canonical compact blocks for horizontal incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open Gadget PeriodicThreeDM PlanarThreeDM

/-- A harmless total fallback for tags outside the computed incidence list.
Its value is irrelevant to every canonical contraction lookup. -/
def horizontalIncidenceDirectionBlockFallback :
    HorizontalTypedIncidenceDirectionBlock :=
  .clause (.topLeftOuter, .red)

/-- Name one of the compact blocks whose existence was proved for every
genuine stable incidence tag.  This definition is a proof-oriented semantic
target; the source emitter below must implement the resulting token function
by an explicit polynomial-time machine. -/
noncomputable def horizontalCanonicalIncidenceDirectionBlock
    (source : PeriodicCNF Nat) (tag : IncidenceTag) :
    HorizontalTypedIncidenceDirectionBlock :=
  if tagMember : tag ∈
      (horizontalThreeDMProblemComputed source).incidenceTags then
    Classical.choose
      (horizontalAssembledRouteAtTag_directionBlock_of_tag_mem
        source tag tagMember)
  else
    horizontalIncidenceDirectionBlockFallback

/-- The canonical selector denotes the exact subdivided assembled route at
every genuine stable incidence tag. -/
theorem horizontalCanonicalIncidenceDirectionBlock_directions
    (source : PeriodicCNF Nat) (tag : IncidenceTag)
    (tagMember : tag ∈
      (horizontalThreeDMProblemComputed source).incidenceTags) :
    (horizontalCanonicalIncidenceDirectionBlock source tag).directions =
      unitSubdivisionDirections
        (horizontalAssembledRouteAtTagComputed (source, tag)) := by
  unfold horizontalCanonicalIncidenceDirectionBlock
  rw [dif_pos tagMember]
  exact (Classical.choose_spec
    (horizontalAssembledRouteAtTag_directionBlock_of_tag_mem
      source tag tagMember)).symm

/-- Hence the named selector satisfies the complete incidence lookup
contract consumed by canonical contraction. -/
theorem horizontalCanonicalIncidenceDirectionBlocks_correct
    (source : PeriodicCNF Nat) :
    HorizontalIncidenceDirectionBlocksCorrect source
      (horizontalCanonicalIncidenceDirectionBlock source) := by
  intro tag tagMember
  exact horizontalCanonicalIncidenceDirectionBlock_directions
    source tag tagMember

/-- Canonically ordered contracted edge blocks with no external lookup
parameter. -/
noncomputable def horizontalCanonicalContractedDirectionBlocks
    (source : PeriodicCNF Nat) :
    List DirectSparseCompactContractedEdgeBlock :=
  horizontalContractedDirectionBlocks
    (horizontalThreeDMProblemComputed source)
    (horizontalCanonicalIncidenceDirectionBlock source)

/-- Exact proof-oriented compact source-token target for the remaining route
emitter. -/
noncomputable def directSparseCanonicalCompactContractedRouteSourceTokens
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List HorizontalContractedRouteRasterSource.Token :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  HorizontalContractedRouteRasterSource.tokens
    (directSparseCompactContractedRouteEntries
      source
      (directSparseAssembledRouteMetadata decider symbols)
      (horizontalCanonicalContractedDirectionBlocks source))

/-- Interpreting the canonical compact source target gives exactly the
canonical raster-request word. -/
theorem directSparseCanonicalCompactContractedRouteSourceTokens_correct
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    TM2EndDelimitedBlockMap.mappedOutput
        HorizontalContractedRouteRasterSource.isEnd
        HorizontalContractedRouteRasterSource.requestOutput
        (directSparseCanonicalCompactContractedRouteSourceTokens
          decider symbols) =
      GadgetSparseRouteRasterRequestTokens.tokens
        (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
          decider symbols) := by
  unfold directSparseCanonicalCompactContractedRouteSourceTokens
    horizontalCanonicalContractedDirectionBlocks
  exact
    directSparseCompactContractedRouteEntries_mappedOutput_of_incidenceBlocks
      decider symbols
      (horizontalCanonicalIncidenceDirectionBlock
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
      (horizontalCanonicalIncidenceDirectionBlocks_correct
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance
    horizontalCanonicalIncidenceDirectionBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Concrete machine obligation left by the canonical semantic source
target. -/
abbrev DirectSparseCanonicalCompactContractedRouteSourceTokenCompiler :=
  TM2ComputableInPolyTime id id
    (directSparseCanonicalCompactContractedRouteSourceTokens decider)

/-- An implementation of the canonical target supplies the abstract compact
source interface used by all downstream route machinery. -/
noncomputable def directSparseCompactContractedRouteRasterSourceCompilerOfCanonical
    (compiler :
      DirectSparseCanonicalCompactContractedRouteSourceTokenCompiler
        decider) :
    DirectSparseCompactContractedRouteRasterSourceCompiler decider where
  sourceTokens :=
    directSparseCanonicalCompactContractedRouteSourceTokens decider
  computableInPolyTime := compiler
  correct :=
    directSparseCanonicalCompactContractedRouteSourceTokens_correct decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
