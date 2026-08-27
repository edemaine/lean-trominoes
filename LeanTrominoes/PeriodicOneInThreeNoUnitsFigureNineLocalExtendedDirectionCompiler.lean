/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirections
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineExtendedRouteDecomposition

/-!
# Finite compiler for local-plus-extended Figure 9 prefixes

The complete potentially loopy prefix is determined by a finite width-three
clause profile, one valid local-template incidence index, finite exit-fan
metadata, and one of three fan slots.  Consequently its normalized direction
word is a fixed finite block.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open Computability Turing
open Gadget
open PeriodicCNF.UnaryProgramClauseProfile

/-- Select the finite Figure 9 template using only the clause's finite literal
profile.  Atom identities and horizontal-slice flags do not affect this local
geometry. -/
def templateDrawingOfClauseProfile :
    ClauseProfile →
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
        FigureNineNoUnitsVariable
  | .unary first => oneDrawingFor first.value
  | .binary first second =>
      twoDrawingFor first.value second.value
  | .ternary first second third =>
      fullDrawingFor first.value second.value third.value

/-- Finite selection data for one complete local-plus-extended prefix. -/
abbrev LocalExtendedDirectionQuery :=
  Σ profile : ClauseProfile,
    Fin (templateDrawingOfClauseProfile profile).incidences.length ×
      ComposedClauseExitFanData × Fin 3

/-- The exact normalized direction block selected by one finite prefix
query. -/
def normalizedLocalExtendedDirectionBlock
    (query : LocalExtendedDirectionQuery) : List AxisDirection :=
  let drawing := templateDrawingOfClauseProfile query.1
  let localRoute := drawing.routeAt (drawing.incidenceAt query.2.1)
  let extendedRoute := query.2.2.1.extendedRoute query.2.2.2
  unitSubdivisionDirections
    (AxisDirection.normalizeOrthogonalPolyline
      (joinAtEndpoint localRoute extendedRoute))

local instance localExtendedDirectionAxisDirectionInhabited :
    Inhabited AxisDirection := ⟨.invalid⟩

/-- A fixed finite block transducer emits any stream of selected normalized
local-plus-extended prefix words in linear time. -/
noncomputable def normalizedLocalExtendedDirectionsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List LocalExtendedDirectionQuery)
      (List AxisDirection)
      LocalExtendedDirectionQuery AxisDirection
      id id
      (fun queries =>
        queries.flatMap normalizedLocalExtendedDirectionBlock) :=
  FiniteBlockTransducer.computableInPolyTime
    normalizedLocalExtendedDirectionBlock

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

end
