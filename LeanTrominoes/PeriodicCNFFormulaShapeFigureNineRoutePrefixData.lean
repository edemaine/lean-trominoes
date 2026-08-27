/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfilePolarityRouteOperationData
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionCompiler

/-! # Finite Figure 9 route-prefix descriptors from directed profiles -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open UnaryProgramClauseProfile
open FormulaShapeDirectionOrdering
open ClauseProfilePolarityRouteOperation
open PlanarOneInThreeNoUnitsFigureNine
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Forget the first directions while preserving the clause's literal order. -/
def clauseProfile : DirectedClauseProfile → ClauseProfile
  | .unary first _ => .unary first
  | .binary first _ second _ => .binary first second
  | .ternary first _ second _ third _ => .ternary first second third

/-- Repackage the stable clockwise sort while retaining each literal's
paired source-route direction.  The width-three constructors make the total
`ofList` fallback unreachable. -/
def orderedDirectedProfile (profile : DirectedClauseProfile) :
    DirectedClauseProfile :=
  DirectedClauseProfile.ofList
    (profile.taggedLiterals.insertionSort directionLE)

/-- The repackaging retains the complete sorted literal/direction list. -/
@[simp] theorem taggedLiterals_orderedDirectedProfile :
    ∀ profile : DirectedClauseProfile,
      (orderedDirectedProfile profile).taggedLiterals =
        profile.taggedLiterals.insertionSort directionLE := by
  native_decide

/-- Forgetting the directions after the paired sort is exactly the existing
clockwise ordered literal profile. -/
@[simp] theorem clauseProfile_orderedDirectedProfile :
    ∀ profile : DirectedClauseProfile,
      clauseProfile (orderedDirectedProfile profile) =
        profile.orderedProfile := by
  native_decide

/-- Reconstruct the finite composed exit-fan lookup from a directed clause
profile.  Inactive slots use the harmless `invalid` fallback. -/
def exitFanData (profile : DirectedClauseProfile) :
    ComposedClauseExitFanData where
  countPred := match profile with
    | .unary .. => ⟨0, by decide⟩
    | .binary .. => ⟨1, by decide⟩
    | .ternary .. => ⟨2, by decide⟩
  direction := fun slot =>
    ((profile.taggedLiterals[slot.val]?).map Prod.snd).getD .invalid

/-- Convert the stable width-three source slot to the connector's finite
slot index. -/
def sourceSlotFin : SourceLiteralSlot → Fin 3
  | .first => ⟨0, by decide⟩
  | .second => ⟨1, by decide⟩
  | .third => ⟨2, by decide⟩

/-- Recognize the three genuine inherited source roles among all finite
Figure 9 and unit-elimination roles. -/
def sourceSlot? : FigureNineNoUnitsVariable → Option SourceLiteralSlot
  | .inherited .sourceFirst => some .first
  | .inherited .sourceSecond => some .second
  | .inherited .sourceThird => some .third
  | _ => none

/-- One finite Figure 9 prefix.  Only a genuine inherited source occurrence
still needs its corresponding dynamic source-tail word. -/
inductive Descriptor
  | local (query : LocalDirectionQuery)
  | inherited
      (sourceSlot : SourceLiteralSlot)
      (query : LocalExtendedDirectionQuery)
  deriving DecidableEq, Fintype

instance : Inhabited Descriptor :=
  ⟨.local
    ⟨.unary default,
      ⟨0, by native_decide⟩⟩⟩

/-- Classify one finite template incidence and package its exact local query. -/
def descriptorAt (profile : DirectedClauseProfile)
    (index : Fin
      (templateDrawingOfClauseProfile
        (clauseProfile profile)).incidences.length) : Descriptor :=
  let plain := clauseProfile profile
  let drawing := templateDrawingOfClauseProfile plain
  match sourceSlot? (drawing.incidenceAt index).literal.1 with
  | none => .local ⟨plain, index⟩
  | some sourceSlot =>
      .inherited sourceSlot
        ⟨plain, index, exitFanData profile, sourceSlotFin sourceSlot⟩

/-- All finite prefixes produced by one source clause, in the template's
clause-major and literal-minor incidence order. -/
def clauseDescriptors (profile : DirectedClauseProfile) :
    List Descriptor :=
  let drawing :=
    templateDrawingOfClauseProfile (clauseProfile profile)
  (List.finRange drawing.incidences.length).map
    (descriptorAt profile)

@[simp] theorem clauseDescriptors_length
    (profile : DirectedClauseProfile) :
    (clauseDescriptors profile).length =
      (templateDrawingOfClauseProfile
        (clauseProfile profile)).incidences.length := by
  simp [clauseDescriptors]

/-- Figure 9 ignores distinct-variable markers, first applies the semantic
clockwise clause permutation, and then expands the clause to its complete
finite incidence-prefix block. -/
def tokenBlock : FormulaShapeDirectionOrdering.Token → List Descriptor
  | .clause profile => clauseDescriptors (orderedDirectedProfile profile)
  | .variable => []

/-- Complete finite prefix stream for a direction-aware formula shape. -/
def descriptors (source : List FormulaShapeDirectionOrdering.Token) :
    List Descriptor :=
  source.flatMap tokenBlock

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
