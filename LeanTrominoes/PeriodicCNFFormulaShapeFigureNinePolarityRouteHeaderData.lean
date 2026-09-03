/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingData
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixData

/-! # Finite Figure 9 and polarity route headers -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteHeader

open UnaryProgramClauseProfile
open FormulaShapeDirectionOrdering
open ClauseProfilePolarityRouteOperation
open PlanarOneInThreeNoUnitsFigureNine
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeFigureNineFinalClauseOrdering

/-- Zero-based source position selected by a polarity descriptor. -/
def sourceSlotNat : SourceLiteralSlot → Nat
  | .first => 0
  | .second => 1
  | .third => 2

/-- Every emitted polarity descriptor selects a genuine literal of its
source clause. -/
theorem descriptor_sourceSlotNat_lt
    (profile : ClauseProfile)
    (descriptor : ClauseProfilePolarityRouteOperation.Descriptor)
    (member : descriptor ∈
      ClauseProfilePolarityRouteOperation.descriptors profile) :
    sourceSlotNat descriptor.sourceSlot < profile.literals.length := by
  rcases descriptor with ⟨sourceSlot, operation⟩
  cases profile with
  | unary first =>
      by_cases compatible : first.value =
          ClauseProfilePolarityNormalization.normalizedPolarity 0 <;>
        simp_all [ClauseProfilePolarityRouteOperation.descriptors,
          ClauseProfilePolarityRouteOperation.clauseRouteBlocks,
          ClauseProfilePolarityRouteOperation.complementRouteBlocks,
          ClauseProfilePolarityRouteOperation.normalizedDescriptor,
          sourceSlotNat, ClauseProfile.literals];
        cases sourceSlot <;> simp_all
  | binary first second =>
      by_cases firstCompatible :
          first.value =
            ClauseProfilePolarityNormalization.normalizedPolarity 0 <;>
        by_cases secondCompatible :
          second.value =
            ClauseProfilePolarityNormalization.normalizedPolarity 1 <;>
        simp_all [ClauseProfilePolarityRouteOperation.descriptors,
          ClauseProfilePolarityRouteOperation.clauseRouteBlocks,
          ClauseProfilePolarityRouteOperation.complementRouteBlocks,
          ClauseProfilePolarityRouteOperation.normalizedDescriptor,
          sourceSlotNat, ClauseProfile.literals] <;>
        cases sourceSlot <;> simp_all
  | ternary first second third =>
      by_cases firstCompatible :
          first.value =
            ClauseProfilePolarityNormalization.normalizedPolarity 0 <;>
        by_cases secondCompatible :
          second.value =
            ClauseProfilePolarityNormalization.normalizedPolarity 1 <;>
        by_cases thirdCompatible :
          third.value =
            ClauseProfilePolarityNormalization.normalizedPolarity 2 <;>
        simp_all [ClauseProfilePolarityRouteOperation.descriptors,
          ClauseProfilePolarityRouteOperation.clauseRouteBlocks,
          ClauseProfilePolarityRouteOperation.complementRouteBlocks,
          ClauseProfilePolarityRouteOperation.normalizedDescriptor,
          sourceSlotNat, ClauseProfile.literals] <;>
        cases sourceSlot <;> simp_all

/-- One final routed incidence header: its polarity operation together with
the finite Figure 9 source prefix on which that operation acts. -/
structure Header where
  polarity : ClauseProfilePolarityRouteOperation.Descriptor
  figurePrefix : FormulaShapeFigureNineRoutePrefix.Descriptor
  deriving DecidableEq, Fintype, Inhabited

/-- Attach one polarity descriptor to the selected source incidence of its
Figure 9 clause.  The fallback is unreachable on genuine aligned blocks. -/
def headerOf (prefixes : List FormulaShapeFigureNineRoutePrefix.Descriptor)
    (polarity : ClauseProfilePolarityRouteOperation.Descriptor) : Header :=
  ⟨polarity,
    prefixes.getD (sourceSlotNat polarity.sourceSlot) default⟩

@[simp] theorem headerOf_polarity
    (prefixes : List FormulaShapeFigureNineRoutePrefix.Descriptor)
    (polarity : ClauseProfilePolarityRouteOperation.Descriptor) :
    (headerOf prefixes polarity).polarity = polarity :=
  rfl

/-- On a correctly sized Figure 9 clause-prefix block, header selection is a
genuine list lookup rather than the total fallback. -/
theorem headerOf_figurePrefix_eq_get
    (profile : ClauseProfile)
    (prefixes : List FormulaShapeFigureNineRoutePrefix.Descriptor)
    (lengthEq : prefixes.length = profile.literals.length)
    (polarity : ClauseProfilePolarityRouteOperation.Descriptor)
    (member : polarity ∈
      ClauseProfilePolarityRouteOperation.descriptors profile) :
    let selectedIndex : Fin prefixes.length :=
      ⟨sourceSlotNat polarity.sourceSlot, by
        rw [lengthEq]
        exact descriptor_sourceSlotNat_lt profile polarity member⟩
    (headerOf prefixes polarity).figurePrefix =
      prefixes.get selectedIndex := by
  dsimp only
  unfold headerOf
  dsimp only
  let selectedIndex : Fin prefixes.length :=
    ⟨sourceSlotNat polarity.sourceSlot, by
      rw [lengthEq]
      exact descriptor_sourceSlotNat_lt profile polarity member⟩
  change prefixes.getD selectedIndex default = prefixes.get selectedIndex
  exact List.getD_eq_get prefixes default selectedIndex

/-- Expand one Figure 9 clause's source-prefix block through polarity
normalization. -/
def clauseHeaders
    (profile : ClauseProfile)
    (prefixes : List FormulaShapeFigureNineRoutePrefix.Descriptor) :
    List Header :=
  (ClauseProfilePolarityRouteOperation.descriptors profile).map
    (headerOf prefixes)

/-- Consume one source-prefix block per Figure 9 clause and emit its final
polarity-normalized routed headers. -/
def headers :
    List ClauseProfile →
      List FormulaShapeFigureNineRoutePrefix.Descriptor → List Header
  | [], _ => []
  | profile :: profiles, prefixes =>
      let count := profile.literals.length
      clauseHeaders profile (prefixes.take count) ++
        headers profiles (prefixes.drop count)

/-- Header annotation preserves the complete polarity descriptor stream. -/
@[simp] theorem headers_map_polarity
    (profiles : List ClauseProfile)
    (prefixes : List FormulaShapeFigureNineRoutePrefix.Descriptor) :
    (headers profiles prefixes).map Header.polarity =
      profiles.flatMap ClauseProfilePolarityRouteOperation.descriptors := by
  induction profiles generalizing prefixes with
  | nil => rfl
  | cons profile profiles induction =>
      rw [headers, List.map_append, List.flatMap_cons,
        induction]
      congr 1
      unfold clauseHeaders
      rw [List.map_map]
      let polarityDescriptors :=
        ClauseProfilePolarityRouteOperation.descriptors profile
      calc
        List.map
            (Header.polarity ∘
              headerOf (List.take profile.literals.length prefixes))
            polarityDescriptors =
          List.map id polarityDescriptors := by
            apply List.map_congr_left
            intro polarity _polarityMember
            exact headerOf_polarity _ polarity
        _ = polarityDescriptors := List.map_id polarityDescriptors

/-- Consume the same original Figure 9 prefix blocks after applying the
second, unit-elimination-induced clockwise permutation inside each generated
clause. -/
def finalHeaders :
    List ClauseProfile →
      List FormulaShapeFigureNineRoutePrefix.Descriptor → List Header
  | [], _ => []
  | profile :: profiles, prefixes =>
      let count := profile.literals.length
      clauseHeaders (reorderProfile profile)
          (reorderList (prefixes.take count)) ++
        finalHeaders profiles (prefixes.drop count)

/-- Final header annotation preserves the polarity schedule of the reordered
Figure 9 clause profiles. -/
@[simp] theorem finalHeaders_map_polarity
    (profiles : List ClauseProfile)
    (prefixes : List FormulaShapeFigureNineRoutePrefix.Descriptor) :
    (finalHeaders profiles prefixes).map Header.polarity =
      profiles.flatMap fun profile =>
        ClauseProfilePolarityRouteOperation.descriptors
          (reorderProfile profile) := by
  induction profiles generalizing prefixes with
  | nil => rfl
  | cons profile profiles induction =>
      rw [finalHeaders, List.map_append, List.flatMap_cons, induction]
      congr 1
      unfold clauseHeaders
      rw [List.map_map]
      let polarityDescriptors :=
        ClauseProfilePolarityRouteOperation.descriptors
          (reorderProfile profile)
      calc
        List.map
            (Header.polarity ∘
              headerOf
                (reorderList
                  (List.take profile.literals.length prefixes)))
            polarityDescriptors =
          List.map id polarityDescriptors := by
            apply List.map_congr_left
            intro polarity _polarityMember
            exact headerOf_polarity _ polarity
        _ = polarityDescriptors := List.map_id polarityDescriptors

/-- Finite literal profile of one embedded Figure 9 output clause. -/
def embeddedClauseProfile
    (clause : PlanarThreeSAT.EmbeddedClause FigureNineNoUnitsVariable) :
    ClauseProfile :=
  FormulaShapeOfFormula.clauseProfile
    (clause.literals.map fun literal =>
      { nextSlice := false, value := literal.2 })

/-- Figure 9 output clauses in their exact template presentation order. -/
def figureClauseProfiles (profile : DirectedClauseProfile) :
    List ClauseProfile :=
    (templateDrawingOfClauseProfile
    (FormulaShapeFigureNineRoutePrefix.clauseProfile profile)).formula.map
      embeddedClauseProfile

/-- Figure 9 output profiles after the final clockwise clause permutation. -/
def finalFigureClauseProfiles (profile : DirectedClauseProfile) :
    List ClauseProfile :=
  (figureClauseProfiles profile).map reorderProfile

/-- Complete finite final route headers generated by one directed source
clause profile. -/
def sourceClauseHeaders (profile : DirectedClauseProfile) : List Header :=
  let ordered :=
    FormulaShapeFigureNineRoutePrefix.orderedDirectedProfile profile
  finalHeaders (figureClauseProfiles ordered)
    (FormulaShapeFigureNineRoutePrefix.clauseDescriptors ordered)

@[simp] theorem sourceClauseHeaders_map_polarity
    (profile : DirectedClauseProfile) :
    (sourceClauseHeaders profile).map Header.polarity =
      (finalFigureClauseProfiles
        (FormulaShapeFigureNineRoutePrefix.orderedDirectedProfile
          profile)).flatMap
        ClauseProfilePolarityRouteOperation.descriptors := by
  simp [sourceClauseHeaders, finalFigureClauseProfiles,
    List.flatMap_map]

/-- Variable markers do not generate clauses; each directed clause expands
to all of its final finite route headers. -/
def tokenBlock : FormulaShapeDirectionOrdering.Token → List Header
  | .clause profile => sourceClauseHeaders profile
  | .variable => []

/-- Complete finite route-header stream for a direction-aware source shape. -/
def sourceHeaders (source : List FormulaShapeDirectionOrdering.Token) :
    List Header :=
  source.flatMap tokenBlock

end FormulaShapeFigureNinePolarityRouteHeader
end PeriodicCNF
end LeanTrominoes
