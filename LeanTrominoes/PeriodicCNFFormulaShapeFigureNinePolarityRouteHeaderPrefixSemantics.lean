/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderData
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaSemantics

/-! # Figure 9 route headers select genuine finite prefixes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteHeader

open ClauseProfilePolarityRouteOperation
open FormulaShapeFigureNineRoutePrefix
open PlanarThreeSAT
open UnaryProgramClauseProfile

private theorem headers_figurePrefix_mem
    (profiles : List ClauseProfile)
    (prefixes : List FormulaShapeFigureNineRoutePrefix.Descriptor)
    (lengthEq : prefixes.length =
      (profiles.map fun profile => profile.literals.length).sum)
    (header : Header) (headerMember : header ∈ headers profiles prefixes) :
    header.figurePrefix ∈ prefixes := by
  induction profiles generalizing prefixes with
  | nil => simp [headers] at headerMember
  | cons profile profiles induction =>
      simp only [headers, List.mem_append] at headerMember
      rcases headerMember with currentMember | laterMember
      · unfold clauseHeaders at currentMember
        rcases List.mem_map.mp currentMember with
          ⟨polarity, polarityMember, rfl⟩
        have countLe : profile.literals.length ≤ prefixes.length := by
          rw [lengthEq]
          simp
        have takeLength :
            (prefixes.take profile.literals.length).length =
              profile.literals.length := by
          simp [Nat.min_eq_left countLe]
        rw [headerOf_figurePrefix_eq_get
          profile (prefixes.take profile.literals.length)
          takeLength polarity polarityMember]
        exact List.mem_of_mem_take (List.get_mem _ _)
      · have droppedMember : header.figurePrefix ∈
            prefixes.drop profile.literals.length := by
          apply induction (prefixes := prefixes.drop profile.literals.length)
          · rw [List.length_drop, lengthEq]
            simp
          · exact laterMember
        rw [← List.take_append_drop profile.literals.length prefixes]
        exact List.mem_append_right _ droppedMember

private theorem templateClause_arity_two_or_three
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    ∀ clause ∈
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          (clauseProfile profile)).formula,
      clause.literals.length = 2 ∨ clause.literals.length = 3 := by
  cases profile with
  | unary first direction =>
      simp only [FormulaShapeFigureNineRoutePrefix.clauseProfile,
        PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile]
      clear direction
      native_decide +revert
  | binary first firstDirection second secondDirection =>
      simp only [FormulaShapeFigureNineRoutePrefix.clauseProfile,
        PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile]
      clear firstDirection secondDirection
      native_decide +revert
  | ternary first firstDirection second secondDirection third thirdDirection =>
      simp only [FormulaShapeFigureNineRoutePrefix.clauseProfile,
        PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile]
      clear firstDirection secondDirection thirdDirection
      native_decide +revert

private theorem clauseDescriptors_length_eq_figureClauseProfiles
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    (clauseDescriptors profile).length =
      ((figureClauseProfiles profile).map fun generated =>
        generated.literals.length).sum := by
  simp [clauseDescriptors, figureClauseProfiles,
    EmbeddedCNFIncidenceDrawing.incidences, embeddedCNFIncidences]
  apply congrArg List.sum
  let formula :=
    (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
      (clauseProfile profile)).formula
  calc
    formula.zipIdx.map (fun taggedClause =>
        taggedClause.1.literals.length) =
      formula.map (fun clause => clause.literals.length) := by
      have mapped := congrArg
        (List.map fun clause => clause.literals.length)
        (List.zipIdx_map_fst 0 formula)
      change formula.zipIdx.map
          ((fun clause => clause.literals.length) ∘ Prod.fst) =
        formula.map (fun clause => clause.literals.length)
      simpa only [List.map_map] using mapped
    _ = formula.map
        ((fun generated => generated.literals.length) ∘
          embeddedClauseProfile) := by
      apply List.map_congr_left
      intro clause clauseMember
      have arity := templateClause_arity_two_or_three
        profile clause clauseMember
      change clause.literals.length =
        (embeddedClauseProfile clause).literals.length
      unfold embeddedClauseProfile
      rw [FormulaShapeOfFormula.clauseProfile_literals]
      · simp
      · have positive : 0 < clause.literals.length := by
          rcases arity with arity | arity <;> omega
        apply List.ne_nil_of_length_pos
        simpa only [List.length_map] using positive
      · rcases arity with arity | arity <;> simp_all

/-- Every prefix selected by a final polarity header is one of the exact
`descriptorAt` entries of its clockwise parent Figure 9 template. -/
theorem sourceClauseHeaders_figurePrefix_mem_clauseDescriptors
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (header : Header) (headerMember : header ∈ sourceClauseHeaders profile) :
    header.figurePrefix ∈
      clauseDescriptors (orderedDirectedProfile profile) := by
  unfold sourceClauseHeaders at headerMember
  exact headers_figurePrefix_mem
    (figureClauseProfiles (orderedDirectedProfile profile))
    (clauseDescriptors (orderedDirectedProfile profile))
    (clauseDescriptors_length_eq_figureClauseProfiles
      (orderedDirectedProfile profile))
    header headerMember

/-- Hence every selected prefix exposes an exact dependent template index,
not merely a total `getD` fallback value. -/
theorem exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (header : Header) (headerMember : header ∈ sourceClauseHeaders profile) :
    ∃ index : Fin
        (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          (clauseProfile (orderedDirectedProfile profile))).incidences.length,
      descriptorAt (orderedDirectedProfile profile) index =
        header.figurePrefix := by
  have prefixMember :=
    sourceClauseHeaders_figurePrefix_mem_clauseDescriptors
      profile header headerMember
  unfold clauseDescriptors at prefixMember
  rw [List.mem_map] at prefixMember
  rcases prefixMember with ⟨index, _indexMember, descriptorEq⟩
  exact ⟨index, descriptorEq⟩

end FormulaShapeFigureNinePolarityRouteHeader
end PeriodicCNF
end LeanTrominoes
