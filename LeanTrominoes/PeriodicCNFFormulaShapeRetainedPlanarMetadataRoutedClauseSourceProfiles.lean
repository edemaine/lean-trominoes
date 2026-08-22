/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseCurrentProfiles
import LeanTrominoes.PeriodicCNFPlanarWidth
import LeanTrominoes.IndexedListScan

/-! # Routed clause profiles in source presentation order -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open UnaryProgramClauseProfile

private theorem map_zipIdx_filter_fst
    {Value Output : Type}
    (values : List Value)
    (selected : Value → Bool)
    (output : Value → Output) :
    ((values.zipIdx.filter fun tagged => selected tagged.1).map
        fun tagged => output tagged.1) =
      (values.filter selected).map output := by
  simpa only [← List.map_eq_flatMap] using
    (IndexedListScan.zipIdx_filter_fst_flatMap
      values selected (fun value => [output value]))

/-- At a tagged source clause and any neighboring translation, routed-clause
profiles are its original literal polarities in order with all slice bits
cleared. -/
theorem routedClauseCurrentProfiles_eq_taggedClause
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedMember : taggedClause ∈ source.clauses.zipIdx)
    (translate : Cell) :
    routedClauseCurrentProfiles source (taggedClause.2, translate) =
      taggedClause.1.map fun literal =>
        (⟨false, literal.value⟩ : LiteralProfile) := by
  unfold routedClauseCurrentProfiles clauseRouteOccurrencesAt
  simp only [List.map_map, Function.comp_def]
  calc
    _ = ((PeriodicCNF.incidencesWithMetadata source).filter
          fun incidence =>
            decide (incidence.clauseIndex = taggedClause.2)).map
          (fun incidence =>
            (⟨false, incidence.literal.value⟩ : LiteralProfile)) :=
      map_zipIdx_filter_fst _ _ _
    _ = _ := by
      rw [PeriodicOrthocrossing.incidencesWithMetadata_filter_clauseIndex
        source taggedClause taggedMember]
      let output := fun literal : PeriodicLiteral Variable =>
        (⟨false, literal.value⟩ : LiteralProfile)
      have mapped := congrArg (List.map output)
        (List.zipIdx_map_fst 0 taggedClause.1)
      simpa only [List.map_map, Function.comp_def] using mapped

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
