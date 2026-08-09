import LeanTrominoes.PeriodicOneInThreePolarityNormalizationOriginalOccurrenceOrder
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteOrders

/-!
# Routed original occurrences under polarity normalization

The logical occurrence pairing identifies equal source and output slots.  For
route geometry, an output occurrence must additionally retain the clause
metadata that selects its raw route.  This module enumerates literals directly
from the metadata list, proves that forgetting metadata recovers the ordinary
occurrence table, and pairs those enriched output occurrences with the refined
source occurrence table in the same slots.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

abbrev TaggedMetadataOccurrence (Variable : Type*) :=
  PeriodicOneInThreeToThreeDM.TaggedOccurrence
      (PolarityNormalizedVariable Variable) ×
    ClauseMetadata Variable

/-- Enumerate every literal of a metadata-indexed clause list while retaining
the metadata entry that owns it. -/
def taggedMetadataLiteralsFrom {Variable : Type*} (start : Nat)
    (metadata : List (ClauseMetadata Variable)) :
    List (TaggedMetadataOccurrence Variable) :=
  metadata.zipIdx start |>.flatMap fun taggedClause =>
    taggedClause.1.clause.literals.zipIdx.map fun taggedLiteral =>
      ((taggedLiteral.1, taggedClause.2, taggedLiteral.2), taggedClause.1)

/-- Forgetting metadata from the enriched enumeration gives the ordinary
tagged-literal enumeration of the projected clauses. -/
theorem taggedMetadataLiteralsFrom_map_output
    {Variable : Type*} (start : Nat)
    (metadata : List (ClauseMetadata Variable)) :
    (taggedMetadataLiteralsFrom start metadata).map Prod.fst =
      PeriodicOneInThreePolarityNormalization.taggedLiteralsFrom start
        (metadata.map fun entry => entry.clause.literals) := by
  induction metadata generalizing start with
  | nil => rfl
  | cons head rest induction =>
      rw [show
        taggedMetadataLiteralsFrom start (head :: rest) =
          (head.clause.literals.zipIdx.map fun taggedLiteral =>
            ((taggedLiteral.1, start, taggedLiteral.2), head)) ++
            taggedMetadataLiteralsFrom (start + 1) rest by
          simp [taggedMetadataLiteralsFrom]]
      rw [List.map_append, induction (start + 1)]
      simp [PeriodicOneInThreePolarityNormalization.taggedLiteralsFrom,
        List.map_map, Function.comp_def]

/-- Metadata-enriched raw occurrences of one embedded original variable. -/
def rawOriginalMetadataOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) : List (TaggedMetadataOccurrence Variable) :=
  (taggedMetadataLiteralsFrom 0
      (clauseMetadata source sourcePlacement routes)).filter
    fun tagged => tagged.1.1.atom = Sum.inl atom

private theorem map_fst_filter_by_fst
    {First Second : Type*} (values : List (First × Second))
    (predicate : First → Bool) :
    ((values.filter fun value => predicate value.1).map Prod.fst) =
      (values.map Prod.fst).filter predicate := by
  induction values with
  | nil => rfl
  | cons head rest induction =>
      by_cases selected : predicate head.1 = true
      · simp [selected, induction]
      · simp [selected, induction]

/-- Forgetting metadata from the selected original occurrences recovers the
ordinary raw-formula occurrence list. -/
theorem rawOriginalMetadataOccurrences_map_output
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (rawOriginalMetadataOccurrences
        source sourcePlacement routes atom).map Prod.fst =
      PeriodicOneInThreeToThreeDM.occurrencesOf
        (rawFormula source sourcePlacement routes).erase (Sum.inl atom) := by
  unfold rawOriginalMetadataOccurrences
  rw [show
    ((taggedMetadataLiteralsFrom 0
        (clauseMetadata source sourcePlacement routes)).filter
          fun tagged => tagged.1.1.atom = Sum.inl atom).map Prod.fst =
      ((taggedMetadataLiteralsFrom 0
        (clauseMetadata source sourcePlacement routes)).map Prod.fst).filter
          (fun tagged => tagged.1.atom = Sum.inl atom) by
      simpa only [] using
        (map_fst_filter_by_fst
          (taggedMetadataLiteralsFrom 0
            (clauseMetadata source sourcePlacement routes))
          (fun tagged :
              PeriodicOneInThreeToThreeDM.TaggedOccurrence
                (PolarityNormalizedVariable Variable) =>
            decide (tagged.1.atom = Sum.inl atom)))]
  rw [taggedMetadataLiteralsFrom_map_output]
  have clausesEq :
      (clauseMetadata source sourcePlacement routes).map
          (fun entry => entry.clause.literals) =
        (rawFormula source sourcePlacement routes).erase.clauses := by
    change
      (clauseMetadata source sourcePlacement routes).map
          (fun entry => entry.clause.literals) =
        (rawFormula source sourcePlacement routes).clauses.map
          PositionedPeriodicClause.literals
    calc
      (clauseMetadata source sourcePlacement routes).map
          (fun entry => entry.clause.literals) =
          ((clauseMetadata source sourcePlacement routes).map
            ClauseMetadata.clause).map
              PositionedPeriodicClause.literals := by
        rw [List.map_map]
        congr 1
      _ = (rawFormula source sourcePlacement routes).clauses.map
            PositionedPeriodicClause.literals :=
        congrArg
          (List.map PositionedPeriodicClause.literals)
          (clauseMetadata_clauses source sourcePlacement routes)
  rw [clausesEq]
  rfl

/-- The enriched raw occurrence list has the same length as the refined
source occurrence list. -/
theorem rawOriginalMetadataOccurrences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (rawOriginalMetadataOccurrences
        source sourcePlacement routes atom).length =
      (PeriodicOneInThreeToThreeDM.occurrencesOf
        (refinedSource source sourcePlacement).erase atom).length := by
  let refined := (refinedSource source sourcePlacement).erase
  let pairs :=
    PeriodicOneInThreePolarityNormalization.formulaOriginalOccurrencePairs
      refined atom
  have outputEq :=
    PeriodicOneInThreePolarityNormalization.formulaOriginalOccurrencePairs_fst
      refined atom
  have sourceEq :=
    PeriodicOneInThreePolarityNormalization.formulaOriginalOccurrencePairs_snd
      refined atom
  calc
    (rawOriginalMetadataOccurrences
        source sourcePlacement routes atom).length =
        (PeriodicOneInThreeToThreeDM.occurrencesOf
          (rawFormula source sourcePlacement routes).erase
          (Sum.inl atom)).length := by
      rw [← rawOriginalMetadataOccurrences_map_output]
      simp
    _ = (PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThreePolarityNormalization.formula refined)
          (Sum.inl atom)).length := by
      simp [rawFormula, refined]
    _ = (pairs.map Prod.fst).length := by rw [outputEq]
    _ = pairs.length := by simp
    _ = (pairs.map Prod.snd).length := by simp
    _ = (PeriodicOneInThreeToThreeDM.occurrencesOf refined atom).length := by
      rw [sourceEq]
    _ = (PeriodicOneInThreeToThreeDM.occurrencesOf
          (refinedSource source sourcePlacement).erase atom).length := rfl

abbrev RawOriginalOccurrencePair (Variable : Type*) :=
  TaggedMetadataOccurrence Variable ×
    PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable

/-- Pair enriched raw occurrences with refined source occurrences in their
common global occurrence order. -/
def rawOriginalOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) : List (RawOriginalOccurrencePair Variable) :=
  (rawOriginalMetadataOccurrences source sourcePlacement routes atom).zip
    (PeriodicOneInThreeToThreeDM.occurrencesOf
      (refinedSource source sourcePlacement).erase atom)

private theorem map_fst_zip_of_length_eq
    {First Second : Type*} (first : List First) (second : List Second)
    (lengthEq : first.length = second.length) :
    (first.zip second).map Prod.fst = first := by
  induction first generalizing second with
  | nil => rfl
  | cons head rest induction =>
      cases second with
      | nil => simp at lengthEq
      | cons secondHead secondRest =>
          simp only [List.length_cons, Nat.succ.injEq] at lengthEq
          simp [induction secondRest lengthEq]

private theorem map_snd_zip_of_length_eq
    {First Second : Type*} (first : List First) (second : List Second)
    (lengthEq : first.length = second.length) :
    (first.zip second).map Prod.snd = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons head rest => simp at lengthEq
  | cons head rest induction =>
      cases second with
      | nil => simp at lengthEq
      | cons secondHead secondRest =>
          simp only [List.length_cons, Nat.succ.injEq] at lengthEq
          simp [induction secondRest lengthEq]

theorem rawOriginalOccurrencePairs_map_metadata
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (rawOriginalOccurrencePairs source sourcePlacement routes atom).map
        Prod.fst =
      rawOriginalMetadataOccurrences source sourcePlacement routes atom := by
  apply map_fst_zip_of_length_eq
  exact rawOriginalMetadataOccurrences_length
    source sourcePlacement routes atom

theorem rawOriginalOccurrencePairs_map_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (rawOriginalOccurrencePairs source sourcePlacement routes atom).map
        Prod.snd =
      PeriodicOneInThreeToThreeDM.occurrencesOf
        (refinedSource source sourcePlacement).erase atom := by
  apply map_snd_zip_of_length_eq
  exact rawOriginalMetadataOccurrences_length
    source sourcePlacement routes atom

/-- Every raw occurrence of an embedded original variable has, in the same
slot, both its owning clause metadata and its paired refined-source
occurrence. -/
theorem exists_metadata_source_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (output :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (PolarityNormalizedVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
        (rawFormula source sourcePlacement routes).erase
        (Sum.inl atom) slot = some output) :
    ∃ metadata sourceOccurrence,
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (refinedSource source sourcePlacement).erase atom slot =
        some sourceOccurrence ∧
      ((output, metadata), sourceOccurrence) ∈
        rawOriginalOccurrencePairs source sourcePlacement routes atom := by
  let pairs := rawOriginalOccurrencePairs
    source sourcePlacement routes atom
  have outputLookup :
      (pairs.map fun pair => pair.1.1)[slot.index]? = some output := by
    rw [show
      pairs.map (fun pair => pair.1.1) =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (rawFormula source sourcePlacement routes).erase
          (Sum.inl atom) by
        rw [show pairs.map (fun pair => pair.1.1) =
            (pairs.map Prod.fst).map Prod.fst by
          simp [List.map_map, Function.comp_def]]
        rw [rawOriginalOccurrencePairs_map_metadata,
          rawOriginalMetadataOccurrences_map_output]]
    exact lookup
  rw [List.getElem?_map, Option.map_eq_some_iff] at outputLookup
  rcases outputLookup with ⟨pair, pairLookup, outputEq⟩
  have sourceLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (refinedSource source sourcePlacement).erase atom slot =
        some pair.2 := by
    change
      (PeriodicOneInThreeToThreeDM.occurrencesOf
        (refinedSource source sourcePlacement).erase atom)[slot.index]? =
          some pair.2
    rw [← rawOriginalOccurrencePairs_map_source
      source sourcePlacement routes atom,
      List.getElem?_map, pairLookup]
    rfl
  refine ⟨pair.1.2, pair.2, sourceLookup, ?_⟩
  rw [← outputEq]
  exact List.mem_iff_getElem?.mpr ⟨slot.index, pairLookup⟩

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
