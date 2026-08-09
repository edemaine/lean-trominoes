import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRoutedOriginalOccurrences

/-!
# Source-clause provenance for routed original occurrences

The metadata-enriched output list and the refined source occurrence list are
paired by global position.  This file proves that the two entries of every
pair belong to the same source-clause block.  Equivalently, mapping both lists
to their retained source-clause indices gives exactly the same sequence.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

/-- Metadata generation over a suffix of positioned clauses, retaining the
absolute source-clause index. -/
def formulaClauseMetadataFrom {Variable : Type*}
    (positions : Positions Variable) (sourceStart : Nat)
    (clauses : List (PositionedPeriodicClause Variable)) :
    List (ClauseMetadata Variable) :=
  clauses.zipIdx sourceStart |>.flatMap fun taggedSource =>
    clauseMetadataFor positions taggedSource.2 taggedSource.1

theorem formulaClauseMetadataFrom_cons {Variable : Type*}
    (positions : Positions Variable) (sourceStart : Nat)
    (clause : PositionedPeriodicClause Variable)
    (rest : List (PositionedPeriodicClause Variable)) :
    formulaClauseMetadataFrom positions sourceStart (clause :: rest) =
      clauseMetadataFor positions sourceStart clause ++
        formulaClauseMetadataFrom positions (sourceStart + 1) rest := by
  rfl

theorem taggedMetadataLiteralsFrom_append
    {Variable : Type*} (start : Nat)
    (first second : List (ClauseMetadata Variable)) :
    taggedMetadataLiteralsFrom start (first ++ second) =
      taggedMetadataLiteralsFrom start first ++
        taggedMetadataLiteralsFrom (start + first.length) second := by
  simp [taggedMetadataLiteralsFrom, List.zipIdx_append]

/-- Every entry of a single metadata block retains that block's source-clause
index. -/
theorem clauseMetadataFor_sourceClauseIndex
    {Variable : Type*}
    (positions : Positions Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ clauseMetadataFor positions sourceClauseIndex sourceClause) :
    metadata.sourceClauseIndex = sourceClauseIndex := by
  unfold clauseMetadataFor at metadataMember
  simp only [List.mem_cons] at metadataMember
  rcases metadataMember with metadataEq | metadataMember
  · subst metadata
    rfl
  · exact
      (complementClauseMetadataFrom_source_eq positions sourceClause
        sourceClauseIndex 0 sourceClause.literals metadataMember).2

/-- The metadata retained by any enriched literal is a member of the
enumerated metadata list. -/
theorem metadata_mem_of_mem_taggedMetadataLiteralsFrom
    {Variable : Type*}
    (start : Nat) (metadata : List (ClauseMetadata Variable))
    {tagged : TaggedMetadataOccurrence Variable}
    (taggedMember : tagged ∈ taggedMetadataLiteralsFrom start metadata) :
    tagged.2 ∈ metadata := by
  simp only [taggedMetadataLiteralsFrom, List.mem_flatMap,
    List.mem_map] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, taggedClauseMember, taggedLiteral,
      _taggedLiteralMember, taggedEq⟩
  subst tagged
  exact List.fst_mem_of_mem_zipIdx taggedClauseMember

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

/-- Original-variable occurrences selected from one metadata block. -/
def metadataBlockOriginalOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (positions : Positions Variable)
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    List (TaggedMetadataOccurrence Variable) :=
  (taggedMetadataLiteralsFrom outputStart
      (clauseMetadataFor positions sourceClauseIndex sourceClause)).filter
    fun tagged => tagged.1.1.atom = Sum.inl atom

/-- Forgetting metadata from a single selected block gives the logical
original-occurrence block used by the slot pairing. -/
theorem metadataBlockOriginalOccurrences_map_output
    {Variable : Type*} [DecidableEq Variable]
    (positions : Positions Variable)
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (metadataBlockOriginalOccurrences positions atom outputStart
        sourceClauseIndex sourceClause).map Prod.fst =
      PeriodicOneInThreePolarityNormalization.outputBlockOccurrences
        atom outputStart sourceClauseIndex sourceClause.literals := by
  unfold metadataBlockOriginalOccurrences
  rw [show
    ((taggedMetadataLiteralsFrom outputStart
      (clauseMetadataFor positions sourceClauseIndex sourceClause)).filter
        fun tagged => tagged.1.1.atom = Sum.inl atom).map Prod.fst =
      ((taggedMetadataLiteralsFrom outputStart
        (clauseMetadataFor positions sourceClauseIndex sourceClause)).map
          Prod.fst).filter
        (fun tagged => tagged.1.atom = Sum.inl atom) by
      simpa only [] using
        (map_fst_filter_by_fst
          (taggedMetadataLiteralsFrom outputStart
            (clauseMetadataFor positions sourceClauseIndex sourceClause))
          (fun tagged :
              PeriodicOneInThreeToThreeDM.TaggedOccurrence
                (PolarityNormalizedVariable Variable) =>
            decide (tagged.1.atom = Sum.inl atom)))]
  rw [taggedMetadataLiteralsFrom_map_output]
  have clausesEq :
      (clauseMetadataFor positions sourceClauseIndex sourceClause).map
          (fun entry => entry.clause.literals) =
        PeriodicOneInThreePolarityNormalization.clauseClauses
          sourceClauseIndex sourceClause.literals := by
    calc
      _ = ((clauseMetadataFor positions sourceClauseIndex sourceClause).map
            ClauseMetadata.clause).map
              PositionedPeriodicClause.literals := by
        rw [List.map_map]
        congr 1
      _ = (clauseBlock positions sourceClauseIndex sourceClause).map
            PositionedPeriodicClause.literals :=
        congrArg (List.map PositionedPeriodicClause.literals)
          (clauseMetadataFor_clauses positions sourceClauseIndex sourceClause)
      _ = _ := clauseBlock_literals positions sourceClauseIndex sourceClause
  rw [clausesEq]
  rfl

private theorem map_eq_replicate_of_constant
    {Value Target : Type*} (values : List Value)
    (function : Value → Target) (constant : Target)
    (constantOn : ∀ value ∈ values, function value = constant) :
    values.map function = List.replicate values.length constant := by
  induction values with
  | nil => rfl
  | cons head rest induction =>
      rw [List.map_cons, List.length_cons, List.replicate_succ]
      rw [constantOn head (by simp)]
      exact congrArg (constant :: ·)
        (induction (by
          intro value valueMember
          exact constantOn value (by simp [valueMember])))

/-- Every selected metadata literal in one block maps to that block's source
clause index. -/
theorem metadataBlockOriginalOccurrences_sourceIndices
    {Variable : Type*} [DecidableEq Variable]
    (positions : Positions Variable)
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (metadataBlockOriginalOccurrences positions atom outputStart
        sourceClauseIndex sourceClause).map
          (fun tagged => tagged.2.sourceClauseIndex) =
      List.replicate
        (metadataBlockOriginalOccurrences positions atom outputStart
          sourceClauseIndex sourceClause).length
        sourceClauseIndex := by
  apply map_eq_replicate_of_constant
  intro tagged taggedMember
  apply clauseMetadataFor_sourceClauseIndex
    positions sourceClauseIndex sourceClause
  apply metadata_mem_of_mem_taggedMetadataLiteralsFrom outputStart
  exact (List.mem_filter.mp taggedMember).1

/-- Every source occurrence in one source clause maps to that clause's
presentation index. -/
theorem sourceClauseOccurrences_sourceIndices
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (sourceClauseIndex : Nat)
    (sourceClause : PeriodicClause Variable) :
    (PeriodicOneInThreePolarityNormalization.sourceClauseOccurrences
        atom sourceClauseIndex sourceClause).map
          (fun tagged => tagged.2.1) =
      List.replicate
        (PeriodicOneInThreePolarityNormalization.sourceClauseOccurrences
          atom sourceClauseIndex sourceClause).length
        sourceClauseIndex := by
  apply map_eq_replicate_of_constant
  intro tagged taggedMember
  unfold PeriodicOneInThreePolarityNormalization.sourceClauseOccurrences
    at taggedMember
  have mappedMember := (List.mem_filter.mp taggedMember).1
  rcases List.mem_map.mp mappedMember with
    ⟨sourceLiteral, _sourceLiteralMember, taggedEq⟩
  rw [← taggedEq]

/-- The selected metadata block and source clause have the same ordered
source-index sequence. -/
theorem metadataBlock_sourceIndices_eq_source
    {Variable : Type*} [DecidableEq Variable]
    (positions : Positions Variable)
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (metadataBlockOriginalOccurrences positions atom outputStart
        sourceClauseIndex sourceClause).map
          (fun tagged => tagged.2.sourceClauseIndex) =
      (PeriodicOneInThreePolarityNormalization.sourceClauseOccurrences
        atom sourceClauseIndex sourceClause.literals).map
          (fun tagged => tagged.2.1) := by
  rw [metadataBlockOriginalOccurrences_sourceIndices,
    sourceClauseOccurrences_sourceIndices]
  congr 1
  calc
    (metadataBlockOriginalOccurrences positions atom outputStart
        sourceClauseIndex sourceClause).length =
        (PeriodicOneInThreePolarityNormalization.outputBlockOccurrences
          atom outputStart sourceClauseIndex sourceClause.literals).length := by
      rw [← metadataBlockOriginalOccurrences_map_output
        (positions := positions)]
      simp
    _ = (PeriodicOneInThreePolarityNormalization.sourceClauseOccurrences
          atom sourceClauseIndex sourceClause.literals).length :=
      PeriodicOneInThreePolarityNormalization.outputBlockOccurrences_length
        atom outputStart sourceClauseIndex sourceClause.literals

/-- Across a positioned source suffix, enriched and source occurrences map to
the same sequence of retained source-clause indices. -/
theorem formulaMetadataOriginal_sourceIndices
    {Variable : Type*} [DecidableEq Variable]
    (positions : Positions Variable)
    (atom : Variable) (outputStart sourceStart : Nat)
    (clauses : List (PositionedPeriodicClause Variable)) :
    (((taggedMetadataLiteralsFrom outputStart
        (formulaClauseMetadataFrom positions sourceStart clauses)).filter
          fun tagged => tagged.1.1.atom = Sum.inl atom).map
            (fun tagged => tagged.2.sourceClauseIndex)) =
      ((PeriodicOneInThreePolarityNormalization.taggedLiteralsFrom
          sourceStart (clauses.map PositionedPeriodicClause.literals)).filter
        fun tagged => tagged.1.atom = atom).map
          (fun tagged => tagged.2.1) := by
  induction clauses generalizing outputStart sourceStart with
  | nil => rfl
  | cons clause rest induction =>
      rw [formulaClauseMetadataFrom_cons,
        taggedMetadataLiteralsFrom_append]
      rw [List.filter_append, List.map_append]
      change
        (metadataBlockOriginalOccurrences positions atom outputStart
            sourceStart clause).map
              (fun tagged => tagged.2.sourceClauseIndex) ++
          (((taggedMetadataLiteralsFrom
              (outputStart +
                (clauseMetadataFor positions sourceStart clause).length)
              (formulaClauseMetadataFrom positions (sourceStart + 1) rest)
            ).filter
              fun tagged => tagged.1.1.atom = Sum.inl atom).map
                (fun tagged => tagged.2.sourceClauseIndex)) = _
      rw [metadataBlock_sourceIndices_eq_source]
      rw [show
        PeriodicOneInThreePolarityNormalization.taggedLiteralsFrom
            sourceStart
            ((clause :: rest).map PositionedPeriodicClause.literals) =
          (clause.literals.zipIdx.map fun taggedLiteral =>
            (taggedLiteral.1, sourceStart, taggedLiteral.2)) ++
            PeriodicOneInThreePolarityNormalization.taggedLiteralsFrom
              (sourceStart + 1)
              (rest.map PositionedPeriodicClause.literals) by
          simp [PeriodicOneInThreePolarityNormalization.taggedLiteralsFrom]]
      rw [List.filter_append, List.map_append]
      apply congrArg₂ (fun first second => first ++ second)
      · rfl
      · exact induction
          (outputStart +
            (clauseMetadataFor positions sourceStart clause).length)
          (sourceStart + 1)

/-- The concrete raw metadata occurrence list and refined source occurrence
list have the same clause-index sequence. -/
theorem rawOriginalMetadataOccurrences_sourceIndices
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (rawOriginalMetadataOccurrences source sourcePlacement routes atom).map
        (fun tagged => tagged.2.sourceClauseIndex) =
      (PeriodicOneInThreeToThreeDM.occurrencesOf
        (refinedSource source sourcePlacement).erase atom).map
          (fun tagged => tagged.2.1) := by
  simpa [rawOriginalMetadataOccurrences, clauseMetadata,
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata,
    formulaClauseMetadataFrom,
    PeriodicOneInThreePolarityNormalization.taggedLiteralsFrom,
    PeriodicOneInThreeToThreeDM.occurrencesOf,
    PeriodicThreeSATThree.taggedLiterals,
    PositionedPeriodicCNF.erase] using
      formulaMetadataOriginal_sourceIndices
        (rawPositions sourcePlacement routes) atom 0 0
        (refinedSource source sourcePlacement).clauses

private theorem relation_of_mem_zip_of_map_eq
    {First Second Target : Type*}
    (first : List First) (second : List Second)
    (firstMap : First → Target) (secondMap : Second → Target)
    (mapsEq : first.map firstMap = second.map secondMap)
    {pair : First × Second} (pairMember : pair ∈ first.zip second) :
    firstMap pair.1 = secondMap pair.2 := by
  induction first generalizing second with
  | nil => simp at pairMember
  | cons firstHead firstRest induction =>
      cases second with
      | nil => simp at pairMember
      | cons secondHead secondRest =>
          simp only [List.map_cons, List.cons.injEq] at mapsEq
          simp only [List.zip_cons_cons, List.mem_cons] at pairMember
          rcases pairMember with pairEq | pairMember
          · subst pair
            exact mapsEq.1
          · exact induction secondRest mapsEq.2 pairMember

/-- Every enriched raw/source pair belongs to the same retained source
clause. -/
theorem rawOriginalOccurrencePair_sourceClauseIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    {pair : RawOriginalOccurrencePair Variable}
    (pairMember :
      pair ∈ rawOriginalOccurrencePairs
        source sourcePlacement routes atom) :
    pair.1.2.sourceClauseIndex = pair.2.2.1 := by
  apply relation_of_mem_zip_of_map_eq
    (rawOriginalMetadataOccurrences source sourcePlacement routes atom)
    (PeriodicOneInThreeToThreeDM.occurrencesOf
      (refinedSource source sourcePlacement).erase atom)
    (fun tagged => tagged.2.sourceClauseIndex)
    (fun tagged => tagged.2.1)
  · exact rawOriginalMetadataOccurrences_sourceIndices
      source sourcePlacement routes atom
  · exact pairMember

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
