import LeanTrominoes.PeriodicOneInThreePolarityNormalizationOccurrences
import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences

/-!
# Ordered original occurrences under polarity normalization

Polarity normalization may move an incompatible original literal from its
source clause into a following binary complement clause.  Nevertheless, each
source clause block contributes exactly the same number of occurrences of any
fixed original atom as the source clause itself.  Pairing those two finite
lists block by block therefore preserves the global first, second, and third
occurrence slots.

The pairing in this file is deliberately logical: when a source clause repeats
an atom, it pairs the two block lists by position without claiming which source
literal generated which output route.  The geometric route-order theorem adds
the usual per-clause atom-distinctness hypothesis to recover that provenance.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalization

abbrev OriginalOccurrencePair (Variable : Type*) :=
  PeriodicOneInThreeToThreeDM.TaggedOccurrence
      (PolarityNormalizedVariable Variable) ×
    PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable

/-- Flatten clauses into the tagged-literal order used by occurrence-slot
lookups, beginning the clause indices at `start`. -/
def taggedLiteralsFrom {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    List (PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable) :=
  clauses.zipIdx start |>.flatMap fun taggedClause =>
    taggedClause.1.zipIdx.map fun taggedLiteral =>
      (taggedLiteral.1, taggedClause.2, taggedLiteral.2)

theorem taggedLiteralsFrom_append {Variable : Type*}
    (start : Nat) (first second : List (PeriodicClause Variable)) :
    taggedLiteralsFrom start (first ++ second) =
      taggedLiteralsFrom start first ++
        taggedLiteralsFrom (start + first.length) second := by
  simp [taggedLiteralsFrom, List.zipIdx_append]

/-- The original-atom occurrences appearing in one generated clause block. -/
def outputBlockOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    List
      (PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (PolarityNormalizedVariable Variable)) :=
  (taggedLiteralsFrom outputStart
      (clauseClauses sourceClauseIndex source)).filter
    fun tagged => tagged.1.atom = Sum.inl atom

/-- The occurrences of one atom in the corresponding source clause. -/
def sourceClauseOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    List (PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable) :=
  (source.zipIdx.map fun taggedLiteral =>
      (taggedLiteral.1, sourceClauseIndex, taggedLiteral.2)).filter
    fun tagged => tagged.1.atom = atom

private theorem taggedClause_filter_length_eq_count
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicClause Variable)
    (clauseIndex literalStart : Nat) (atom : Variable) :
    (((source.zipIdx literalStart).map fun taggedLiteral =>
        (taggedLiteral.1, clauseIndex, taggedLiteral.2)).filter
          fun tagged => tagged.1.atom = atom).length =
      (source.map PeriodicLiteral.atom).count atom := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases same : literal.atom = atom
      · simp [same, induction (literalStart + 1)]
      · simp [same, induction (literalStart + 1)]

private theorem filter_taggedLiteralsFrom_length_eq_count
    {Variable : Type*} [DecidableEq Variable]
    (clauses : List (PeriodicClause Variable))
    (start : Nat) (atom : Variable) :
    ((taggedLiteralsFrom start clauses).filter
        fun tagged => tagged.1.atom = atom).length =
      @List.count Variable instBEqOfDecidableEq atom
        (PeriodicCNF.variableOccurrences (PeriodicCNF.mk clauses)) := by
  induction clauses generalizing start with
  | nil => simp [taggedLiteralsFrom, PeriodicCNF.variableOccurrences]
  | cons clause rest induction =>
      rw [show
        taggedLiteralsFrom start (clause :: rest) =
          (clause.zipIdx.map fun taggedLiteral =>
            (taggedLiteral.1, start, taggedLiteral.2)) ++
            taggedLiteralsFrom (start + 1) rest by
          simp [taggedLiteralsFrom]]
      rw [List.filter_append, List.length_append,
        induction (start + 1),
        taggedClause_filter_length_eq_count clause start 0 atom]
      simp [PeriodicCNF.variableOccurrences]

private theorem sourceClauseOccurrences_length
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    (sourceClauseOccurrences atom sourceClauseIndex source).length =
      (source.map PeriodicLiteral.atom).count atom := by
  exact taggedClause_filter_length_eq_count
    source sourceClauseIndex 0 atom

/-- A generated source-clause block and its source clause contribute equally
many occurrences of every embedded original atom. -/
theorem outputBlockOccurrences_length
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    (outputBlockOccurrences atom outputStart sourceClauseIndex source).length =
      (sourceClauseOccurrences atom sourceClauseIndex source).length := by
  rw [sourceClauseOccurrences_length]
  unfold outputBlockOccurrences
  rw [filter_taggedLiteralsFrom_length_eq_count]
  have countInstanceEq :
      @List.count (PolarityNormalizedVariable Variable)
          instBEqOfDecidableEq (Sum.inl atom)
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (clauseClauses sourceClauseIndex source))) =
        @List.count (PolarityNormalizedVariable Variable)
          Sum.instBEq (Sum.inl atom)
          (PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (clauseClauses sourceClauseIndex source))) := by
    unfold List.count
    congr 1
    funext head
    by_cases same : head = Sum.inl atom <;> simp [same]
  rw [countInstanceEq]
  simpa only [clauseClausesFrom_zero] using
    clauseClausesFrom_count_original sourceClauseIndex 0 source atom

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

/-- Pair the generated and source occurrences contributed by one source
clause, in their respective within-block orders. -/
def clauseOriginalOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    List (OriginalOccurrencePair Variable) :=
  (outputBlockOccurrences atom outputStart sourceClauseIndex source).zip
    (sourceClauseOccurrences atom sourceClauseIndex source)

theorem clauseOriginalOccurrencePairs_fst
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    (clauseOriginalOccurrencePairs
        atom outputStart sourceClauseIndex source).map Prod.fst =
      outputBlockOccurrences atom outputStart sourceClauseIndex source := by
  apply map_fst_zip_of_length_eq
  exact outputBlockOccurrences_length atom outputStart sourceClauseIndex source

theorem clauseOriginalOccurrencePairs_snd
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    (clauseOriginalOccurrencePairs
        atom outputStart sourceClauseIndex source).map Prod.snd =
      sourceClauseOccurrences atom sourceClauseIndex source := by
  apply map_snd_zip_of_length_eq
  exact outputBlockOccurrences_length atom outputStart sourceClauseIndex source

/-- Pair all generated and source occurrences, advancing the generated clause
index by the size of each variable-length replacement block. -/
def formulaOriginalOccurrencePairsFrom
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) :
    Nat → Nat → List (PeriodicClause Variable) →
      List (OriginalOccurrencePair Variable)
  | _, _, [] => []
  | outputStart, sourceStart, clause :: rest =>
      clauseOriginalOccurrencePairs atom outputStart sourceStart clause ++
        formulaOriginalOccurrencePairsFrom atom
          (outputStart + (clauseClauses sourceStart clause).length)
          (sourceStart + 1) rest

theorem formulaOriginalOccurrencePairsFrom_fst
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceStart : Nat)
    (clauses : List (PeriodicClause Variable)) :
    (formulaOriginalOccurrencePairsFrom
        atom outputStart sourceStart clauses).map Prod.fst =
      (taggedLiteralsFrom outputStart
        (formulaClausesFrom sourceStart clauses)).filter
          (fun tagged => tagged.1.atom = Sum.inl atom) := by
  induction clauses generalizing outputStart sourceStart with
  | nil => rfl
  | cons clause rest induction =>
      rw [formulaOriginalOccurrencePairsFrom, List.map_append,
        clauseOriginalOccurrencePairs_fst]
      rw [formulaClausesFrom_cons,
        taggedLiteralsFrom_append, List.filter_append]
      exact congrArg₂ (· ++ ·) rfl
        (induction
          (outputStart + (clauseClauses sourceStart clause).length)
          (sourceStart + 1))

theorem formulaOriginalOccurrencePairsFrom_snd
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceStart : Nat)
    (clauses : List (PeriodicClause Variable)) :
    (formulaOriginalOccurrencePairsFrom
        atom outputStart sourceStart clauses).map Prod.snd =
      (taggedLiteralsFrom sourceStart clauses).filter
        (fun tagged => tagged.1.atom = atom) := by
  induction clauses generalizing outputStart sourceStart with
  | nil => rfl
  | cons clause rest induction =>
      rw [formulaOriginalOccurrencePairsFrom, List.map_append,
        clauseOriginalOccurrencePairs_snd]
      rw [show
        taggedLiteralsFrom sourceStart (clause :: rest) =
          (clause.zipIdx.map fun taggedLiteral =>
            (taggedLiteral.1, sourceStart, taggedLiteral.2)) ++
            taggedLiteralsFrom (sourceStart + 1) rest by
          simp [taggedLiteralsFrom]]
      rw [List.filter_append]
      exact congrArg₂ (· ++ ·) rfl
        (induction
          (outputStart + (clauseClauses sourceStart clause).length)
          (sourceStart + 1))

def formulaOriginalOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    List (OriginalOccurrencePair Variable) :=
  formulaOriginalOccurrencePairsFrom atom 0 0 source.clauses

theorem formulaOriginalOccurrencePairs_fst
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (formulaOriginalOccurrencePairs source atom).map Prod.fst =
      PeriodicOneInThreeToThreeDM.occurrencesOf
        (formula source) (Sum.inl atom) := by
  simpa [formulaOriginalOccurrencePairs, taggedLiteralsFrom,
    PeriodicOneInThreeToThreeDM.occurrencesOf,
    PeriodicThreeSATThree.taggedLiterals, formula,
    formulaClausesFrom] using
      formulaOriginalOccurrencePairsFrom_fst atom 0 0 source.clauses

theorem formulaOriginalOccurrencePairs_snd
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (formulaOriginalOccurrencePairs source atom).map Prod.snd =
      PeriodicOneInThreeToThreeDM.occurrencesOf source atom := by
  simpa [formulaOriginalOccurrencePairs, taggedLiteralsFrom,
    PeriodicOneInThreeToThreeDM.occurrencesOf,
    PeriodicThreeSATThree.taggedLiterals] using
      formulaOriginalOccurrencePairsFrom_snd atom 0 0 source.clauses

/-- Every occurrence of an embedded original variable is paired with a source
occurrence in the identical global occurrence slot. -/
theorem exists_source_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (output :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (PolarityNormalizedVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source) (Sum.inl atom) slot = some output) :
    ∃ sourceOccurrence,
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source atom slot = some sourceOccurrence ∧
        (output, sourceOccurrence) ∈
          formulaOriginalOccurrencePairs source atom := by
  let pairs := formulaOriginalOccurrencePairs source atom
  have outputLookup :
      (pairs.map Prod.fst)[slot.index]? = some output := by
    rw [show pairs.map Prod.fst =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (formula source) (Sum.inl atom) by
      simpa [pairs] using formulaOriginalOccurrencePairs_fst source atom]
    exact lookup
  rw [List.getElem?_map, Option.map_eq_some_iff] at outputLookup
  rcases outputLookup with
    ⟨pair, pairLookup, pairFst⟩
  have sourceLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source atom slot = some pair.2 := by
    change
      (PeriodicOneInThreeToThreeDM.occurrencesOf
        source atom)[slot.index]? = some pair.2
    rw [← formulaOriginalOccurrencePairs_snd source atom,
      List.getElem?_map, pairLookup]
    rfl
  refine ⟨pair.2, sourceLookup, ?_⟩
  rw [← pairFst]
  exact List.mem_iff_getElem?.mpr ⟨slot.index, pairLookup⟩

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
