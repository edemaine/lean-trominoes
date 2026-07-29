import LeanTrominoes.PeriodicOneInThreeToThreeDMDegreeThreeOriginal

/-!
# Ordered original occurrences in the Figure 7 transformation

The Figure 7 exact-one construction preserves original literals in
presentation order, although it distributes them among different generated
clauses and may negate the second and third literals.  This file constructs
an explicit order-preserving pairing between every occurrence of an embedded
output variable and the corresponding tagged source occurrence.

Consequently, the first, second, and third output occurrence slots pair with
the same source slots.  Later route-order proofs can therefore transport a
degree-three source fan pointwise through the transformation.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

abbrev OriginalOccurrencePair (Variable : Type*) :=
  PeriodicOneInThreeToThreeDM.TaggedOccurrence
      (OneInThreeVariable Variable) ×
    PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable

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

def originalOccurrencePairIf
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    (outputLiteral :
      PeriodicLiteral (OneInThreeVariable Variable))
    (outputClauseIndex outputLiteralIndex : Nat)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceClauseIndex sourceLiteralIndex : Nat) :
    List (OriginalOccurrencePair Variable) :=
  if sourceLiteral.atom = atom then
    [((outputLiteral, outputClauseIndex, outputLiteralIndex),
      (sourceLiteral, sourceClauseIndex, sourceLiteralIndex))]
  else
    []

def clauseOriginalOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat) :
    PeriodicClause Variable → List (OriginalOccurrencePair Variable)
  | [] => []
  | [first] =>
      originalOccurrencePairIf atom
        (liftLiteral first) outputStart 0
        first sourceClauseIndex 0
  | [first, second] =>
      originalOccurrencePairIf atom
          (liftLiteral first) outputStart 0
          first sourceClauseIndex 0 ++
        originalOccurrencePairIf atom
          (negate (liftLiteral second)) (outputStart + 1) 0
          second sourceClauseIndex 1
  | first :: second :: third :: _ =>
      originalOccurrencePairIf atom
          (liftLiteral first) outputStart 0
          first sourceClauseIndex 0 ++
        originalOccurrencePairIf atom
          (negate (liftLiteral second)) (outputStart + 1) 0
          second sourceClauseIndex 1 ++
        originalOccurrencePairIf atom
          (negate (liftLiteral third)) (outputStart + 2) 0
          third sourceClauseIndex 2

theorem clauseOriginalOccurrencePairs_fst
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    (clauseOriginalOccurrencePairs
        atom outputStart sourceClauseIndex source).map Prod.fst =
      (taggedLiteralsFrom outputStart
        (clauseClauses sourceClauseIndex source)).filter
          (fun tagged => tagged.1.atom = Sum.inl atom) := by
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseOriginalOccurrencePairs, taggedLiteralsFrom,
      clauseClauses, disjunctionGadget, forcePaddingFalse,
      auxiliary, padding]
  · rcases rest with _ | ⟨second, rest⟩
    · by_cases firstAtom : first.atom = atom
      · simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom, taggedLiteralsFrom,
          clauseClauses, disjunctionGadget, forcePaddingFalse,
          liftLiteral, auxiliary, padding]
      · simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom, taggedLiteralsFrom,
          clauseClauses, disjunctionGadget, forcePaddingFalse,
          liftLiteral, auxiliary, padding]
    · rcases rest with _ | ⟨third, rest⟩
      · by_cases firstAtom : first.atom = atom
        <;> by_cases secondAtom : second.atom = atom
        <;> simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom, secondAtom,
          taggedLiteralsFrom, clauseClauses, disjunctionGadget,
          forcePaddingFalse, liftLiteral, auxiliary, padding,
          negate]
      · by_cases firstAtom : first.atom = atom
        <;> by_cases secondAtom : second.atom = atom
        <;> by_cases thirdAtom : third.atom = atom
        <;> simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom, secondAtom, thirdAtom,
          taggedLiteralsFrom, clauseClauses, disjunctionGadget,
          liftLiteral, auxiliary, negate]

theorem clauseOriginalOccurrencePairs_snd
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable)
    (width : source.length ≤ 3) :
    (clauseOriginalOccurrencePairs
        atom outputStart sourceClauseIndex source).map Prod.snd =
      (source.zipIdx.map fun taggedLiteral =>
        (taggedLiteral.1, sourceClauseIndex, taggedLiteral.2)).filter
          (fun tagged => tagged.1.atom = atom) := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · by_cases firstAtom : first.atom = atom
      <;> simp [clauseOriginalOccurrencePairs,
        originalOccurrencePairIf, firstAtom]
    · rcases rest with _ | ⟨third, rest⟩
      · by_cases firstAtom : first.atom = atom
        <;> by_cases secondAtom : second.atom = atom
        <;> simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom, secondAtom]
      · have restNil : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_cons] at width
          omega
        subst rest
        by_cases firstAtom : first.atom = atom
        <;> by_cases secondAtom : second.atom = atom
        <;> by_cases thirdAtom : third.atom = atom
        <;> simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom, secondAtom, thirdAtom]

def formulaOriginalOccurrencePairsFrom
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) :
    Nat → Nat → List (PeriodicClause Variable) →
      List (OriginalOccurrencePair Variable)
  | _, _, [] => []
  | outputStart, sourceStart, clause :: rest =>
      clauseOriginalOccurrencePairs
          atom outputStart sourceStart clause ++
        formulaOriginalOccurrencePairsFrom atom
          (outputStart +
            (clauseClauses sourceStart clause).length)
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
  | nil =>
      rfl
  | cons clause rest induction =>
      rw [formulaOriginalOccurrencePairsFrom]
      rw [List.map_append,
        clauseOriginalOccurrencePairs_fst]
      rw [formulaClausesFrom_cons,
        taggedLiteralsFrom_append]
      rw [List.filter_append, induction]

theorem formulaOriginalOccurrencePairsFrom_snd
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceStart : Nat)
    (clauses : List (PeriodicClause Variable))
    (width : ∀ clause ∈ clauses, clause.length ≤ 3) :
    (formulaOriginalOccurrencePairsFrom
        atom outputStart sourceStart clauses).map Prod.snd =
      (taggedLiteralsFrom sourceStart clauses).filter
        (fun tagged => tagged.1.atom = atom) := by
  induction clauses generalizing outputStart sourceStart with
  | nil =>
      rfl
  | cons clause rest induction =>
      rw [formulaOriginalOccurrencePairsFrom,
        List.map_append,
        clauseOriginalOccurrencePairs_snd
          atom outputStart sourceStart clause
          (width clause (by simp))]
      rw [show
        taggedLiteralsFrom sourceStart (clause :: rest) =
          (clause.zipIdx.map fun taggedLiteral =>
            (taggedLiteral.1, sourceStart, taggedLiteral.2)) ++
            taggedLiteralsFrom (sourceStart + 1) rest by
          simp [taggedLiteralsFrom]]
      rw [List.filter_append]
      exact congrArg
        ((clause.zipIdx.map fun taggedLiteral =>
          (taggedLiteral.1, sourceStart, taggedLiteral.2)).filter
            (fun tagged => tagged.1.atom = atom) ++ ·)
        (induction
          (outputStart + (clauseClauses sourceStart clause).length)
          (sourceStart + 1)
          (by
            intro current member
            exact width current (by simp [member])))

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
  simpa [formulaOriginalOccurrencePairs,
    taggedLiteralsFrom, PeriodicOneInThreeToThreeDM.occurrencesOf,
    PeriodicThreeSATThree.taggedLiterals, formula,
    formulaClausesFrom] using
    formulaOriginalOccurrencePairsFrom_fst atom 0 0 source.clauses

theorem formulaOriginalOccurrencePairs_snd
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3) (atom : Variable) :
    (formulaOriginalOccurrencePairs source atom).map Prod.snd =
      PeriodicOneInThreeToThreeDM.occurrencesOf source atom := by
  simpa [formulaOriginalOccurrencePairs,
    taggedLiteralsFrom, PeriodicOneInThreeToThreeDM.occurrencesOf,
    PeriodicThreeSATThree.taggedLiterals] using
    formulaOriginalOccurrencePairsFrom_snd
      atom 0 0 source.clauses
      (by
        intro clause member
        exact width clause member)

/-- Every ordered occurrence of an embedded original variable is paired
with the source occurrence in the same occurrence slot. -/
theorem exists_source_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (output :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (OneInThreeVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source) (Sum.inl atom) slot =
        some output) :
    ∃ sourceOccurrence,
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source atom slot = some sourceOccurrence ∧
        (output, sourceOccurrence) ∈
          formulaOriginalOccurrencePairs source atom := by
  let pairs := formulaOriginalOccurrencePairs source atom
  have outputLookup :
      (pairs.map Prod.fst)[slot.index]? = some output := by
    rw [show
      pairs.map Prod.fst =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (formula source) (Sum.inl atom) by
        simpa [pairs] using
          formulaOriginalOccurrencePairs_fst source atom]
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
    rw [← formulaOriginalOccurrencePairs_snd source width atom,
      List.getElem?_map, pairLookup]
    rfl
  refine ⟨pair.2, sourceLookup, ?_⟩
  rw [← pairFst]
  exact List.mem_iff_getElem?.mpr ⟨slot.index, pairLookup⟩

end PeriodicOneInThree
end LeanTrominoes
