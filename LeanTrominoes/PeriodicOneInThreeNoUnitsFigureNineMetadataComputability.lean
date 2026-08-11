import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineIndex
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedComputability
import LeanTrominoes.PeriodicOneInThreePositionedComputability

/-!
# Computability of composed Figure 9 metadata

The proof-oriented composed metadata stores a generated clause together with
several membership certificates.  Route computation only needs its source
clause and three presentation indices.  This module computes that flat
projection with a primitive-recursive left fold and proves exact agreement
with the established metadata enumeration.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

set_option maxHeartbeats 2000000
set_option linter.overlappingInstances false

/-- Proof-free source and local indices parallel to one composed metadata
row. -/
abbrev ClauseIndexData (Variable : Type*) :=
  (PositionedPeriodicClause Variable × Nat) × (Nat × Nat)

/-- Forget the generated clause from one proof-oriented metadata row. -/
def ClauseMetadata.indexData {Variable : Type*}
    (metadata : ClauseMetadata Variable) : ClauseIndexData Variable :=
  ((metadata.sourceClause, metadata.sourceClauseIndex),
    (metadata.figureNineClauseStart, metadata.localClauseIndex))

/-- The unit-elimination blocks over a consecutively indexed list of
Figure 9 clauses are primitive recursive. -/
theorem unitEliminationClausesFrom_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        Nat × List (PositionedPeriodicClause Variable) =>
      unitEliminationClausesFrom input.1 input.2 := by
  have tagged : Primrec fun input :
      Nat × List (PositionedPeriodicClause Variable) =>
      input.2.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp Primrec.snd
  have one : Primrec₂ fun
      (input : Nat × List (PositionedPeriodicClause Variable))
      (taggedClause : PositionedPeriodicClause Variable × Nat) =>
      PeriodicOneInThreeNoUnitsPositioned.clauseGadget
        (input.1 + taggedClause.2) taggedClause.1 := by
    exact PeriodicOneInThreeNoUnitsPositioned.clauseGadget_primrec.comp
      (Primrec.pair
        (Primrec.nat_add.comp
          (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  exact (Primrec.list_flatMap tagged one).of_eq fun input => by
    rw [unitEliminationClausesFrom_eq_localZipIdx]

/-- Proof-free source and local indices for one complete composed block. -/
def clauseIndexDataFor
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    List (ClauseIndexData Variable) :=
  (unitEliminationClausesFrom figureNineClauseStart
    (PeriodicOneInThreePositioned.clauseGadget
      sourceClauseIndex sourceClause)).zipIdx.map fun taggedClause =>
        ((sourceClause, sourceClauseIndex),
          (figureNineClauseStart, taggedClause.2))

private theorem clauseIndexDataFor_eq
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    clauseIndexDataFor sourceClauseIndex figureNineClauseStart
        sourceClause =
      (clauseMetadataFor sourceClauseIndex figureNineClauseStart
        sourceClause).map ClauseMetadata.indexData := by
  simp [clauseIndexDataFor, clauseMetadataFor,
    ClauseMetadata.indexData, List.map_map, Function.comp_def]

/-- Proof-free indices for one complete composed source-clause block are
primitive recursive. -/
theorem clauseIndexDataFor_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        (Nat × Nat) × PositionedPeriodicClause Variable =>
      clauseIndexDataFor input.1.1 input.1.2 input.2 := by
  let Query := (Nat × Nat) × PositionedPeriodicClause Variable
  have figureNineBlock : Primrec fun input : Query =>
      PeriodicOneInThreePositioned.clauseGadget
        input.1.1 input.2 :=
    PeriodicOneInThreePositioned.clauseGadget_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have generated : Primrec fun input : Query =>
      unitEliminationClausesFrom input.1.2
        (PeriodicOneInThreePositioned.clauseGadget
          input.1.1 input.2) :=
    unitEliminationClausesFrom_primrec.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) figureNineBlock)
  have tagged : Primrec fun input : Query =>
      (unitEliminationClausesFrom input.1.2
        (PeriodicOneInThreePositioned.clauseGadget
          input.1.1 input.2)).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp generated
  have one : Primrec₂ fun (input : Query)
      (taggedClause :
        PositionedPeriodicClause
          (OneInThreeNoUnitVariable
            (OneInThreeVariable Variable)) × Nat) =>
      ((input.2, input.1.1), (input.1.2, taggedClause.2)) := by
    exact Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_map tagged one).of_eq fun _ => rfl

private abbrev IndexState (Variable : Type*) :=
  Nat × (Nat × List (ClauseIndexData Variable))

private def formulaClauseIndexDataStep
    {Variable : Type*}
    (state : IndexState Variable)
    (sourceClause : PositionedPeriodicClause Variable) :
    IndexState Variable :=
  (state.1 + 1,
    (state.2.1 +
      (PeriodicOneInThreePositioned.clauseGadget
        state.1 sourceClause).length,
      state.2.2 ++
        clauseIndexDataFor state.1 state.2.1 sourceClause))

private theorem formulaClauseIndexDataStep_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec₂ (@formulaClauseIndexDataStep Variable) := by
  change Primrec fun combined :
      IndexState Variable × PositionedPeriodicClause Variable =>
    formulaClauseIndexDataStep combined.1 combined.2
  have sourceIndex : Primrec fun combined :
      IndexState Variable × PositionedPeriodicClause Variable =>
      combined.1.1 :=
    Primrec.fst.comp Primrec.fst
  have figureNineStart : Primrec fun combined :
      IndexState Variable × PositionedPeriodicClause Variable =>
      combined.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have metadata : Primrec fun combined :
      IndexState Variable × PositionedPeriodicClause Variable =>
      combined.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have block : Primrec fun combined :
      IndexState Variable × PositionedPeriodicClause Variable =>
      PeriodicOneInThreePositioned.clauseGadget
        combined.1.1 combined.2 :=
    PeriodicOneInThreePositioned.clauseGadget_primrec.comp
      (Primrec.pair sourceIndex Primrec.snd)
  have blockMetadata : Primrec fun combined :
      IndexState Variable × PositionedPeriodicClause Variable =>
      clauseIndexDataFor combined.1.1 combined.1.2.1 combined.2 :=
    clauseIndexDataFor_primrec.comp
      (Primrec.pair
        (Primrec.pair sourceIndex figureNineStart)
        Primrec.snd)
  exact (Primrec.pair
    (Primrec.succ.comp sourceIndex)
    (Primrec.pair
      (Primrec.nat_add.comp figureNineStart
        (Primrec.list_length.comp block))
      (Primrec.list_append.comp metadata blockMetadata))).of_eq
        fun _ => rfl

/-- Proof-free left-fold implementation of the flattened source and local
index list. -/
def formulaClauseIndexData
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    List (ClauseIndexData Variable) :=
  (source.clauses.foldl
    formulaClauseIndexDataStep (0, (0, []))).2.2

private theorem formulaClauseIndexDataFold_metadata
    {Variable : Type*}
    (sourceStart figureNineStart : Nat)
    (accumulator : List (ClauseIndexData Variable))
    (clauses : List (PositionedPeriodicClause Variable)) :
    (clauses.foldl formulaClauseIndexDataStep
      (sourceStart, (figureNineStart, accumulator))).2.2 =
      accumulator ++
        (formulaClauseMetadataFrom
          sourceStart figureNineStart clauses).map
            ClauseMetadata.indexData := by
  induction clauses generalizing sourceStart figureNineStart accumulator with
  | nil => simp [formulaClauseMetadataFrom]
  | cons sourceClause rest induction =>
      simp only [List.foldl_cons, formulaClauseIndexDataStep]
      rw [induction]
      simp [formulaClauseMetadataFrom, clauseIndexDataFor_eq,
        List.append_assoc]

/-- The flat executable indices are pointwise projections of the established
proof-oriented metadata list. -/
theorem formulaClauseIndexData_eq
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    formulaClauseIndexData source =
      (formulaClauseMetadata source).map
        ClauseMetadata.indexData := by
  simpa [formulaClauseIndexData, formulaClauseMetadata] using
    formulaClauseIndexDataFold_metadata
      (Variable := Variable) 0 0 [] source.clauses

/-- The flat source and local index list is primitive recursive. -/
theorem formulaClauseIndexData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (formulaClauseIndexData :
      PositionedPeriodicCNF Variable → List (ClauseIndexData Variable)) := by
  have step : Primrec₂ fun
      (_source : PositionedPeriodicCNF Variable)
      (stateClause :
        IndexState Variable × PositionedPeriodicClause Variable) =>
      formulaClauseIndexDataStep stateClause.1 stateClause.2 := by
    change Primrec fun combined :
        PositionedPeriodicCNF Variable ×
          (IndexState Variable × PositionedPeriodicClause Variable) =>
      formulaClauseIndexDataStep combined.2.1 combined.2.2
    exact formulaClauseIndexDataStep_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  have folded : Primrec fun source : PositionedPeriodicCNF Variable =>
      source.clauses.foldl formulaClauseIndexDataStep
        (0, (0, ([] : List (ClauseIndexData Variable)))) :=
    Primrec.list_foldl
      PositionedPeriodicCNF.clauses_primrec
      (Primrec.const (0, (0, [])))
      step
  exact Primrec.snd.comp (Primrec.snd.comp folded)

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
