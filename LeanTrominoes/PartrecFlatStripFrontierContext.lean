import LeanTrominoes.PartrecFlatSavitchContext
import LeanTrominoes.PartrecFrontierIndexDecode
import LeanTrominoes.PeriodicStripFlatEncoding

/-!
# Flat strip context for Savitch frontier leaves

The suffix-preserving Savitch evaluator carries the strip as native fields

`[width, period, motif length, x₀, y₀, x₁, y₁, ...]`.

At a depth-zero leaf, this module recovers that suffix and combines it with
the query endpoints stored in the fixed DFS header.  The resulting layout is

`[width, period, motif length, first word, first phase,
  last word, last phase, coordinates...]`.

In particular, no recursively paired code for the motif is constructed.
-/

namespace LeanTrominoes.FiniteState

open Turing ToPartrec

namespace FlatStripEdgePartrec

open Code

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Select one field from the flat strip suffix following the current DFS
stack. -/
def stripFieldCode (fieldIndex : Nat) : Code :=
  (get fieldIndex).comp DivideEvalPartrec.flatContextCode

@[simp]
theorem stripFieldCode_eval
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    (stripFieldCode fieldIndex).eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        [(PeriodicStripFlatEncoding.stripFields periodicStrip)[fieldIndex]?.getD
          0] := by
  calc
    _ = (get fieldIndex).eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) :=
      comp_eval_pure _ _ _ _
        (DivideEvalPartrec.flatContextCode_eval context stateCount state
          (PeriodicStripFlatEncoding.stripFields periodicStrip))
    _ = _ := by simp

/-- Assemble `[period, firstIndex, lastIndex]` for the common frontier-pair
decoder.  The two query endpoints are fixed fields five and six even though
the continuation stack has variable length. -/
def pairArgumentsCode : Code :=
  prepend (stripFieldCode 1) <|
    prepend (get 5) (get 6)

@[simp]
theorem pairArgumentsCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    pairArgumentsCode.eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        [periodicStrip.period, state.query.first, state.query.last] := by
  have periodEval :=
    stripFieldCode_eval 1 context stateCount state periodicStrip
  rcases state with ⟨⟨depth, first, last⟩, stack, answer⟩
  simp only [pairArgumentsCode, prepend_eval_eq]
  rw [periodEval]
  simp [
    divideEvalProgramList, DivideEvalState.toNatList,
    PeriodicStripFlatEncoding.stripFields]

/-- Decode both query endpoints to their base-nine assignment words and
horizontal phases. -/
def pairViewCode : Code :=
  frontierPairViewCode.comp pairArgumentsCode

@[simp]
theorem pairViewCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    pairViewCode.eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        [state.query.first / periodicStrip.period,
          state.query.first % periodicStrip.period,
          state.query.last / periodicStrip.period,
          state.query.last % periodicStrip.period] := by
  calc
    _ = frontierPairViewCode.eval
        [periodicStrip.period, state.query.first, state.query.last] :=
      comp_eval_pure _ _ _ _
        (pairArgumentsCode_eval context stateCount state periodicStrip)
    _ = _ := frontierPairViewCode_eval _ _ _

/-- Select one decoded word/phase field. -/
def pairFieldCode (fieldIndex : Nat) : Code :=
  (get fieldIndex).comp pairViewCode

@[simp]
theorem pairFieldCode_eval
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    (pairFieldCode fieldIndex).eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        [[state.query.first / periodicStrip.period,
            state.query.first % periodicStrip.period,
            state.query.last / periodicStrip.period,
            state.query.last % periodicStrip.period][fieldIndex]?.getD 0] := by
  calc
    _ = (get fieldIndex).eval
        [state.query.first / periodicStrip.period,
          state.query.first % periodicStrip.period,
          state.query.last / periodicStrip.period,
          state.query.last % periodicStrip.period] :=
      comp_eval_pure _ _ _ _
        (pairViewCode_eval context stateCount state periodicStrip)
    _ = _ := by simp

/-- Recover the native coordinate fields, dropping only the three flat strip
header fields. -/
def coordinatesCode : Code :=
  (drop 3).comp DivideEvalPartrec.flatContextCode

@[simp]
theorem coordinatesCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    coordinatesCode.eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        (periodicStrip.motif.flatMap
          PeriodicStripFlatEncoding.cellFields) := by
  calc
    _ = (drop 3).eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) :=
      comp_eval_pure _ _ _ _
        (DivideEvalPartrec.flatContextCode_eval context stateCount state
          (PeriodicStripFlatEncoding.stripFields periodicStrip))
    _ = _ := by simp [PeriodicStripFlatEncoding.stripFields]

/-- Complete flat context consumed by the strip transition leaf. -/
def contextCode : Code :=
  prepend (stripFieldCode 0) <|
    prepend (stripFieldCode 1) <|
      prepend (stripFieldCode 2) <|
        prepend (pairFieldCode 0) <|
          prepend (pairFieldCode 1) <|
            prepend (pairFieldCode 2) <|
              prepend (pairFieldCode 3) coordinatesCode

@[simp]
theorem contextCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    contextCode.eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        ([periodicStrip.width, periodicStrip.period,
            periodicStrip.motif.length,
            state.query.first / periodicStrip.period,
            state.query.first % periodicStrip.period,
            state.query.last / periodicStrip.period,
            state.query.last % periodicStrip.period] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) := by
  simp only [contextCode, prepend_eval_eq]
  rw [stripFieldCode_eval 0, stripFieldCode_eval 1,
    stripFieldCode_eval 2, pairFieldCode_eval 0,
    pairFieldCode_eval 1, pairFieldCode_eval 2,
    pairFieldCode_eval 3, coordinatesCode_eval]
  simp [PeriodicStripFlatEncoding.stripFields]

end FlatStripEdgePartrec
end LeanTrominoes.FiniteState
