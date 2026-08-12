import LeanTrominoes.IndexedSavitchDFSPartrec
import LeanTrominoes.PartrecStripTransition
import LeanTrominoes.StripFrontierIndexedSearchComputability

/-!
# Partial-recursive code for the strip frontier base case

The flat Savitch evaluator delegates its depth-zero test to a fixed code.
This module supplies that code for the sparse strip-frontier graph.  It reads
the encoded periodic strip and the two current state indices from the flat
machine payload, then returns the Boolean tag for equality or a graph edge.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

open LeanTrominoes.Computability
open LeanTrominoes.FiniteState
open Turing ToPartrec

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure (outer inner : Code)
    (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

private def emptyPeriodicStrip : PeriodicStrip :=
  { width := 0, period := 0, motif := [] }

/-- Natural-valued base-case test used by the compiled Savitch evaluator.
Malformed context naturals decode to the default strip; actual executions
always supply `Encodable.encode periodicStrip`. -/
def stripBaseBoolValue (tromino : Tromino)
    (encodedStrip first last : Nat) : Nat :=
  let periodicStrip :=
    (Encodable.decode (α := PeriodicStrip) encodedStrip).getD
      emptyPeriodicStrip
  divideBoolTag
    (decide (first = last) ||
      indexedTransitionRawBool tromino periodicStrip first last)

theorem stripBaseBoolValue_primrec (tromino : Tromino) :
    Primrec fun input : Nat × Nat × Nat =>
      stripBaseBoolValue tromino input.1 input.2.1 input.2.2 := by
  let periodicStrip : Primrec fun input : Nat × Nat × Nat =>
      (Encodable.decode (α := PeriodicStrip) input.1).getD
        emptyPeriodicStrip :=
    Primrec.option_getD.comp
      (Primrec.decode.comp Primrec.fst)
      (Primrec.const emptyPeriodicStrip)
  let first : Primrec fun input : Nat × Nat × Nat => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let last : Primrec fun input : Nat × Nat × Nat => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  let transition : Primrec fun input : Nat × Nat × Nat =>
      indexedTransitionRawBool tromino
        ((Encodable.decode (α := PeriodicStrip) input.1).getD
          emptyPeriodicStrip)
        input.2.1 input.2.2 :=
    (indexedTransitionRawBool_primrec tromino).comp
      (Primrec.pair periodicStrip (Primrec.pair first last))
  unfold stripBaseBoolValue
  exact (Primrec.dom_finite divideBoolTag).comp
    (Primrec.or.comp
      ((Primrec.eq.comp first last).decide)
      transition)

private def stripBaseVectorValue (tromino : Tromino)
    (values : List.Vector Nat 3) : Nat :=
  stripBaseBoolValue tromino values.head values.tail.head
    values.tail.tail.head

private theorem stripBaseVectorValue_primrec (tromino : Tromino) :
    Primrec (stripBaseVectorValue tromino) := by
  unfold stripBaseVectorValue
  exact (stripBaseBoolValue_primrec tromino).comp
    (Primrec.pair Primrec.vector_head
      (Primrec.pair
        (Primrec.vector_head.comp Primrec.vector_tail)
        (Primrec.vector_head.comp
          (Primrec.vector_tail.comp Primrec.vector_tail))))

private theorem exists_stripBaseVectorCode (tromino : Tromino) :
    ∃ code : Code, ∀ values : List.Vector Nat 3,
      code.eval values.1 =
        pure [stripBaseVectorValue tromino values] := by
  have vectorPrimrec :
      Nat.Primrec' (stripBaseVectorValue tromino) :=
    Nat.Primrec'.prim_iff.mpr
      (stripBaseVectorValue_primrec tromino)
  have vectorPartrec :
      Nat.Partrec'
        (fun values : List.Vector Nat 3 =>
          stripBaseVectorValue tromino values) :=
    Nat.Partrec'.prim vectorPrimrec
  simpa using Code.exists_code vectorPartrec

/-- The explicit fixed three-argument code for the strip base-case
predicate. -/
def stripBaseVectorCode (tromino : Tromino) : Code :=
  Code.stripBaseTransitionCode tromino

theorem stripBaseVectorCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    (stripBaseVectorCode tromino).eval
        [Encodable.encode periodicStrip, first, last] =
      pure [stripBaseBoolValue tromino
        (Encodable.encode periodicStrip) first last] := by
  have run := Code.stripBaseTransitionCode_eval
    tromino periodicStrip wellFormed first last
  have decode :
      Encodable.decode (Encodable.encode periodicStrip) =
        some periodicStrip := Encodable.encodek periodicStrip
  simp only [stripBaseBoolValue, decode, Option.getD_some]
  cases result :
      (decide (first = last) ||
        indexedTransitionRawBool
          tromino periodicStrip first last) <;>
    simpa [stripBaseVectorCode,
      FiniteState.divideBoolTag, result] using run

/-- Natural-valued raw edge test, without the reflexive base case used by
Savitch reachability. -/
def stripEdgeBoolValue (tromino : Tromino)
    (encodedStrip first last : Nat) : Nat :=
  let periodicStrip :=
    (Encodable.decode (α := PeriodicStrip) encodedStrip).getD
      emptyPeriodicStrip
  divideBoolTag
    (indexedTransitionRawBool tromino periodicStrip first last)

theorem stripEdgeBoolValue_primrec (tromino : Tromino) :
    Primrec fun input : Nat × Nat × Nat =>
      stripEdgeBoolValue tromino input.1 input.2.1 input.2.2 := by
  let periodicStrip : Primrec fun input : Nat × Nat × Nat =>
      (Encodable.decode (α := PeriodicStrip) input.1).getD
        emptyPeriodicStrip :=
    Primrec.option_getD.comp
      (Primrec.decode.comp Primrec.fst)
      (Primrec.const emptyPeriodicStrip)
  let first : Primrec fun input : Nat × Nat × Nat => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let last : Primrec fun input : Nat × Nat × Nat => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  let transition : Primrec fun input : Nat × Nat × Nat =>
      indexedTransitionRawBool tromino
        ((Encodable.decode (α := PeriodicStrip) input.1).getD
          emptyPeriodicStrip)
        input.2.1 input.2.2 :=
    (indexedTransitionRawBool_primrec tromino).comp
      (Primrec.pair periodicStrip (Primrec.pair first last))
  unfold stripEdgeBoolValue
  exact (Primrec.dom_finite divideBoolTag).comp transition

private def stripEdgeVectorValue (tromino : Tromino)
    (values : List.Vector Nat 3) : Nat :=
  stripEdgeBoolValue tromino values.head values.tail.head
    values.tail.tail.head

private theorem stripEdgeVectorValue_primrec (tromino : Tromino) :
    Primrec (stripEdgeVectorValue tromino) := by
  let arguments : Primrec fun values : List.Vector Nat 3 =>
      (values.head, values.tail.head, values.tail.tail.head) :=
    Primrec.pair Primrec.vector_head
      (Primrec.pair
        (Primrec.vector_head.comp Primrec.vector_tail)
        (Primrec.vector_head.comp
          (Primrec.vector_tail.comp Primrec.vector_tail)))
  exact ((stripEdgeBoolValue_primrec tromino).comp arguments).of_eq
    fun _ => rfl

private theorem exists_stripEdgeVectorCode (tromino : Tromino) :
    ∃ code : Code, ∀ values : List.Vector Nat 3,
      code.eval values.1 =
        pure [stripEdgeVectorValue tromino values] := by
  have vectorPrimrec :
      Nat.Primrec' (stripEdgeVectorValue tromino) :=
    Nat.Primrec'.prim_iff.mpr
      (stripEdgeVectorValue_primrec tromino)
  have vectorPartrec :
      Nat.Partrec'
        (fun values : List.Vector Nat 3 =>
          stripEdgeVectorValue tromino values) :=
    Nat.Partrec'.prim vectorPrimrec
  simpa using Code.exists_code vectorPartrec

/-- Explicit fixed three-argument code for the raw indexed frontier edge
relation. -/
def stripEdgeVectorCode (tromino : Tromino) : Code :=
  Code.stripTransitionCode tromino

theorem stripEdgeVectorCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    (stripEdgeVectorCode tromino).eval
        [Encodable.encode periodicStrip, first, last] =
      pure [divideBoolTag
        (indexedTransitionRawBool tromino periodicStrip first last)] := by
  have run := Code.stripTransitionCode_eval
    tromino periodicStrip wellFormed first last
  cases result :
      indexedTransitionRawBool
        tromino periodicStrip first last <;>
    simpa [stripEdgeVectorCode,
      FiniteState.divideBoolTag, result] using run

private def stripBaseArguments : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 5) <|
      Code.prepend (Code.get 6) Code.nil

/-- The strip base-case program connected to the flat DFS payload layout. -/
noncomputable def stripBaseBoolCode (tromino : Tromino) : Code :=
  (stripBaseVectorCode tromino).comp stripBaseArguments

theorem stripBaseBoolCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount : Nat)
    (state : DivideEvalState) :
    (stripBaseBoolCode tromino).eval
        (divideEvalProgramList (Encodable.encode periodicStrip)
          stateCount state) =
      pure [divideBoolTag
        (decide (state.query.first = state.query.last) ||
          indexedTransitionRawBool tromino periodicStrip
            state.query.first state.query.last)] := by
  have arguments :
      stripBaseArguments.eval
          (divideEvalProgramList (Encodable.encode periodicStrip)
            stateCount state) =
        pure [Encodable.encode periodicStrip,
          state.query.first, state.query.last] := by
    simp [stripBaseArguments, divideEvalProgramList,
      DivideEvalState.toNatList]
  calc
    _ = (stripBaseVectorCode tromino).eval
        [Encodable.encode periodicStrip,
          state.query.first, state.query.last] :=
      comp_eval_pure _ _ _ _ arguments
    _ = _ := by
      have decode :
          Encodable.decode (Encodable.encode periodicStrip) =
            some periodicStrip := Encodable.encodek periodicStrip
      have valueEq :
          stripBaseBoolValue tromino
              (Encodable.encode periodicStrip)
              state.query.first state.query.last =
            divideBoolTag
              (decide (state.query.first = state.query.last) ||
                indexedTransitionRawBool tromino periodicStrip
                  state.query.first state.query.last) := by
        simp only [stripBaseBoolValue, decode, Option.getD_some]
      rw [← valueEq]
      exact stripBaseVectorCode_eval tromino periodicStrip wellFormed
        state.query.first state.query.last

theorem stripStepCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount : Nat)
    (state : DivideEvalState) :
    (DivideEvalPartrec.stepCode (stripBaseBoolCode tromino)).eval
        (divideEvalProgramList (Encodable.encode periodicStrip)
          stateCount state) =
      pure (divideEvalProgramList (Encodable.encode periodicStrip)
        stateCount
        (FiniteState.divideEvalStep stateCount
          (indexedTransitionRawBool tromino periodicStrip) state)) :=
  DivideEvalPartrec.stepCode_eval _ _ _ _ _
    (stripBaseBoolCode_eval
      tromino periodicStrip wellFormed stateCount state)

/-- The compiled countdown evaluator computes exactly the requested number of
strip-specialized DFS transitions. -/
theorem stripFlatIterate_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (stateCount steps : Nat)
    (state : DivideEvalState) :
    (Code.flatIterate
        (DivideEvalPartrec.stepCode (stripBaseBoolCode tromino))).eval
        (steps ::
          divideEvalProgramList (Encodable.encode periodicStrip)
            stateCount state) =
      pure (divideEvalProgramList (Encodable.encode periodicStrip)
        stateCount
        ((FiniteState.divideEvalStep stateCount
          (indexedTransitionRawBool tromino periodicStrip))^[steps]
            state)) :=
  DivideEvalPartrec.flatIterate_stepCode_eval _ _ _ _
    (stripBaseBoolCode_eval
      tromino periodicStrip wellFormed stateCount)
    steps state

end RawWindowState
end PeriodicStrip
end LeanTrominoes
