import LeanTrominoes.IndexedSavitchDFSPartrec
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

/-- A fixed three-argument code for the strip base-case predicate. -/
noncomputable def stripBaseVectorCode (tromino : Tromino) : Code :=
  Classical.choose (exists_stripBaseVectorCode tromino)

theorem stripBaseVectorCode_eval (tromino : Tromino)
    (encodedStrip first last : Nat) :
    (stripBaseVectorCode tromino).eval [encodedStrip, first, last] =
      pure [stripBaseBoolValue tromino encodedStrip first last] := by
  let values : List.Vector Nat 3 :=
    ⟨[encodedStrip, first, last], rfl⟩
  have correctness :=
    Classical.choose_spec (exists_stripBaseVectorCode tromino) values
  change
    (stripBaseVectorCode tromino).eval [encodedStrip, first, last] =
      pure [stripBaseBoolValue tromino encodedStrip first last] at correctness
  exact correctness

private def stripBaseArguments : Code :=
  Code.prepend (Code.get 0) <|
    Code.prepend (Code.get 5) <|
      Code.prepend (Code.get 6) Code.nil

/-- The strip base-case program connected to the flat DFS payload layout. -/
noncomputable def stripBaseBoolCode (tromino : Tromino) : Code :=
  (stripBaseVectorCode tromino).comp stripBaseArguments

theorem stripBaseBoolCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (stateCount : Nat)
    (state : DivideEvalState) :
    (stripBaseBoolCode tromino).eval
        (divideEvalProgramList (Encodable.encode periodicStrip)
          stateCount state) =
      pure [divideBoolTag
        (decide (state.query.first = state.query.last) ||
          indexedTransitionRawBool tromino periodicStrip
            state.query.first state.query.last)] := by
  simp [stripBaseBoolCode, stripBaseArguments, divideEvalProgramList,
    DivideEvalState.toNatList, stripBaseVectorCode_eval,
    stripBaseBoolValue]

theorem stripStepCode_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (stateCount : Nat)
    (state : DivideEvalState) :
    (DivideEvalPartrec.stepCode (stripBaseBoolCode tromino)).eval
        (divideEvalProgramList (Encodable.encode periodicStrip)
          stateCount state) =
      pure (divideEvalProgramList (Encodable.encode periodicStrip)
        stateCount
        (FiniteState.divideEvalStep stateCount
          (indexedTransitionRawBool tromino periodicStrip) state)) :=
  DivideEvalPartrec.stepCode_eval _ _ _ _ _
    (stripBaseBoolCode_eval tromino periodicStrip stateCount state)

/-- The compiled countdown evaluator computes exactly the requested number of
strip-specialized DFS transitions. -/
theorem stripFlatIterate_eval (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (stateCount steps : Nat)
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
    (stripBaseBoolCode_eval tromino periodicStrip stateCount)
    steps state

end RawWindowState
end PeriodicStrip
end LeanTrominoes
