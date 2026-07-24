import LeanTrominoes.PartrecFrontierIndexDecode
import LeanTrominoes.PartrecPeriodicStripDecode

/-!
# Explicit fixed-width context for strip frontier checks

The strip base and edge leaves receive

`[encodedStrip, firstIndex, lastIndex]`.

This module decodes that payload to

`[width, period, motifCode, firstWord, firstPhase, lastWord, lastPhase]`.

The motif remains in its standard encoded-list form, and each assignment
remains one base-nine natural ready for streaming digit steps.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input =
      outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Decode the strip stored in field zero, leaving no other input fields in
the decoder call. -/
def stripFrontierHeaderAtCode : Code :=
  periodicStripHeaderCode.comp (get 0)

@[simp]
theorem stripFrontierHeaderAtCode_eval
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripFrontierHeaderAtCode.eval
        [Encodable.encode periodicStrip, first, last] =
      pure
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif] := by
  calc
    _ = periodicStripHeaderCode.eval
        [Encodable.encode periodicStrip] :=
      comp_eval_pure _ _ _ _ (by simp)
    _ = _ := periodicStripHeaderCode_eval periodicStrip

/-- Select one decoded strip-header field. -/
def stripFrontierHeaderFieldCode (field : Nat) : Code :=
  (get field).comp stripFrontierHeaderAtCode

@[simp]
theorem stripFrontierHeaderFieldCode_eval
    (field : Nat) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    (stripFrontierHeaderFieldCode field).eval
        [Encodable.encode periodicStrip, first, last] =
      pure
        [[periodicStrip.width, periodicStrip.period,
            Encodable.encode periodicStrip.motif][field]?.getD 0] := by
  calc
    _ = (get field).eval
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif] :=
      comp_eval_pure _ _ _ _
        (stripFrontierHeaderAtCode_eval
          periodicStrip first last)
    _ = _ := by simp

/-- Assemble `[period, firstIndex, lastIndex]` for the packed pair decoder. -/
def stripFrontierPairArgumentsCode : Code :=
  prepend (stripFrontierHeaderFieldCode 1) <|
    prepend (get 1) (get 2)

@[simp]
theorem stripFrontierPairArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripFrontierPairArgumentsCode.eval
        [Encodable.encode periodicStrip, first, last] =
      pure [periodicStrip.period, first, last] := by
  have periodEval :=
    stripFrontierHeaderFieldCode_eval
      1 periodicStrip first last
  simp only [stripFrontierPairArgumentsCode,
    Code.prepend_eval_eq]
  rw [periodEval]
  simp

/-- Decode the two index fields while retaining only their packed words and
phases. -/
def stripFrontierPairViewCode : Code :=
  frontierPairViewCode.comp stripFrontierPairArgumentsCode

@[simp]
theorem stripFrontierPairViewCode_eval
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripFrontierPairViewCode.eval
        [Encodable.encode periodicStrip, first, last] =
      pure
        [first / periodicStrip.period,
          first % periodicStrip.period,
          last / periodicStrip.period,
          last % periodicStrip.period] := by
  calc
    _ = frontierPairViewCode.eval
        [periodicStrip.period, first, last] :=
      comp_eval_pure _ _ _ _
        (stripFrontierPairArgumentsCode_eval
          periodicStrip first last)
    _ = _ := frontierPairViewCode_eval
      periodicStrip.period first last

/-- Select one decoded word/phase field. -/
def stripFrontierPairFieldCode (field : Nat) : Code :=
  (get field).comp stripFrontierPairViewCode

@[simp]
theorem stripFrontierPairFieldCode_eval
    (field : Nat) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    (stripFrontierPairFieldCode field).eval
        [Encodable.encode periodicStrip, first, last] =
      pure
        [[first / periodicStrip.period,
            first % periodicStrip.period,
            last / periodicStrip.period,
            last % periodicStrip.period][field]?.getD 0] := by
  calc
    _ = (get field).eval
        [first / periodicStrip.period,
          first % periodicStrip.period,
          last / periodicStrip.period,
          last % periodicStrip.period] :=
      comp_eval_pure _ _ _ _
        (stripFrontierPairViewCode_eval
          periodicStrip first last)
    _ = _ := by simp

/-- Complete fixed-width strip-frontier context. -/
def stripFrontierContextCode : Code :=
  prepend (stripFrontierHeaderFieldCode 0) <|
    prepend (stripFrontierHeaderFieldCode 1) <|
      prepend (stripFrontierHeaderFieldCode 2) <|
        prepend (stripFrontierPairFieldCode 0) <|
          prepend (stripFrontierPairFieldCode 1) <|
            prepend (stripFrontierPairFieldCode 2)
              (stripFrontierPairFieldCode 3)

@[simp]
theorem stripFrontierContextCode_eval
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripFrontierContextCode.eval
        [Encodable.encode periodicStrip, first, last] =
      pure
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif,
          first / periodicStrip.period,
          first % periodicStrip.period,
          last / periodicStrip.period,
          last % periodicStrip.period] := by
  have widthEval :=
    stripFrontierHeaderFieldCode_eval
      0 periodicStrip first last
  have periodEval :=
    stripFrontierHeaderFieldCode_eval
      1 periodicStrip first last
  have motifEval :=
    stripFrontierHeaderFieldCode_eval
      2 periodicStrip first last
  have firstWordEval :=
    stripFrontierPairFieldCode_eval
      0 periodicStrip first last
  have firstPhaseEval :=
    stripFrontierPairFieldCode_eval
      1 periodicStrip first last
  have lastWordEval :=
    stripFrontierPairFieldCode_eval
      2 periodicStrip first last
  have lastPhaseEval :=
    stripFrontierPairFieldCode_eval
      3 periodicStrip first last
  simp only [stripFrontierContextCode,
    Code.prepend_eval_eq]
  rw [widthEval, periodEval, motifEval,
    firstWordEval, firstPhaseEval,
    lastWordEval, lastPhaseEval]
  simp

end Turing.ToPartrec.Code
