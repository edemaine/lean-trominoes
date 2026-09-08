/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockEndpointCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestHeaderData
import LeanTrominoes.TM2CompositionMachine

/-! # Finite incidence endpoint summaries with the complete RGB triple fan -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction.IncidenceEndpointSummary

open Computability Turing Gadget PeriodicThreeDM.NormalizationCompiler
open PeriodicThreeDM.NormalizationDirectionRequest

abbrev Endpoints := AxisDirection × AxisDirection
abbrev RGBEndpoints := Endpoints × Endpoints × Endpoints

/-- Three starting directions, one incidence color, and its terminal
 direction contain the finite data needed at both ends of that incidence. -/
structure Summary where
  redFirst : AxisDirection
  greenFirst : AxisDirection
  blueFirst : AxisDirection
  color : WireColor
  last : AxisDirection
  deriving DecidableEq, Fintype, Repr

instance : Inhabited Summary :=
  ⟨⟨.invalid, .invalid, .invalid, .red, .invalid⟩⟩

def Summary.first (summary : Summary) : AxisDirection :=
  match summary.color with
  | .red => summary.redFirst
  | .green => summary.greenFirst
  | .blue => summary.blueFirst

def Summary.tripleFan (summary : Summary) : EndpointTripleData :=
  ((VertexSide.ofDirection summary.redFirst, .red),
    (VertexSide.ofDirection summary.greenFirst, .green),
    (VertexSide.ofDirection summary.blueFirst, .blue))

def Summary.tripleEndpointData (summary : Summary) : EndpointHeaderData :=
  { vertexIsTriple := true
    fan := some summary.tripleFan
    endpoint := (VertexSide.ofDirection summary.first, summary.color) }

def Summary.retainedSideColor (summary : Summary) : EndpointSideColor :=
  (VertexSide.ofDirection summary.last.opposite, summary.color)

/-- Complete all three summaries when the blue incidence closes the triple. -/
def tripleSummaries (red green blue : Endpoints) : List Summary :=
  [⟨red.1, green.1, blue.1, .red, red.2⟩,
    ⟨red.1, green.1, blue.1, .green, green.2⟩,
    ⟨red.1, green.1, blue.1, .blue, blue.2⟩]

abbrev State := Option (Endpoints × Option Endpoints)

def transition (state : State) (endpoints : Endpoints) : State × List Summary :=
  match state with
  | none => (some (endpoints, none), [])
  | some (red, none) => (some (red, some endpoints), [])
  | some (red, some green) => (none, tripleSummaries red green endpoints)

def finish (_ : State) : List Summary := []

def output (input : List Endpoints) : List Summary :=
  FiniteStateTransducer.output none transition finish input

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime none transition finish

private theorem scan_triple (red green blue : Endpoints) :
    FiniteStateTransducer.scan transition none [red, green, blue] =
      (none, tripleSummaries red green blue) := by
  simp [FiniteStateTransducer.scan, transition]

theorem output_triple_append (red green blue : Endpoints)
    (remaining : List Endpoints) :
    output ([red, green, blue] ++ remaining) =
      tripleSummaries red green blue ++ output remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_triple]
  simp [finish]

/-- Grouping in threes preserves RGB order and repeats the same complete
fan in each of a triple's three records. -/
theorem output_triples (triples : List RGBEndpoints) :
    output (triples.flatMap (fun triple => [triple.1, triple.2.1, triple.2.2])) =
      triples.flatMap (fun triple => tripleSummaries triple.1 triple.2.1 triple.2.2) := by
  induction triples with
  | nil => rfl
  | cons triple triples induction =>
      simp only [List.flatMap_cons]
      rw [output_triple_append, induction]

/-- The canonical finite record at an incidence tag. -/
def atTag (endpoints : PeriodicThreeDM.IncidenceTag → Endpoints)
    (tag : PeriodicThreeDM.IncidenceTag) : Summary :=
  ⟨(endpoints ⟨tag.tripleIndex, .red⟩).1,
    (endpoints ⟨tag.tripleIndex, .green⟩).1,
    (endpoints ⟨tag.tripleIndex, .blue⟩).1,
    tag.color, (endpoints tag).2⟩

/-- Triple endpoint reconstruction is a finite identity, independent of the
implementation of the endpoint lookup. -/
theorem atTag_tripleEndpointData
    (endpoints : PeriodicThreeDM.IncidenceTag → Endpoints)
    (tag : PeriodicThreeDM.IncidenceTag) :
    (atTag endpoints tag).tripleEndpointData =
      { vertexIsTriple := true
        fan := some
          ((VertexSide.ofDirection (endpoints ⟨tag.tripleIndex, .red⟩).1, .red),
            (VertexSide.ofDirection (endpoints ⟨tag.tripleIndex, .green⟩).1, .green),
            (VertexSide.ofDirection (endpoints ⟨tag.tripleIndex, .blue⟩).1, .blue))
        endpoint := (VertexSide.ofDirection (endpoints tag).1, tag.color) } := by
  cases tag with
  | mk index color => cases color <;> rfl

theorem atTag_retainedSideColor
    (endpoints : PeriodicThreeDM.IncidenceTag → Endpoints)
    (tag : PeriodicThreeDM.IncidenceTag) :
    (atTag endpoints tag).retainedSideColor =
      (VertexSide.ofDirection (endpoints tag).2.opposite, tag.color) := by
  rfl

/-- Triple-major incidence order supplies precisely the consecutive RGB
triples expected by the machine. -/
theorem output_incidenceTags (problem : PeriodicThreeDM)
    (endpoints : PeriodicThreeDM.IncidenceTag → Endpoints) :
    output (problem.incidenceTags.map endpoints) =
      problem.incidenceTags.map (atTag endpoints) := by
  have exact := output_triples (problem.triples.zipIdx.map (fun tagged =>
    (endpoints ⟨tagged.2, .red⟩,
      endpoints ⟨tagged.2, .green⟩,
      endpoints ⟨tagged.2, .blue⟩)))
  simpa [PeriodicThreeDM.incidenceTags, PeriodicThreeDM.tripleIncidenceTags,
    PeriodicThreeDM.incidenceColors, List.map_flatMap, List.flatMap_map,
    tripleSummaries, atTag] using exact

/-- First summarize each delimited word, then attach the RGB fan. -/
def directionOutput
    (input : List (FiniteAlphabetDelimitedBlockJoin.Token AxisDirection)) : List Summary :=
  output (FiniteAlphabetDelimitedBlockEndpoints.output .invalid input)

noncomputable def directionOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id directionOutput := by
  unfold directionOutput
  exact TM2CompositionMachine.computableInPolyTime
    (FiniteAlphabetDelimitedBlockEndpoints.computableInPolyTime AxisDirection.invalid)
    computableInPolyTime

/-- Exact block semantics of the composed finite-state pass. -/
theorem directionOutput_blocks (bodies : List (List AxisDirection)) :
    directionOutput (FiniteAlphabetDelimitedBlockJoin.blocks bodies) =
      output (bodies.map (fun body => (body.headD .invalid, body.getLastD .invalid))) := by
  unfold directionOutput
  rw [FiniteAlphabetDelimitedBlockEndpoints.output_blocks]

end LeanTrominoes.PeriodicCNFStripReduction.IncidenceEndpointSummary

end
