/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripIncidenceEndpointSummaryCompiler
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerData

/-! # Finite-state assembly of contracted route headers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction.IncidenceHeaderAssembler

open Computability Turing PeriodicThreeDM
open PeriodicThreeDM.NormalizationCompiler PeriodicThreeDM.NormalizationDirectionRequest

abbrev Summary := IncidenceEndpointSummary.Summary
abbrev Role := ContractedDirectionAssembler.Role

def throughHeader (first second : Summary) : Header :=
  Header.ofEndpointData first.tripleEndpointData second.tripleEndpointData

def retainedFan (first second third : Summary) : EndpointTripleData :=
  (first.retainedSideColor, second.retainedSideColor, third.retainedSideColor)

def retainedHeader (fan : EndpointTripleData) (incidence : Summary) : Header :=
  Header.ofEndpointData incidence.tripleEndpointData
    { vertexIsTriple := false, fan := some fan, endpoint := incidence.retainedSideColor }

def retainedHeaders (first second third : Summary) : List Header :=
  let fan := retainedFan first second third
  [retainedHeader fan first, retainedHeader fan second, retainedHeader fan third]

/-- Only unfinished groups are retained in finite control. -/
inductive State
  | empty
  | through (first : Summary)
  | retainedOne (first : Summary)
  | retainedTwo (first second : Summary)
  deriving DecidableEq, Fintype

instance : Inhabited State := ⟨.empty⟩

def transition (state : State) (input : Role × Summary) : State × List Header :=
  match input.1 with
  | .throughFirst => (.through input.2, [])
  | .throughSecond =>
      match state with
      | .through first => (.empty, [throughHeader first input.2])
      | _ => (.empty, [])
  | .retained =>
      match state with
      | .retainedOne first => (.retainedTwo first input.2, [])
      | .retainedTwo first second => (.empty, retainedHeaders first second input.2)
      | _ => (.retainedOne input.2, [])

def finish (_ : State) : List Header := []

def output (input : List (Role × Summary)) : List Header :=
  FiniteStateTransducer.output .empty transition finish input

/-- The degree-two and degree-three endpoint assembler is a fixed finite
machine, independent of source size and route lengths. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  letI : Inhabited Header := ⟨throughHeader default default⟩
  exact FiniteStateTransducer.computableInPolyTime .empty transition finish

private theorem scan_through (first second : Summary) :
    FiniteStateTransducer.scan transition .empty
      [(.throughFirst, first), (.throughSecond, second)] =
      (.empty, [throughHeader first second]) := by
  simp [FiniteStateTransducer.scan, transition]

private theorem scan_retained (first second third : Summary) :
    FiniteStateTransducer.scan transition .empty
      [(.retained, first), (.retained, second), (.retained, third)] =
      (.empty, retainedHeaders first second third) := by
  simp [FiniteStateTransducer.scan, transition]

theorem output_through_append (first second : Summary) (remaining : List (Role × Summary)) :
    output ([ (.throughFirst, first), (.throughSecond, second)] ++ remaining) =
      throughHeader first second :: output remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_through]
  simp [finish]

theorem output_retained_append (first second third : Summary)
    (remaining : List (Role × Summary)) :
    output ([ (.retained, first), (.retained, second), (.retained, third)] ++ remaining) =
      retainedHeaders first second third ++ output remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_retained]
  simp [finish]

/-- Cons forms expose the finite input prefix directly to rewriting. -/
theorem output_through_cons (first second : Summary) (remaining : List (Role × Summary)) :
    output ((.throughFirst, first) :: (.throughSecond, second) :: remaining) =
      throughHeader first second :: output remaining := by
  exact output_through_append first second remaining

theorem output_retained_cons (first second third : Summary) (remaining : List (Role × Summary)) :
    output ((.retained, first) :: (.retained, second) :: (.retained, third) :: remaining) =
      retainedHeaders first second third ++ output remaining := by
  exact output_retained_append first second third remaining

end LeanTrominoes.PeriodicCNFStripReduction.IncidenceHeaderAssembler

end
