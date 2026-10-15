/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationCoRE
import Mathlib.Tactic.IntervalCases

/-! # Loop and malformed-input checks for graph orientations -/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Gadget PeriodicOneInThree

def loopGraph : Input :=
  ([false,false],[(⟨0,0,(0,0)⟩,.red),(⟨1,1,(0,0)⟩,.red),(⟨0,1,(0,0)⟩,.red)])

/-- Each loop contributes two edge ends, so these vertices have degree three. -/
example : IsWellFormed loopGraph := by
  constructor
  · simp [loopGraph]
  · intro v hv
    change v < 2 at hv
    interval_cases v <;> simp [colors,endsAt,ends,edgeEnds,loopGraph]

/-- Both loops already contribute one incoming edge. The joining edge
cannot point outward at both ends. -/
example : ¬ HasOrientation loopGraph := by
  rintro ⟨a,h⟩
  have atFirst := h (0,0) 0 (by decide)
  have atSecond := h (0,0) 1 (by decide)
  cases h0 : a 0 (0,0) <;> cases h1 : a 1 (0,0) <;> cases h2 : a 2 (0,0) <;>
    simp [loopGraph,incoming,endsAt,ends,edgeEnds,ClauseHolds,
      clauseValues,ExactlyOne,Cell.add,Cell.sub,h0,h1,h2] at atFirst atSecond

def missingVertices : Input := ([],[(⟨0,0,(0,0)⟩,.red)])

example : ¬ IsWellFormed missingVertices := by simp [IsWellFormed,missingVertices]

example : ¬ Problem missingVertices := by simp [Problem,IsWellFormed,missingVertices]

end LeanTrominoes.TrichromaticGraphOrientation
