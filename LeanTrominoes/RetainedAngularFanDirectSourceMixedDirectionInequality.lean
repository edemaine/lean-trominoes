/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceSegmentClassification
import LeanTrominoes.RetainedTerminalDirectionAlignment

/-!
# Direction inequality for oblique direct source choices

The finite direct atlas can contain both axis-aligned and oblique source
segments.  In the oblique branch, exact segment classification separates
the choice's terminal direction from that of every classified axis-aligned
segment.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- An oblique selected direct segment and a classified axis-aligned segment
cannot have the same retained terminal direction. -/
theorem RetainedDirectSourceRouteChoice.direction_ne_of_otherSegment_aligned
    (choice : RetainedDirectSourceRouteChoice)
    {otherStart otherFinish : Cell}
    {otherDirection : RetainedTerminalDirection}
    {otherLength : Nat}
    (otherClassified :
      retainedTerminalDirectionClassify
          (Cell.sub otherStart otherFinish) =
        some (otherDirection, otherLength))
    (otherAligned :
      (GridSegment.mk otherStart otherFinish).IsAxisAligned)
    (directNotAligned : ¬choice.sourceSegment.IsAxisAligned) :
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 ≠ otherDirection := by
  exact
    (retainedTerminalDirections_ne_of_segment_alignment_ne
      otherClassified choice.sourceSegment_terminalClassify
      otherAligned directNotAligned).symm

/-- Record-valued interface to
`RetainedDirectSourceRouteChoice.direction_ne_of_otherSegment_aligned`.
Keeping the classified direction and length bundled prevents downstream
applications from normalizing a large route expression through both
projections independently. -/
theorem RetainedDirectSourceRouteChoice.direction_ne_of_otherTerminal_aligned
    (choice : RetainedDirectSourceRouteChoice)
    {otherStart otherFinish : Cell}
    {otherTerminal : RetainedTerminalData}
    (otherClassified :
      retainedTerminalDirectionClassify
          (Cell.sub otherStart otherFinish) =
        some otherTerminal)
    (otherAligned :
      (GridSegment.mk otherStart otherFinish).IsAxisAligned)
    (directNotAligned : ¬choice.sourceSegment.IsAxisAligned) :
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 ≠ otherTerminal.1 := by
  exact
    choice.direction_ne_of_otherSegment_aligned
      (otherDirection := otherTerminal.1)
      (otherLength := otherTerminal.2)
      otherClassified otherAligned directNotAligned

end PeriodicEightOccurrenceSplit
end LeanTrominoes
