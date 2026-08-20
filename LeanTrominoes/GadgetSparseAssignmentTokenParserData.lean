/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokenMachineCleanupExecution

/-! # Recursive parser data for sparse assignment tokens -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace GadgetSparseAssignmentTokenMachine

abbrev Phase := GadgetSparseAssignmentTokens.Phase

/-- Horizontal scans always have an empty vertical counter. -/
def phaseVertical : Phase → Nat → Nat
  | .horizontal, _ => 0
  | .vertical, vertical => vertical

/-- Canonical tapes at either parser scan phase. -/
def phaseData (phase : Phase) (input : List InputToken)
    (horizontal vertical : Nat) (outputReverse output : List OutputToken) :
    TapeData :=
  activeData input horizontal (phaseVertical phase vertical)
    outputReverse output

/-- Parser configuration associated with a semantic phase. -/
def phaseCfg : Phase → TapeData → TM2.Cfg Alphabet Label State
  | .horizontal => scanHorizontalCfg
  | .vertical => scanVerticalCfg

/-- Semantic prepared suffix associated with a parser phase. -/
def phaseExpand (tromino : Tromino) (phase : Phase)
    (horizontal vertical : Nat) (tokens : List InputToken) :
    List OutputToken :=
  GadgetSparseAssignmentTokens.expandAux tromino phase horizontal
    (phaseVertical phase vertical) tokens

/-- Exact scan-to-reversal allowance.  Coordinate clearing and fixed-mask
expansion are included; final output reversal is accounted for separately. -/
def scanTime (tromino : Tromino) :
    Phase → Nat → Nat → List InputToken → Nat
  | .horizontal, horizontal, _, [] => horizontal + 2 + 1
  | .horizontal, horizontal, _, .coordinateUnit :: tokens =>
      scanTime tromino .horizontal (horizontal + 1) 0 tokens + 1
  | .horizontal, horizontal, _, .fieldEnd :: tokens =>
      scanTime tromino .vertical horizontal 0 tokens + 1
  | .horizontal, horizontal, _, .cellType _ :: tokens =>
      scanTime tromino .horizontal 0 0 tokens + (horizontal + 2 + 1)
  | .vertical, horizontal, vertical, [] =>
      horizontal + vertical + 2 + 1
  | .vertical, horizontal, vertical, .coordinateUnit :: tokens =>
      scanTime tromino .vertical horizontal (vertical + 1) tokens + 1
  | .vertical, horizontal, vertical, .fieldEnd :: tokens =>
      scanTime tromino .horizontal 0 0 tokens +
        (horizontal + vertical + 2 + 1)
  | .vertical, horizontal, vertical, .cellType cellType :: tokens =>
      scanTime tromino .horizontal 0 0 tokens +
        (1 + pixelsTime horizontal vertical (boundedPixels tromino cellType) +
          (horizontal + vertical + 2) + 1)

end GadgetSparseAssignmentTokenMachine
end LeanTrominoes
