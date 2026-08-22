/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebra

/-! # Affine segments and fixed period translations -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- A segment whose two endpoints are affine descriptor-pair points. -/
structure Segment where
  start : Point
  finish : Point
  deriving DecidableEq

/-- Evaluate an affine segment under a natural-valued field assignment. -/
def Segment.eval
    (valuation : Side → Fin 11 → Nat) (segment : Segment) : GridSegment :=
  ⟨segment.start.eval valuation, segment.finish.eval valuation⟩

/-- Evaluate an affine segment on a semantic descriptor pair. -/
def Segment.evalPair
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) : GridSegment :=
  segment.eval (pairFieldValue pair)

/-- Evaluate an affine segment by counting tagged unary units. -/
def Segment.evalTokens
    (segment : Segment)
    (tokens : List RouteDescriptorPairFieldTags.Token) : GridSegment :=
  segment.eval (tokenFieldValue tokens)

/-- Consecutive affine segments of an affine polygonal chain. -/
def segments : List Point → List Segment
  | first :: second :: rest =>
      ⟨first, second⟩ :: segments (second :: rest)
  | _ => []

/-- Translate an affine point by a fixed lattice cell times an affine period. -/
def Point.translateByPeriod
    (affinePoint : Point) (period : Expression) (translate : Cell) : Point :=
  point
    (affinePoint.horizontal.add (period.scale translate.1))
    (affinePoint.vertical.add (period.scale translate.2))

/-- Translate both endpoints of an affine segment by a fixed lattice cell
times an affine period. -/
def Segment.translateByPeriod
    (segment : Segment) (period : Expression) (translate : Cell) : Segment :=
  ⟨segment.start.translateByPeriod period translate,
    segment.finish.translateByPeriod period translate⟩

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
