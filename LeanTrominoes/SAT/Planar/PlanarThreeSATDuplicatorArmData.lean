/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Tactic.DeriveFintype

/-! # The three routed-variable duplicator arms -/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The three geometric arms at a routed variable site.  The middle route
fanout enters from below in the drawing coordinate system. -/
inductive DuplicatorArm
  | left
  | middle
  | right
  deriving DecidableEq, Repr, Fintype

end PlanarThreeSAT
end LeanTrominoes
