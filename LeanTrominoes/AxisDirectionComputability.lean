/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineRibbon
import Mathlib.Computability.Primrec.List

/-! # Canonical primitive-recursive encoding of axis directions -/

noncomputable section

namespace LeanTrominoes
namespace AxisDirection

noncomputable instance : Primcodable AxisDirection :=
  Primcodable.ofEquiv (Fin (Fintype.card AxisDirection))
    (Fintype.equivFin AxisDirection)

end AxisDirection
end LeanTrominoes
