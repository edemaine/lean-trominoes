/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolyominoes

/-! # Corollary 5.6: plane and strip targets, with translations only -/

namespace LeanTrominoes.ThreeTranslationPolyominoes

def planeStatement : Prop := LeanWang.CoREComplete planeProblem

def stripStatement : Prop := Complexity.PSPACEComplete Theorem55StripEncoding.finEncoding stripProblem

def statement : Prop := planeStatement ∧ stripStatement

end LeanTrominoes.ThreeTranslationPolyominoes
