/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computability
import LeanTrominoes.PlanarThreeSATDuplicatorArm

/-! # Primitive-recursive retained local route datatypes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PlanarThreeSAT

namespace DuplicatorArmVariable

def equivBool : DuplicatorArmVariable ≃ Bool where
  toFun
    | .port => false
    | .center => true
  invFun
    | false => .port
    | true => .center
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

noncomputable instance : Primcodable DuplicatorArmVariable :=
  Primcodable.ofEquiv Bool equivBool

theorem equivBool_primrec : Primrec equivBool :=
  Primrec.of_equiv

theorem equivBool_symm_primrec : Primrec equivBool.symm :=
  Primrec.of_equiv_symm

end DuplicatorArmVariable

end PlanarThreeSAT
end LeanTrominoes
