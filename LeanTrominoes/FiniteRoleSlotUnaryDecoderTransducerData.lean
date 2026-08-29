/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderData
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Streaming data for the generic unary role/slot decoder -/

noncomputable section

namespace LeanTrominoes.FiniteRoleSlotUnaryDecoder

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

def transition {Role : Type} [Fintype Role] [Nonempty Role] :
    Control Role → Symbol → Control Role × List (Pair Role)
  | control, .unit => (increment control, [])
  | control, .delimiter => (zero, [decode control])

def finish {Role : Type} [Fintype Role] [Nonempty Role]
    (_ : Control Role) : List (Pair Role) := []

end LeanTrominoes.FiniteRoleSlotUnaryDecoder

end
