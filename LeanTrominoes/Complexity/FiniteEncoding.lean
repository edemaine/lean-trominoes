/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import Mathlib.Computability.Encoding

/-! # Encodings with a bundled finite alphabet

Bundle a finite alphabet with Mathlib's `Encoding` for the project's
decision-problem definitions. Encoding functions and laws come from Mathlib;
the forwarding accessors keep the bundled interface convenient.
-/

namespace LeanTrominoes

universe u

/-- A Mathlib encoding together with its finite alphabet. -/
structure FiniteEncoding (α : Type u) where
  Γ : Type
  ΓFin : Fintype Γ
  encoding : Computability.Encoding α Γ

namespace FiniteEncoding

instance {α : Type u} (encoding : FiniteEncoding α) : Fintype encoding.Γ :=
  encoding.ΓFin

/-- Encode through the underlying Mathlib encoding. -/
@[simp]
abbrev encode {α : Type u} (encoding : FiniteEncoding α) : α → List encoding.Γ :=
  encoding.encoding.encode

/-- Decode through the underlying Mathlib encoding. -/
@[simp]
abbrev decode {α : Type u} (encoding : FiniteEncoding α) : List encoding.Γ → Option α :=
  encoding.encoding.decode

@[simp]
theorem decode_encode {α : Type u} (encoding : FiniteEncoding α) (value : α) :
    encoding.decode (encoding.encode value) = some value :=
  encoding.encoding.decode_encode value

theorem encode_injective {α : Type u} (encoding : FiniteEncoding α) :
    Function.Injective encoding.encode :=
  encoding.encoding.encode_injective

end FiniteEncoding
end LeanTrominoes
