/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialEmitterSpec

/-!
# Unary padding for the initial input-stack tail

The bounded stack width is source length plus the decider's certified space
polynomial plus the fixed accepting-configuration reserve.  Thus the `none`
tail after the source-dependent input prefix has its own fixed polynomial
length.  This file appends exactly that many unary tail markers to the shared
prepared-data/token workspace in polynomial time.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceInitialTailPadding

open AffineEmitterPipeline
open PolySpaceRequestPadding
open UnaryPolynomialPaddingMachine

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding
abbrev Workspace := AffineEmitterPipeline.Workspace
  (Symbol (encoding := encoding))
abbrev TailWorkspace := Workspace (encoding := encoding) ⊕ Unit

local instance symbolInhabited :
    Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedSpace⟩

def isSource : Symbol (encoding := encoding) → Bool
  | .inl (.inl (.inl (some _))) => true
  | _ => false

def workspaceSource : Workspace (encoding := encoding) → Bool :=
  AffineTemplateEmitterMachine.dataSelected
    (isSource (encoding := encoding))

/-- Polynomial length of the empty suffix after the input symbols. -/
noncomputable def tailPolynomial : Polynomial Nat :=
  decider.space +
    Polynomial.C
      (Complexity.configurationSpace decider.tm
        (PolySpaceReduction.acceptingConfiguration decider))

def tailCount (symbols : List encoding.Γ) : Nat :=
  decider.space.eval symbols.length +
    Complexity.configurationSpace decider.tm
      (PolySpaceReduction.acceptingConfiguration decider)

def tailCoefficients : List Nat :=
  polynomialCoefficients (tailPolynomial decider)

@[simp]
theorem eval_tailCoefficients (length : Nat) :
    evalCoefficients (tailCoefficients decider) length =
      decider.space.eval length +
        Complexity.configurationSpace decider.tm
          (PolySpaceReduction.acceptingConfiguration decider) := by
  simp [tailCoefficients, tailPolynomial, Polynomial.eval_add]

theorem space_eq_source_add_tail (symbols : List encoding.Γ) :
    PolySpaceCompiler.spaceOfSymbols decider symbols =
      symbols.length + tailCount decider symbols := by
  unfold PolySpaceCompiler.spaceOfSymbols tailCount
  omega

@[simp]
theorem tailCount_eq_space_sub (symbols : List encoding.Γ) :
    tailCount decider symbols =
      PolySpaceCompiler.spaceOfSymbols decider symbols - symbols.length := by
  have exactWidth := space_eq_source_add_tail decider symbols
  omega

@[simp]
theorem selectedCount_isSource_preparedSources
    (symbols : List encoding.Γ) :
    selectedCount (isSource (encoding := encoding))
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      symbols.length := by
  rw [PolySpaceUnaryPreparedLayout.preparedSources_eq_layout]
  simp [PolySpaceUnaryPreparedLayout.layout,
    PolySpaceUnaryPreparedLayout.embedSpace,
    PolySpaceUnaryPreparedLayout.embedClock,
    PolySpaceUnaryPreparedLayout.embedFresh,
    isSource, PolySpaceUnaryPreparedLayout.selectedCount_append,
    PolySpaceUnaryPreparedLayout.selectedCount_eq_zero_of]
  exact PolySpaceSourcePreparation.selectedCount_map_of_true
    (isSource (encoding := encoding))
    PolySpaceUnaryPreparedLayout.embedSource (fun _ => rfl) symbols

@[simp]
theorem selectedCount_workspaceSource
    (symbols : List encoding.Γ) (tokens : List UnaryProgramTokens.Token) :
    selectedCount (workspaceSource (encoding := encoding))
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      symbols.length := by
  rw [show selectedCount (workspaceSource (encoding := encoding))
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      selectedCount (isSource (encoding := encoding))
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) by
    exact AffineEmitterPipeline.selectedCount_embed_append_tokens
      (isSource (encoding := encoding))
      (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) tokens]
  exact selectedCount_isSource_preparedSources decider symbols

/-- Preserve the current workspace and append the polynomial number of tail
markers. -/
def paddedWorkspace (workspace : List (Workspace (encoding := encoding))) :
    List (TailWorkspace (encoding := encoding)) :=
  paddedOutput (workspaceSource (encoding := encoding))
    (tailCoefficients decider) workspace

theorem paddedWorkspace_embed_append_tokens
    (symbols : List encoding.Γ) (tokens : List UnaryProgramTokens.Token) :
    paddedWorkspace decider
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))).map Sum.inl ++
        List.replicate (tailCount decider symbols) (Sum.inr ()) := by
  unfold paddedWorkspace paddedOutput
  rw [selectedCount_workspaceSource, eval_tailCoefficients]
  rfl

/-- Tail-marker materialization is polynomial-time on the shared workspace. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (TailWorkspace (encoding := encoding)))
      (Workspace (encoding := encoding))
      (TailWorkspace (encoding := encoding)) id id
      (paddedWorkspace decider) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime
    (workspaceSource (encoding := encoding)) (tailCoefficients decider)

end PolySpaceInitialTailPadding
end PeriodicCNF
end LeanTrominoes
