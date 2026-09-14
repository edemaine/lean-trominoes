/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitReduction

/-! # Converting inward orientations to agreeing circuit signals -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

def CircuitKind.InwardRelation (kind : CircuitKind) (inward : Fin 4 → Bool) : Prop :=
  match kind with
  | .blank => True
  | .horizontal => inward 1 ≠ inward 2
  | .vertical => inward 0 ≠ inward 3
  | .northwest => inward 0 ≠ inward 2
  | .southeast => inward 1 ≠ inward 3
  | .northeast => inward 0 ≠ inward 1
  | .southwest => inward 2 ≠ inward 3
  | .copy => inward 2 = inward 0 ∧ inward 0 = inward 1
  | .exactone => [inward 2,inward 0,inward 1].count true = 1

instance (kind : CircuitKind) (inward : Fin 4 → Bool) : Decidable (kind.InwardRelation inward) := by
  unfold CircuitKind.InwardRelation
  split <;> infer_instance

def orientSignal (p : Fin 4) (b : Bool) : Bool := if p.val < 2 then b else !b

def CircuitKind.toSignals (kind : CircuitKind) (inward : Fin 4 → Bool) (p : Fin 4) : Bool :=
  if kind.portEnabled p then orientSignal p (inward p) else false

theorem source_inward_relation (kind : CircuitKind) (inward : Fin 4 → Bool) :
    kind.SourceRelation (kind.toSignals inward) ↔ kind.InwardRelation inward := by
  revert kind inward
  decide +kernel

theorem inward_of_source_relation (kind : CircuitKind) (external : Fin 4 → Bool) :
    kind.SourceRelation external → kind.InwardRelation (fun p => orientSignal p (external p)) := by
  revert kind external
  decide +kernel

theorem orient_signal_seam (p : Fin 4) (a b : Bool) :
    orientSignal p a = orientSignal (gridOpposite p) b ↔ a = !b := by
  revert p a b
  decide +kernel

theorem orient_inverse_seam (p : Fin 4) (a b : Bool) :
    a = b ↔ orientSignal p a = !(orientSignal (gridOpposite p) b) := by
  revert p a b
  decide +kernel

def PortsMatched (kinds : Cell → CircuitKind) : Prop :=
  ∀ c p, (kinds c).portEnabled p = (kinds (gridNeighbor c p)).portEnabled (gridOpposite p)

def InwardGridModel (kinds : Cell → CircuitKind) (inward : Cell → Fin 4 → Bool) : Prop :=
  (∀ c, (kinds c).InwardRelation (inward c)) ∧
    ∀ c p, (kinds c).portEnabled p = true → inward c p = !(inward (gridNeighbor c p) (gridOpposite p))

theorem source_of_inward (kinds : Cell → CircuitKind) (matched : PortsMatched kinds)
    {inward : Cell → Fin 4 → Bool} (model : InwardGridModel kinds inward) : Circuit.SourceHolds kinds := by
  refine ⟨fun c => (kinds c).toSignals (inward c),?_,?_⟩
  · intro c p
    unfold CircuitKind.toSignals
    dsimp only
    rw [← matched c p]
    cases enabled : (kinds c).portEnabled p
    · rfl
    · exact (orient_signal_seam p _ _).mpr (model.2 c p enabled)
  · intro c
    exact (source_inward_relation _ _).mpr (model.1 c)

theorem inward_of_source (kinds : Cell → CircuitKind) (h : Circuit.SourceHolds kinds) :
    ∃ inward, InwardGridModel kinds inward := by
  obtain ⟨external,seams,valid⟩ := h
  refine ⟨fun c p => orientSignal p (external c p),?_,?_⟩
  · intro c
    exact inward_of_source_relation _ _ (valid c)
  · intro c p active
    exact (orient_inverse_seam p _ _).mp (seams c p)

theorem source_iff_inward (kinds : Cell → CircuitKind) (matched : PortsMatched kinds) :
    Circuit.SourceHolds kinds ↔ ∃ inward, InwardGridModel kinds inward :=
  ⟨inward_of_source kinds,fun ⟨_,model⟩ => source_of_inward kinds matched model⟩

end LeanTrominoes.CompletionPattern.LBricks
