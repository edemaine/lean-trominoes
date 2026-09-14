/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionOrientationSignals
import LeanTrominoes.OrthogonalDrawing

/-! # The normalized orientation source and completion circuits -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks
open Gadget Gadget.PeriodicOrthogonalDrawing

set_option maxHeartbeats 2000000

def kindOf : OrthogonalCellType → CircuitKind
  | .blank => .blank
  | .wire .horizontal _ => .horizontal
  | .wire .vertical _ => .vertical
  | .bend .northeast _ => .northeast
  | .bend .northwest _ => .northwest
  | .bend .southeast _ => .southeast
  | .bend .southwest _ => .southwest
  | .monochromaticVertex _ => .exactone
  | .trichromaticVertex _ => .copy

def sideOfPort (p : Fin 4) : Side :=
  match p.val with | 0 => .north | 1 => .east | 2 => .west | _ => .south

def portOfSide : Side → Fin 4
  | .north => 0 | .east => 1 | .west => 2 | .south => 3

@[simp] theorem side_port (s : Side) : sideOfPort (portOfSide s) = s := by cases s <;> rfl
@[simp] theorem port_side (p : Fin 4) : portOfSide (sideOfPort p) = p := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;> rfl

theorem side_opposite (p : Fin 4) : sideOfPort (gridOpposite p) = (sideOfPort p).opposite := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;> rfl

theorem side_neighbor (c : Cell) (p : Fin 4) : gridNeighbor c p = latticeNeighbor c (sideOfPort p) := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;> rfl

theorem enabled_portColor (t : OrthogonalCellType) (p : Fin 4) :
    (kindOf t).portEnabled p = (t.portColor (sideOfPort p)).isSome := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;>
    cases t with
    | blank => rfl
    | wire axis color => cases axis <;> rfl
    | bend bend color => cases bend <;> rfl
    | monochromaticVertex color => rfl
    | trichromaticVertex order => cases order <;> rfl

theorem inward_relation (t : OrthogonalCellType) (v : Side → Bool) :
    (kindOf t).InwardRelation (fun p => v (sideOfPort p)) ↔ satisfiesOrientation t v := by
  cases t with
  | blank => rfl
  | wire axis color => cases axis <;> simp [kindOf,CircuitKind.InwardRelation,satisfiesOrientation,sideOfPort,ne_comm]
  | bend bend color => cases bend <;> simp [kindOf,CircuitKind.InwardRelation,satisfiesOrientation,sideOfPort,ne_comm]
  | monochromaticVertex color => rfl
  | trichromaticVertex order => rfl

def drawingKinds (drawing : PeriodicOrthogonalDrawing) (c : Cell) : CircuitKind := kindOf (drawing.getAt c)

theorem drawing_ports_matched (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed) :
    PortsMatched (drawingKinds drawing) := by
  intro c p
  simp only [drawingKinds,enabled_portColor,side_neighbor,side_opposite]
  rw [drawing.portColor_latticeNeighbor_eq wf]

theorem drawing_source_correct (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed) :
    drawing.HasOrientation ↔ Circuit.SourceHolds (drawingKinds drawing) := by
  rw [source_iff_inward _ (drawing_ports_matched drawing wf)]
  constructor
  · rintro ⟨_,v,valid,seams⟩
    refine ⟨fun c p => v c (sideOfPort p),?_,?_⟩
    · intro c
      exact (inward_relation _ _).mpr (valid c)
    · intro c p enabled
      dsimp only
      rw [side_neighbor,side_opposite]
      exact seams c (sideOfPort p) (by simpa only [drawingKinds,enabled_portColor] using enabled)
  · rintro ⟨v,valid,seams⟩
    refine ⟨wf,fun c s => v c (portOfSide s),?_,?_⟩
    · intro c
      apply (inward_relation _ _).mp
      simpa only [port_side,drawingKinds] using valid c
    · intro c s enabled
      have h := seams c (portOfSide s) (by simpa only [drawingKinds,enabled_portColor,side_port] using enabled)
      have opp : gridOpposite (portOfSide s) = portOfSide s.opposite := by cases s <;> rfl
      simpa only [side_neighbor,side_port,opp] using h

end LeanTrominoes.CompletionPattern.LBricks
