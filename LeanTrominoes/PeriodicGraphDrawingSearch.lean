/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraphDrawingCertificate
import LeanTrominoes.PeriodicThreeDMFiniteDrawingSearch

/-! # Computable search for checked periodic planar drawings -/
noncomputable section
namespace LeanTrominoes.PeriodicGridDrawing.FiniteCertificate
open PeriodicThreeDM.FiniteDrawingSearch
variable {A V : Type} [Primcodable A] [Primcodable V] [DecidableEq V]

private theorem candidate_exists (graph : A → PeriodicGraph V)
    (available : ∀ a, ∃ d, Valid (graph a) d) (a : A) :
    ∃ n, Valid (graph a) (drawingAt n) := by
  obtain ⟨d, hd⟩ := available a
  exact ⟨Encodable.encode d, by simpa only [drawingAt_encode] using hd⟩

open Classical in
def search (graph : A → PeriodicGraph V)
    (available : ∀ a, ∃ d, Valid (graph a) d) (a : A) : PeriodicGridDrawing :=
  drawingAt (Nat.find (candidate_exists graph available a))

theorem search_spec (graph : A → PeriodicGraph V)
    (available : ∀ a, ∃ d, Valid (graph a) d) (a : A) :
    Valid (graph a) (search graph available a) := by
  classical
  exact Nat.find_spec (candidate_exists graph available a)

theorem search_computable {graph : A → PeriodicGraph V} (hg : Computable graph)
    (available : ∀ a, ∃ d, Valid (graph a) d) : Computable (search graph available) := by
  classical
  have predicate : ComputablePred fun p : A × Nat => Valid (graph p.1) (drawingAt p.2) :=
    (valid_primrec.decide.to_comp.comp
      (hg.comp Computable.fst) (drawingAt_primrec.to_comp.comp Computable.snd)).computablePred
  exact drawingAt_primrec.to_comp.comp
    (Computable.find predicate (candidate_exists graph available))

end LeanTrominoes.PeriodicGridDrawing.FiniteCertificate
