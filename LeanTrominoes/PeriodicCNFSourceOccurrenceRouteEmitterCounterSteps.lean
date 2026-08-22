/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterCopyNilStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterCopyConsStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterRestoreNilStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterRestoreConsStep

/-! # Counter-copy steps for source-occurrence route emission

The four transition forms live in separate leaf modules so that Lean never
elaborates all counter proofs in one memory-heavy job.
-/
