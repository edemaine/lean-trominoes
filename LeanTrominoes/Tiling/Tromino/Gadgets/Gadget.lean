/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetCore
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetWireSignatureCounts

/-!
# Finite tromino gadget windows

This public module includes the gadget definitions, exact-cover search, and
kernel-checked red-wire signature counts. The core definitions live in a
separate module so their geometric search certificates can depend on them.
-/
