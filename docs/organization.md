# Repository organization

The module tree follows mathematical subjects. The paper's order is retained
in the main README's result and coverage tables.

| Paper material | Modules |
| --- | --- |
| Section 2: periodic graphs and drawings | `Graphs/Core`, `Graphs/Drawings` |
| Section 3: SAT problems and reductions | `SAT` |
| Section 3: planar 3DM | `ThreeDM` |
| Section 3: trichromatic graph orientation | `Graphs/Orientation` |
| Section 4: 2SAT and Horn algorithms | `SAT/TwoSAT`, `SAT/Horn` |
| Section 4: graph matching algorithms | `Graphs/Matching` |
| Section 5: tiling and completion | `Tiling` |

Finite, line, plane, and slab variants remain with their mathematical subject.
General computation infrastructure is in `Computation`; complexity interfaces
and generic certification are in `Complexity`. Specialized compilers remain
with the reductions they implement. In particular, the CNF-to-tromino strip
compiler lives in `Tiling/Tromino/Strip`, while SAT-specific occurrence-splitting
geometry lives in `SAT/Planar/OccurrenceSplit`.

The largest families have further subdivisions for carriers, routes, raster
requests, encodings, and finite certificates. Descriptive filenames are retained
so existing searches and links remain recognizable.

## Imports and declarations

Each main subject has a `Results.lean` facade collecting the results previously
exposed by the public root. `LeanTrominoes.lean` imports those facades. Orientation
has an additional `Graphs/Orientation/Results.lean` entry point.

File/module paths changed; declaration namespaces and theorem names did not.
For example:

```lean
import LeanTrominoes.Tiling.Tromino.Theorem52Proof

#check LeanTrominoes.Theorem52.proved
```

The [module relocation map](../data/module-relocations.json) records every old
module name and its new name. The structural checker also supports lookup:

```sh
python scripts/check_module_layout.py --lookup LeanTrominoes.Theorem52Proof
```

The generic periodic graph representation is now in
[Graphs/Core/PeriodicGraph.lean](../LeanTrominoes/Graphs/Core/PeriodicGraph.lean).
CNF incidence vertices, edges, and graph properties are in
[SAT/CNF/IncidenceData.lean](../LeanTrominoes/SAT/CNF/IncidenceData.lean) and
[SAT/CNF/Incidence.lean](../LeanTrominoes/SAT/CNF/Incidence.lean).
SAT obtains integer-cell infrastructure directly from `Common/Geometry/CellData`.

## Building and verification

Lake's existing `LeanTrominoes.*` glob includes nested modules.

```sh
python scripts/check_module_layout.py
lake build
```

For machines that need bounded compiler concurrency:

```sh
python scripts/build_subjects.py
python scripts/build_subjects.py --resume
python scripts/build_subjects.py --resume --batch-size 4
```

This invokes Lake with bounded compiler concurrency and retains its ordinary
build traces. Batches share Lake startup while each worker compiles sequentially.
Completed modules release their dependents before the rest of the batch finishes.
Build logs and resumable state are written to
`tmp/organization-build`. A final ordinary Lake build checks the complete library.

[Verification/All.lean](../LeanTrominoes/Verification/All.lean) and the generated
`Verification/Isolated` batches jointly cover every local module, including the
axiom regression checks and modules outside the curated public root. Some legacy
helpers independently use the same declaration name for different statements;
separate batches preserve both versions. For an optional full fresh kernel replay:

```sh
python scripts/check_module_layout.py --kernel
```

This rechecks imported foundations and dependencies as well as project proofs.
It can take hours and substantial memory. The ordinary build already sends each
module's declarations to Lean's kernel; full fresh replay additionally detects
imported-environment inconsistencies.

After adding modules, update that entry point:

```sh
python scripts/check_module_layout.py --write-all
```

If a new duplicate declaration prevents an aggregate import, first build the
affected modules individually, then refresh the compiled declaration catalogue:

```sh
python scripts/check_module_layout.py --refresh-conflicts --write-all
```

The catalogue in `data/verification-conflicts.json` separates incompatible
declarations. Matching generated equation theorems can share a batch; Lean's
ordinary import checks validate every generated batch before kernel replay.

The one-time migration invariant can be rechecked against the recorded Git
baseline with `python scripts/check_module_layout.py --baseline`. This compares
declaration bodies and namespaces, allowing the documented graph/SAT extraction.
Routine later proof changes need only the ordinary structural check.

## Generators

The scripts in `scripts/completion_*.py` write generated data and certificates
under `Tiling/Completion`. Their imports use the new module paths; generated
declarations retain the existing completion namespaces.
