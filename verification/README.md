# Release verification

The published Lean and paired TeX files are copied without mathematical edits
from source checkpoint `2c9924e1bc633639c6f5dc54c617c17e75debbd1`.
Trellis recorded phase and stage `Complete` at cycle 322, with 218 ordinary
nodes closed and a shared preamble. There were no open nodes, sketches,
placeholder definitions, unverified local closures, or local closure failures.
The correspondence and substantiveness records for current nodes passed, as
did the paper-target check for `lem:spread-blowup`.

On 2026-10-15, `lake build Tablet` completed successfully with 3,944 jobs.
The viewer exporter then imported the built root module and checked:

```text
'SpreadBlowup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No project-approved extra axioms were used. `completion.json` preserves a
compact extraction of the final run state; `lean-build.log` records the build;
`source-sha256.json` pins the published mathematical sources and dependency
manifest. The successful target axiom probe and exporter/toolchain metadata
are also included in `docs/data/build-info.toml`.

## Historical equitable-colouring review record

The final state retains an earlier `ReviewerPinnedFail` prose-review record
for `EquitableSquareColoring`. Its current Lean source matches the accepted
local closure certificate revalidated at cycle 316, with an agreed axiom check
and only `propext`, `Classical.choice`, and `Quot.sound`. The full release build
also checks this proof through `SpreadBlowup`.

The run's own process-memory note, reproduced in
`checked-library-acceptance.md`, records the earlier checked-Hajnal–Szemerédi
import incident as superseded by authoritative acceptance at cycle 112.
Trellis requires the prose soundness review for open proof nodes; this node
is closed. The retained record therefore does not prevent completion. This
release preserves that distinction and does not claim that every historical
prose review passed. No review flag or protocol state was edited for publication.
