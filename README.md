# A Vertex-Spread Blow-Up Lemma

This repository contains a Trellis/Lean formalization of Tom Kelly's
manuscript *A Vertex-Spread Blow-Up Lemma*.

The principal Lean declaration is `SpreadBlowup`, corresponding to the
manuscript target `lem:spread-blowup`. It produces a probability distribution
on compatible full embeddings of a bounded-degree graph into a super-regular
blow-up instance with candidacy constraints. The parameters \(\varepsilon\)
and \(C\) are chosen before the number of clusters \(r\). Its conclusion is
the full joint vertex-spread bound: prescribing the images of any \(s\)
distinct source vertices has probability at most \((C/n)^s\).

The formalization was produced using
[Trellis](https://github.com/wpegden/trellis), Wesley Pegden's
autoformalization harness for building verified Lean proof tablets.

## Status

This final snapshot contains 218 closed proof and definition nodes, together
with the preamble. The published snapshot passes the complete
`lake build Tablet` check (3,944 jobs).

The exact formalization checkpoint is
`2c9924e1bc633639c6f5dc54c617c17e75debbd1` (Trellis cycle 322), produced
with Trellis revision `98db307f88de34ac4d6311d2efafeb88b5f21827`.

The project used no project-approved extra axioms:

```json
{
  "global": [],
  "nodes": {}
}
```

The kernel build checks the Lean declarations. Identifying those declarations
and their definitions with the intended mathematics still requires a human
correspondence audit. The saved verification evidence is in `verification/`.
The target axiom check reports only `propext`, `Classical.choice`, and
`Quot.sound`. The [verification notes](verification/README.md) also explain
the retained historical equitable-colouring prose-review record.

## Formalization viewer

The public [formalization viewer](https://tkelly36.github.io/vertex-spread-blow-up-lemma-formalization/#SpreadBlowup)
is the side-by-side TeX/Lean interface for reading and auditing the completed
development. It includes the paper target, its Lean semantic closure, the full
dependency outline, searchable proof nodes, Mathlib links, source links, and
reproducible build metadata.

The viewer is generated into `docs/` and deployed with GitHub Pages. The
resolved semantic closures are also shipped in
`formalization/semantic-closure.json` so they can be reused when rebuilding
the viewer.

## Repository layout

- `formalization/` is the complete buildable Lean artifact.
- `formalization/Tablet/` contains paired `.lean` and `.tex` proof nodes.
- `formalization/Tablet/SpreadBlowup.lean` contains the main theorem.
- `formalization/Tablet/INDEX.md` records the node dependency graph.
- `formalization/Tablet.lean` is the generated root import surface.
- `formalization/semantic-closure.json` records the resolved semantic closures.
- `docs/` is the generated public formalization viewer.
- `verification/` contains the saved build and verification evidence.
- `scripts/` contains release validation and viewer rebuilding tools.
- `paper/README.md` records the frozen manuscript provenance and target label.

The frozen manuscript source, Trellis runtime state, and supervisor history
are not distributed in this public repository.

## Reproducing the Lean check

The development uses Lean `v4.30.0-rc1` and Mathlib revision
`a090f46da78e9af11fee348cd7ee47bf8dd219d2`. Its dependencies on the checked
Egorychev–Falikman, Hajnal–Szemerédi, and entropy-methods libraries are pinned
to exact revisions in `formalization/lakefile.lean` and
`formalization/lake-manifest.json`.

From the repository root:

```bash
cd formalization
lake exe cache get
lake build Tablet
```

Validate the exported viewer and source hashes with
`python3 scripts/validate_release.py`. Rebuild the viewer using
`bash scripts/rebuild_viewer.sh /path/to/trellis-checkout` at the Trellis
revision recorded above.

## Reading the proof

Start with `SpreadBlowup` and the definitions `BlowUpInstance`,
`CandidacySystem`, `CompatibleEmbedding`, and `VertexSpreadOn`. Each theorem
or definition node has a Lean file and a matching natural-language TeX file.
Use the viewer or `formalization/Tablet/INDEX.md` to follow the dependencies.

## Credits

The mathematical result is due to Tom Kelly. The formal artifact was
generated with [Trellis](https://github.com/wpegden/trellis), created by
Wesley Pegden, and checked with Lean and Mathlib. The development also reuses
the pinned checked libraries listed above.
