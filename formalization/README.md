# Vertex-spread blow-up lemma: Lean artifact

| Paper label | Lean module | Result |
|---|---|---|
| `lem:spread-blowup` | `Tablet.SpreadBlowup` | Vertex-spread blow-up lemma |

The principal declaration is `SpreadBlowup`. The complete development has
218 paired proof and definition nodes plus the shared `Preamble`.

```bash
lake build Tablet
```

The toolchain, Mathlib, and the three reused formalization libraries are pinned
in `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`. The
`semantic-closure.json` file preserves the accepted declaration dependencies
used by the public viewer. See the repository README and `verification/` for
the source checkpoint, build evidence, and historical review context.
