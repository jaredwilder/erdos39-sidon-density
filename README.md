# Erdős #39: infinite Sidon sets and density

Can one infinite Sidon set `A` have `|A ∩ [1,N]| ≫ε N^(1/2−ε)` for every
`ε>0`? A Sidon set here has distinct unordered pair sums, **including repeated
summands**. The implicit constant and starting threshold may depend on ε.

This repository organizes Jared Wilder's formal bounds, explicit infinite
construction, numerical controls and original research receipts. The package
does not prove the near-square-root density requested by #39.

## Mathematical results

The [Lean source](research/E39.lean) proves:

- If a finite Sidon set lies in `[1,N]` and has size `k`, then
  `k² ≤ k + 2N + 1` (`sidon_card_sq_le`).
- For every `N`, some Sidon subset of `[1,N]` has `N ≤ 3k³`
  (`exists_dense_sidon`).
- Its explicitly defined infinite set `Greedy` is Sidon, with
  `N ≤ 3 (|Greedy ∩ [1,N]| + 1)³` for every `N`
  (`greedy_is_sidon`, `greedy_infinite`, `greedy_density`).

These are elementary density bounds and formal infrastructure. The finite
square-root-scale constructions in the numerical study do not produce a
single infinite set with the required uniform density.

## Read and reproduce

| File | Role |
|---|---|
| [E39.lean](research/E39.lean) | Problem definition, finite bounds, infinite construction and proofs |
| [Build receipt](research/build-receipt.txt) | Historical successful build and 14 named axiom checks |
| [Computational program](research/sidon_receipts.py) | Two Sidon criteria, greedy sequences, finite constructions and density controls |
| [Original numerical receipt](research/receipts.json) | Preserved historical results, not a new run |
| [Small replay](verification/REPLAY-2026-09-13.json) | Fresh bounded controls and their actual witnesses |

The formal `Blocked` predicate over-approximates forbidden values, using
natural-number truncated subtraction and floor division. Accordingly the
formal `Greedy` construction is **not identified with the standard
Mian–Chowla sequence** computed by the other branch of the Python program.
No equivalence of the two definitions is formalized in this package. The
small replay checks both and records their matching first 30 terms.

With Python 3 (standard library only):

```sh
python verification/verify_source.py
python verification/run_controls.py
```

The controls compare the two Sidon criteria on 4,511 sets, build 40 standard
greedy and 30 formal-predicate terms, and check nine small prime constructions.
These computations are finite controls, not proofs of the infinite statements.
The original script writes `receipts.json` in its working directory; run it in
a separate output directory if repeating the larger historical experiment.

The historical Lean receipt records Lean `v4.31.0-rc1`, Mathlib
`919544d4309104b3f19724b0e6e48c701d27948f`, successful compilation and only
standard Lean axioms for its named checks. The source SHA-256 matches that
receipt. A fresh Lean build was not performed for this release.

## Provenance

All four research files are byte-identical to their public archive versions.
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) records the pinned source commit,
original paths, sizes, Git blob IDs and SHA-256 hashes. The
[campaign archive](https://github.com/jaredwilder/erdos-campaign-archive)
retains the historical originals; this is the focused entry point.

Author: Jared Wilder. Campaign: 2026-09-05. Focused release: 2026-09-13.
License: inherited Apache-2.0; see [LICENSE](LICENSE).
