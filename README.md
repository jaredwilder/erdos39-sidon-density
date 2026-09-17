# Erdős #39 — infinite Sidon sets and density

A Sidon set here means a set with distinct unordered pair sums, including repeated summands. Erdős #39 asks whether there is a single infinite Sidon set `A` satisfying

\[
|A\cap[1,N]|\gg_\varepsilon N^{1/2-\varepsilon}
\]

for every `\varepsilon>0`.

This repository formalizes elementary upper and lower density bounds and an explicit infinite construction.

## Lean results

[`research/E39.lean`](research/E39.lean) proves:

- if a finite Sidon set lies in `[1,N]` and has size `k`, then

  \[
  k^2\le k+2N+1;
  \]

- for every `N`, there exists a Sidon subset of `[1,N]` with

  \[
  N\le 3k^3;
  \]

- an explicitly defined infinite set `Greedy` is Sidon and satisfies

  \[
  N\le 3\bigl(|Greedy\cap[1,N]|+1\bigr)^3.
  \]

Thus the formal construction gives an infinite Sidon set at the `N^{1/3}` density scale.

## Numerical controls

[`research/sidon_receipts.py`](research/sidon_receipts.py) implements two Sidon criteria, greedy constructions, finite examples, and density checks. The fresh control suite compares the criteria on 4,511 sets and checks small prime constructions.

The formal `Greedy` predicate over-approximates forbidden values using natural-number operations. It is therefore not identified in Lean with the standard Mian–Chowla sequence, although the bounded replay records matching first terms.

## Reproduce

```sh
python verification/verify_source.py
python verification/run_controls.py
```

The historical Lean receipt records successful compilation with Lean `v4.31.0-rc1` and Mathlib `919544d4309104b3f19724b0e6e48c701d27948f`.

The near-square-root density requested by Erdős #39 is not proved here; the repository supplies the formal `N^{1/3}`-scale construction and accompanying finite bounds.

Author: Jared Wilder. License: Apache-2.0.
