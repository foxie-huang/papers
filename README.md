# Papers — machine-checked proofs

Lean 4 formalizations of results in papers by Shaosai Huang (Kspectra
Research).  Each paper has its own folder, and each formalization is a
self-contained Lake project with its own Lean and Mathlib versions, so adding
a paper never forces an old formalization to upgrade.

| Paper | Folder | Formalized | Lean / Mathlib |
|---|---|---|---|
| *Stability of Change-of-Numéraire Reweighting: An Exact Wasserstein Boundary* (2026)<br>[arXiv](https://arxiv.org/abs/2609.30329) · [SSRN](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7383120) | [`numeraire-stability/`](numeraire-stability) | Every proposition, lemma, theorem and corollary, the examples of Section 4 and the conclusions of Section 6 (42 statements) | v4.34.0 / v4.34.0 |

## Checking a formalization

Requires [elan](https://github.com/leanprover/elan).

```
cd <paper>/lean
lake exe cache get
lake build
./check-axioms.sh
```

`check-axioms.sh` prints the axioms each paper statement depends on and fails
unless all of them are Lean's standard `propext`, `Classical.choice` and
`Quot.sound` (so no `sorry` and no added axiom).  CI runs the same check for
every paper on each push.

What a reader still has to check is that the Lean statements say what the
paper says; each paper's README lists the modelling conventions.

## License

Apache License 2.0; see [LICENSE](LICENSE).  © 2026 Shaosai Huang.
