# Stability of Change-of-Numéraire Reweighting — Lean formalization

Machine-checked proofs, in Lean 4 with Mathlib, of the results of

> Shaosai Huang, *Stability of Change-of-Numéraire Reweighting: An Exact
> Wasserstein Boundary* (2026), preprint.

The paper characterizes exactly when reweighting a law by a positive numéraire
and pushing forward the payoff-to-numéraire ratio is stable in the
Wasserstein distance `W_s`.

## What is proved

| Paper | Lean |
|---|---|
| Proposition 2.1 (perspective cancellation) | `cancellation_general`, `cancellation_call`, `cancellation_first_moment`, `cancellation_moment`, `hasFiniteMoment_one_of_integrable`, `hasFiniteMoment_iff` |
| §3.1 (the reweighted limit is a probability law; limit identity; `E[A_n] → m`) | `reweight_isProbabilityMeasure`, `reweight_lintegral_boundary`, `mean_tendsto` |
| Lemma 3.1 (weak stability) | `weak_stability` |
| Theorem 3.3 (exact two-way `W_s` boundary) | `exact_two_way_boundary` |
| Corollary 3.4 | `sharp_cancellation`, `sharp_cancellation_of_no_boundary`, `boundary_free_iff_unifIntegrable` |
| Examples 4.1, 4.3, 4.4 | `exTwoAtom_mean`, `reweight_exTwoAtom`, `exTwoAtom_moment`, `example_4_1`, `example_4_3`, `example_4_4` |
| Theorem 5.1 (joint continuity, compact image, affine slices) | `joint_continuity`, `image_compact`, `reweightAt_projective`, `mixture_formula`, `affine_on_slice` |
| Eq. (11) and Corollary 6.1 (the change-of-numéraire involution) | `involution_moment`, `involution_stability`, `involution_w1` |
| §6.1 consequences | `involution_second_moment_iff`, `involution_w2_iff`, `involution_two_atom` |
| §6.2 (annuity-measure swap-rate marginals) | `unifIntegrableOn_of_bounded`, `annuity_ratioTail`, `annuity_w1_continuity`, `annuity_calls_uniform`, `annuity_prices_uniform`, `annuity_second_moment`, `annuity_second_moment_stability`, `example_4_1_calls_second_moment`, `cash_settled` |
| Non-vacuity of the hypotheses of Theorem 5.1 and §6.2 | `jointSetting_example`, `annuitySetting_example` |

All statements are in [`lean/NumeraireStability.lean`](lean/NumeraireStability.lean)
and all definitions in [`lean/NumeraireStability/Defs.lean`](lean/NumeraireStability/Defs.lean)
and [`lean/NumeraireStability/Defs56.lean`](lean/NumeraireStability/Defs56.lean).

**Not formalized**, because it is commentary rather than a mathematical claim:
Remark 5.2's point about averaging models, that `S` is an involution (cited, not
proved, in the paper), and the paper's remarks about other authors' results and
about market pricing measures.

## What to trust

There is no `sorry` and no added axiom.  Every statement depends only on Lean's
standard axioms `propext`, `Classical.choice` and `Quot.sound`;
[`lean/check-axioms.sh`](lean/check-axioms.sh) prints them and fails otherwise,
and CI re-runs it on every push.  Nothing is assumed about Wasserstein distances: the classical fact
that weak convergence plus convergence of `s`-th moments gives `W_s`
convergence (Villani, *Optimal Transport*, Theorem 6.9), which Theorem 3.3
uses, is proved here on `ℝ` through the quantile coupling.

What a reader still has to check is that the Lean statements say what the
paper says.  The conventions:

1. A pair `(A, B)` is represented by its law `Q` on `ℝ × ℝ`; `p.1` is the
   numéraire `a`, `p.2` the payoff `b`.
2. The closed half-plane is imposed by support conditions (`Q_n{a ≤ 0} = 0`,
   `Q{a < 0} = 0`); weak convergence is taken on `ℝ × ℝ`, which for such laws
   is weak convergence on `[0, ∞) × ℝ`.
3. One definition, `reweight`, serves for `Γ_n` and for the limit `Γ`:
   Lean's `b / 0 = 0` is the paper's `T(0, b) := 0`, and
   `reweight_lintegral_boundary` identifies the paper's limit object.
4. `E[A] ∈ (0, ∞)` is written `0 < numeraireMean Q` (the Bochner integral of a
   non-integrable function is `0`).
5. `W_s` is defined from scratch as the infimum over couplings.
6. Uniform integrability of a sequence with changing laws is
   `lim_{M → ∞} sup_n E_{Q_n}[g ; g > M] = 0`.
7. The examples are proved slightly more generally than stated in the paper
   (sequences tending to `0`, not necessarily monotone).
8. Model classes in Section 5 are sets `K` of `ProbabilityMeasure Ω` on a
   Polish `Ω`, with Mathlib's weak topology; `F a ω = (A_a(ω), B_a(ω))` on a
   compact metric parameter space.  Continuity into `(𝒫_s, W_s)` is
   `W_s(Γ(y), Γ(x)) → 0` as `y → x` within `K × 𝔸`; compactness of the image
   is stated as sequential compactness.
9. `inf E_Q[A_a] > 0` is a positive lower bound `c`; the mixture formula is
   proved for `Q₁, Q₂ ∈ K` without requiring the mixture to lie in `K`.
10. In Corollary 6.1, weak convergence on `(0, ∞)` is stated on `ℝ` (the limit
    also lives on `(0, ∞)`); in §6.2 the physically settled price is
    `E_Q[(B_a - k A_a)⁺]` and "stability of the raw second moment" means finite
    second moments that converge.

`example_4_1` shows that the standing hypotheses hold for a concrete
sequence, so Theorem 3.3 is not vacuously true; `jointSetting_example` and
`annuitySetting_example` do the same for Theorem 5.1 and §6.2.

## Build

Requires [elan](https://github.com/leanprover/elan).

```
cd lean
lake exe cache get
lake build
./check-axioms.sh
```

## Layout

All paths are inside [`lean/`](lean).

| File | Contents |
|---|---|
| `NumeraireStability.lean` | the paper's statements |
| `NumeraireStability/Defs.lean`, `Defs56.lean` | definitions |
| `NumeraireStability/Cancellation.lean` | Proposition 2.1 |
| `NumeraireStability/WeakLimits.lean` | weak convergence with uniformly integrable tails, both directions |
| `NumeraireStability/Stability.lean` | `E[A_n] → m`, Lemma 3.1 |
| `NumeraireStability/Wasserstein.lean` | Minkowski through a coupling; `W_s` to a point mass |
| `NumeraireStability/Quantile.lean` | quantile coupling; weak + moments ⇒ `W_s` |
| `NumeraireStability/Boundary.lean` | Theorem 3.3 |
| `NumeraireStability/Corollary.lean` | Corollary 3.4 |
| `NumeraireStability/TwoAtoms.lean`, `Example41.lean`, `Example43_44.lean` | Section 4 |
| `NumeraireStability/Pushforward.lean`, `JointContinuity.lean` | Theorem 5.1 |
| `NumeraireStability/Involution.lean` | §6.1 |
| `NumeraireStability/Annuity.lean` | §6.2 |
| `AxiomCheck.lean`, `check-axioms.sh` | the axiom check |
| `spec/Statements_step1.lean`, `spec/Statements56_step1.lean` | the statements as fixed before any proof was written, for Sections 2–4 and 5–6 (not built) |

## How this was produced

The formal statements were written first and fixed before any proof was
attempted, in two rounds (Sections 2–4, then Sections 5–6);
`spec/Statements_step1.lean` and `spec/Statements56_step1.lean` are those
versions, and the statements in `NumeraireStability.lean` are identical to
them.  The proofs were then developed
with AI assistance (Anthropic's Claude Code).  Every proof is
checked by Lean's kernel, so no step relies on the assistant being right.

## License

Apache License 2.0; see [LICENSE](../LICENSE).  © 2026 Shaosai Huang.
