/-
# Stability of Change-of-Numéraire Reweighting — Lean statements for §5 and §6 (step 1)

Formal statements of Sections 5 and 6 of

  S. Huang, "Stability of Change-of-Numéraire Reweighting: An Exact
  Wasserstein Boundary" (2026):

Theorem 5.1 (joint continuity, compact image, affine slices), equation (11),
Corollary 6.1 and the two consequences drawn from it in §6.1, and the three
conclusions of §6.2 (annuity-measure swap-rate marginals).

Every proof is `sorry`.  This file exists to be REVIEWED: each statement must
say what the paper says.  It builds on the definitions already fixed for
Sections 2–4 (`NumeraireStability/Defs.lean`) and adds the definitions below.

Conventions (as before).  A law of `(A, B)` is a measure on `ℝ × ℝ`; `p.1` is
the numéraire coordinate `a`, `p.2` the payoff coordinate `b`; Lean's
`b / 0 = 0` is the paper's `T(0, b) := 0`.
-/
import NumeraireStability.Defs
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-! ## Definitions for Sections 5 and 6 -/

/-- Uniform integrability of `g(A, B)` over an arbitrary family of laws `L i`:
`lim_{M → ∞} sup_i E_{L i}[g ; g > M] = 0`.  For `ι = ℕ` this is
`UnifIntegrableFamily`. -/
def UnifIntegrableOn {ι : Type*} (L : ι → Measure (ℝ × ℝ)) (g : ℝ × ℝ → ℝ≥0∞) : Prop :=
  Tendsto (fun M : ℝ => ⨆ i, ∫⁻ p in {p | ENNReal.ofReal M < g p}, g p ∂(L i))
    atTop (𝓝 0)

/-- The ratio tail over an arbitrary family of laws,
`sup_i E_{L i}[|B|^s A^{1-s} ; |B| > R A]`.  For `ι = ℕ` this is `ratioTail`. -/
def ratioTailOn {ι : Type*} (s : ℝ) (L : ι → Measure (ℝ × ℝ)) (R : ℝ) : ℝ≥0∞ :=
  ⨆ i, ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂(L i)

/-- The law of `(A_a, B_a)` under a model law `Q`, where
`F a ω = (A_a(ω), B_a(ω))`. -/
def contractLaw {Ω 𝔸 : Type*} [MeasurableSpace Ω] (F : 𝔸 → Ω → ℝ × ℝ)
    (Q : Measure Ω) (a : 𝔸) : Measure (ℝ × ℝ) :=
  Q.map (F a)

/-- `Γ_a(Q)`: the reweighting (1) applied to the law of `(A_a, B_a)` under `Q`
(Theorem 5.1(i)). -/
def reweightAt {Ω 𝔸 : Type*} [MeasurableSpace Ω] (F : 𝔸 → Ω → ℝ × ℝ)
    (Q : Measure Ω) (a : 𝔸) : Measure ℝ :=
  reweight (contractLaw F Q a)

/-- The numerator of the reweighting: `A · (law of (A, B))`, pushed forward by
`B / A`.  `Γ(P)` is this measure divided by `E_P[A]` (Theorem 5.1(iii)). -/
def reweightNumerator (P : Measure (ℝ × ℝ)) : Measure ℝ :=
  (P.withDensity fun p => ENNReal.ofReal p.1).map fun p => p.2 / p.1

/-- The normalized call price `∫ (z - k)⁺ dΓ` of a law `Γ` on `ℝ`. -/
def normCall (Γ : Measure ℝ) (k : ℝ) : ℝ :=
  ∫ z, max (z - k) 0 ∂Γ

/-- The physically settled (payer) swaption price `E_Q[(B_a - k A_a)⁺]`
(§6.2, item 1); by Proposition 2.1 it equals `E_Q[A_a] · normCall (Γ_a(Q)) k`. -/
def payerPrice {Ω 𝔸 : Type*} [MeasurableSpace Ω] (F : 𝔸 → Ω → ℝ × ℝ)
    (Q : Measure Ω) (a : 𝔸) (k : ℝ) : ℝ :=
  ∫ ω, max ((F a ω).2 - k * (F a ω).1) 0 ∂Q

/-- The change-of-numéraire transform of §6.1,
`S(μ) := law of 1/X under (X / m(μ)) dμ`: the reweighting (1) with
`(A, B) = (X, 1)`. -/
def involution (μ : Measure ℝ) : Measure ℝ :=
  reweight (μ.map fun x => (x, (1 : ℝ)))

/-- Uniform integrability of `g(X_n)` for real laws `μ n`:
`lim_{M → ∞} sup_n E_{μ n}[g ; g > M] = 0`. -/
def UnifIntegrableReal (μ : ℕ → Measure ℝ) (g : ℝ → ℝ≥0∞) : Prop :=
  Tendsto (fun M : ℝ => ⨆ n, ∫⁻ x in {x | ENNReal.ofReal M < g x}, g x ∂(μ n))
    atTop (𝓝 0)

/-- The two-atom laws of §6.1: mass `1 - ε` at `1` and mass `ε` at `ε`. -/
def exInvolutionTwoAtom (ε : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - ε) • Measure.dirac (1 : ℝ) + ENNReal.ofReal ε • Measure.dirac ε

/-! ## Section 5 — Theorem 5.1 -/

section JointContinuity

variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {𝔸 : Type*} [MetricSpace 𝔸] [CompactSpace 𝔸]

/-- The hypotheses of Theorem 5.1.  `Ω` is Polish and `𝔸` is a compact metric
space (instance arguments); `K` is a compact set of Borel probability laws on
`Ω` in the weak topology (Mathlib's topology on `ProbabilityMeasure Ω`);
`(a, ω) ↦ (A_a(ω), B_a(ω)) = F a ω` is jointly continuous with values in
`(0, ∞) × ℝ`; the uniform ratio-tail condition (10) holds at order `s`; the
numéraires `{A_a : (Q, a) ∈ K × 𝔸}` are uniformly integrable; and
`inf_{(Q, a)} E_Q[A_a] > 0`. -/
structure JointSetting (F : 𝔸 → Ω → ℝ × ℝ) (K : Set (ProbabilityMeasure Ω)) (s : ℝ) :
    Prop where
  compact : IsCompact K
  cont : Continuous fun x : 𝔸 × Ω => F x.1 x.2
  pos : ∀ a ω, 0 < (F a ω).1
  /-- (10): `lim_R sup_{(Q,a) ∈ K × 𝔸} E_Q[|B_a|^s A_a^{1-s} ; |B_a| > R A_a] = 0`. -/
  tail : Tendsto (ratioTailOn s fun x : K × 𝔸 => contractLaw F (x.1 : Measure Ω) x.2)
    atTop (𝓝 0)
  ui : UnifIntegrableOn (fun x : K × 𝔸 => contractLaw F (x.1 : Measure Ω) x.2)
    fun p => ENNReal.ofReal p.1
  mean_pos : ∃ c : ℝ, 0 < c ∧
    ∀ x : K × 𝔸, c ≤ numeraireMean (contractLaw F (x.1 : Measure Ω) x.2)

variable {F : 𝔸 → Ω → ℝ × ℝ} {K : Set (ProbabilityMeasure Ω)} {s : ℝ}

/-- Theorem 5.1(i).  `Γ_a(Q) ∈ 𝒫_s(ℝ)` for every `(Q, a) ∈ K × 𝔸`, and
`(Q, a) ↦ Γ_a(Q)` is continuous from `K × 𝔸` into `(𝒫_s(ℝ), W_s)`: at every
point `x` of `K × 𝔸`, `W_s(Γ(y), Γ(x)) → 0` as `y → x` within `K × 𝔸`. -/
theorem joint_continuity (h : JointSetting F K s) (hs : 1 ≤ s) :
    (∀ Q ∈ K, ∀ a, HasFiniteMoment s (reweightAt F (Q : Measure Ω) a)) ∧
    ∀ x ∈ K ×ˢ (Set.univ : Set 𝔸),
      Tendsto (fun y : ProbabilityMeasure Ω × 𝔸 =>
          wasserstein s (reweightAt F (y.1 : Measure Ω) y.2)
            (reweightAt F (x.1 : Measure Ω) x.2))
        (𝓝[K ×ˢ Set.univ] x) (𝓝 0) :=
  sorry

/-- Theorem 5.1(ii).  The image `{Γ_a(Q) : (Q, a) ∈ K × 𝔸}` is compact in
`(𝒫_s(ℝ), W_s)`, stated as sequential compactness (equivalent in a metric
space): for every sequence `(Q_n, a_n)` in `K × 𝔸` there are `(Q, a) ∈ K × 𝔸`
and a subsequence along which `W_s(Γ_{a_n}(Q_n), Γ_a(Q)) → 0`. -/
theorem image_compact (h : JointSetting F K s) (hs : 1 ≤ s)
    (y : ℕ → ProbabilityMeasure Ω × 𝔸) (hy : ∀ n, (y n).1 ∈ K) :
    ∃ x ∈ K ×ˢ (Set.univ : Set 𝔸), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => wasserstein s (reweightAt F ((y (φ k)).1 : Measure Ω) (y (φ k)).2)
          (reweightAt F (x.1 : Measure Ω) x.2)) atTop (𝓝 0) :=
  sorry

/-- Theorem 5.1(iii), "projective (a ratio of two affine maps)": for every
`(Q, a)` with `Q ∈ K`, `Γ_a(Q) = E_Q[A_a]⁻¹ · N_a(Q)`, where the numerator
`N_a(Q) = reweightNumerator (law of (A_a, B_a) under Q)` is additive and
positively homogeneous in `Q` and `Q ↦ E_Q[A_a]` is affine on mixtures of
laws in `K`. -/
theorem reweightAt_projective (h : JointSetting F K s) (a : 𝔸) :
    (∀ Q ∈ K, reweightAt F (Q : Measure Ω) a =
      (ENNReal.ofReal (numeraireMean (contractLaw F (Q : Measure Ω) a)))⁻¹ •
        reweightNumerator (contractLaw F (Q : Measure Ω) a)) ∧
    (∀ (c₁ c₂ : ℝ≥0∞) (Q₁ Q₂ : Measure Ω),
      reweightNumerator (contractLaw F (c₁ • Q₁ + c₂ • Q₂) a) =
        c₁ • reweightNumerator (contractLaw F Q₁ a) +
          c₂ • reweightNumerator (contractLaw F Q₂ a)) ∧
    (∀ Q₁ ∈ K, ∀ Q₂ ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      numeraireMean (contractLaw F
          (ENNReal.ofReal t • (Q₁ : Measure Ω) + ENNReal.ofReal (1 - t) • (Q₂ : Measure Ω)) a) =
        t * numeraireMean (contractLaw F (Q₁ : Measure Ω) a) +
          (1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a)) :=
  sorry

/-- Theorem 5.1(iii), mixture formula: for `Q₁, Q₂ ∈ K` and `t ∈ [0, 1]`,
mixtures reweight by relative numéraire value:
`Γ_a(t Q₁ + (1 - t) Q₂) = (w₁ Γ_a(Q₁) + w₂ Γ_a(Q₂)) / (w₁ + w₂)` with
`w₁ = t E_{Q₁}[A_a]` and `w₂ = (1 - t) E_{Q₂}[A_a]`. -/
theorem mixture_formula (h : JointSetting F K s) {Q₁ Q₂ : ProbabilityMeasure Ω}
    (h₁ : Q₁ ∈ K) (h₂ : Q₂ ∈ K) (a : 𝔸) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    reweightAt F (ENNReal.ofReal t • (Q₁ : Measure Ω) + ENNReal.ofReal (1 - t) • (Q₂ : Measure Ω)) a =
      ENNReal.ofReal (t * numeraireMean (contractLaw F (Q₁ : Measure Ω) a) /
          (t * numeraireMean (contractLaw F (Q₁ : Measure Ω) a) +
            (1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a))) •
          reweightAt F (Q₁ : Measure Ω) a +
        ENNReal.ofReal ((1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a) /
          (t * numeraireMean (contractLaw F (Q₁ : Measure Ω) a) +
            (1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a))) •
          reweightAt F (Q₂ : Measure Ω) a :=
  sorry

/-- Theorem 5.1(iii), calibration slices: if `E_{Q₁}[A_a] = E_{Q₂}[A_a] = c`
(both laws in the slice `K_c`), then `Q ↦ Γ_a(Q)` is affine on their mixtures:
`Γ_a(t Q₁ + (1 - t) Q₂) = t Γ_a(Q₁) + (1 - t) Γ_a(Q₂)`. -/
theorem affine_on_slice (h : JointSetting F K s) {Q₁ Q₂ : ProbabilityMeasure Ω}
    (h₁ : Q₁ ∈ K) (h₂ : Q₂ ∈ K) (a : 𝔸) {c : ℝ}
    (hc₁ : numeraireMean (contractLaw F (Q₁ : Measure Ω) a) = c)
    (hc₂ : numeraireMean (contractLaw F (Q₂ : Measure Ω) a) = c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    reweightAt F (ENNReal.ofReal t • (Q₁ : Measure Ω) + ENNReal.ofReal (1 - t) • (Q₂ : Measure Ω)) a =
      ENNReal.ofReal t • reweightAt F (Q₁ : Measure Ω) a +
        ENNReal.ofReal (1 - t) • reweightAt F (Q₂ : Measure Ω) a :=
  sorry

/-- Non-vacuity of the hypotheses of Theorem 5.1: for every `s ≥ 1` they hold
for the compact class `K = {δ_x : x ∈ [0, 1]}` of laws on `Ω = ℝ`, the
parameter space `𝔸 = [0, 1]`, and the contract `(A_a(ω), B_a(ω)) = (1 + a, sin ω)`. -/
theorem jointSetting_example {s : ℝ} (hs : 1 ≤ s) :
    JointSetting (fun (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) => (1 + (a : ℝ), Real.sin ω))
      (diracProba '' Set.Icc (0 : ℝ) 1) s :=
  sorry

end JointContinuity

/-! ## Section 6.1 — the change-of-numéraire involution -/

section Involution

/-- The hypotheses of Corollary 6.1: `μ_n → μ` weakly as probability laws on
`(0, ∞)`, `{X_n}` uniformly integrable, and `m(μ) > 0`.  Weak convergence is
stated on `ℝ`; because the limit also lives on `(0, ∞)`, this is the same as
weak convergence on `(0, ∞)`. -/
structure InvolutionSetting (μ : ℕ → Measure ℝ) (μlim : Measure ℝ) : Prop where
  prob : ∀ n, IsProbabilityMeasure (μ n)
  prob_lim : IsProbabilityMeasure μlim
  pos : ∀ n, μ n (Set.Iic 0) = 0
  pos_lim : μlim (Set.Iic 0) = 0
  weak : WeakConv μ μlim
  ui : UnifIntegrableReal μ fun x => ENNReal.ofReal x
  mean_pos : 0 < ∫ x, x ∂μlim

/-- §6.1, eq. (11).  For a probability law `μ` on `(0, ∞)` with mean
`m(μ) ∈ (0, ∞)` and `s ≥ 1`: `S(μ)` is a law on `(0, ∞)` and
`∫ y^s dS(μ) = E_μ[X^{1-s}] / m(μ)` (on `(0, ∞)`, `y^s = |y|^s`). -/
theorem involution_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : μ (Set.Iic 0) = 0) (hm : 0 < ∫ x, x ∂μ) {s : ℝ} (hs : 1 ≤ s) :
    involution μ (Set.Iic 0) = 0 ∧
    ∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂(involution μ) =
      (∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂μ) / ENNReal.ofReal (∫ x, x ∂μ) :=
  sorry

variable {μ : ℕ → Measure ℝ} {μlim : Measure ℝ}

/-- Corollary 6.1 (exact `W_s`-stability of the involution).  Under its
hypotheses and for `s ≥ 1`, `S(μ_n) → S(μ)` weakly, and the following are
equivalent:
(i)   `S(μ), S(μ_n) ∈ 𝒫_s(ℝ)` and `W_s(S(μ_n), S(μ)) → 0`;
(ii)  every `E_{μ_n}[X_n^{1-s}]` and `E_μ[X^{1-s}]` is finite, and
      `E_{μ_n}[X_n^{1-s}] → E_μ[X^{1-s}]`;
(iii) `{X_n^{1-s}}` is uniformly integrable;
(iv)  `lim_{R → ∞} sup_n E_{μ_n}[X_n^{1-s} ; X_n < 1/R] = 0`. -/
theorem involution_stability (h : InvolutionSetting μ μlim) {s : ℝ} (hs : 1 ≤ s) :
    WeakConv (fun n => involution (μ n)) (involution μlim) ∧
    List.TFAE
      [ HasFiniteMoment s (involution μlim) ∧ (∀ n, HasFiniteMoment s (involution (μ n))) ∧
          Tendsto (fun n => wasserstein s (involution (μ n)) (involution μlim)) atTop (𝓝 0),
        (∀ n, ∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂(μ n) < ∞) ∧
          ∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂μlim < ∞ ∧
          Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂(μ n)) atTop
            (𝓝 (∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂μlim)),
        UnifIntegrableReal μ fun x => ENNReal.ofReal (x ^ (1 - s)),
        Tendsto (fun R : ℝ => ⨆ n, ∫⁻ x in {x | x < 1 / R}, ENNReal.ofReal (x ^ (1 - s)) ∂(μ n))
          atTop (𝓝 0) ] :=
  sorry

/-- Corollary 6.1, last sentence: at `s = 1` the conditions are automatic, so
`W_1`-stability needs no assumption beyond the standing ones. -/
theorem involution_w1 (h : InvolutionSetting μ μlim) :
    HasFiniteMoment 1 (involution μlim) ∧ (∀ n, HasFiniteMoment 1 (involution (μ n))) ∧
      Tendsto (fun n => wasserstein 1 (involution (μ n)) (involution μlim)) atTop (𝓝 0) :=
  sorry

/-- §6.1, first consequence (static part): for a probability law `ν` on
`(0, ∞)` with mean in `(0, ∞)`, `S(ν)` has a finite second moment (the
standing assumption of Beiglböck–Pammer–Riess) iff `E_ν[X^{-1}] < ∞`. -/
theorem involution_second_moment_iff (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : ν (Set.Iic 0) = 0) (hm : 0 < ∫ x, x ∂ν) :
    HasFiniteMoment 2 (involution ν) ↔ ∫⁻ x, ENNReal.ofReal x⁻¹ ∂ν < ∞ :=
  sorry

/-- §6.1, first consequence (stability part): along probability laws on
`(0, ∞)` that converge weakly and whose means converge to `m(μ) > 0` (each
mean finite), `S(μ_n) → S(μ)` in `W_2` (with finite second moments) iff the
inverse moments are finite and `E[X_n^{-1}] → E[X^{-1}]`, iff `{X_n^{-1}}` is
uniformly integrable. -/
theorem involution_w2_iff (hprob : ∀ n, IsProbabilityMeasure (μ n))
    [IsProbabilityMeasure μlim] (hpos : ∀ n, μ n (Set.Iic 0) = 0)
    (hpos_lim : μlim (Set.Iic 0) = 0) (hweak : WeakConv μ μlim)
    (hfin : ∀ n, ∫⁻ x, ENNReal.ofReal x ∂(μ n) < ∞)
    (hmean : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal x ∂(μ n)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal x ∂μlim)))
    (hm : 0 < ∫ x, x ∂μlim) :
    List.TFAE
      [ HasFiniteMoment 2 (involution μlim) ∧ (∀ n, HasFiniteMoment 2 (involution (μ n))) ∧
          Tendsto (fun n => wasserstein 2 (involution (μ n)) (involution μlim)) atTop (𝓝 0),
        (∀ n, ∫⁻ x, ENNReal.ofReal x⁻¹ ∂(μ n) < ∞) ∧ ∫⁻ x, ENNReal.ofReal x⁻¹ ∂μlim < ∞ ∧
          Tendsto (fun n => ∫⁻ x, ENNReal.ofReal x⁻¹ ∂(μ n)) atTop
            (𝓝 (∫⁻ x, ENNReal.ofReal x⁻¹ ∂μlim)),
        UnifIntegrableReal μ fun x => ENNReal.ofReal x⁻¹ ] :=
  sorry

/-- §6.1: the two-atom laws with mass `1 - ε_n` at `1` and `ε_n` at
`a_n = ε_n` satisfy the hypotheses of Corollary 6.1 with limit `δ_1`;
`S(δ_1) = δ_1`; and their transforms converge in `W_σ` for `1 ≤ σ < 2` but
not in `W_2` — the same exact `W_2` threshold as Example 4.1 with `s = 2`. -/
theorem involution_two_atom {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    InvolutionSetting (fun n => exInvolutionTwoAtom (ε n)) (Measure.dirac 1) ∧
    involution (Measure.dirac 1) = Measure.dirac 1 ∧
    (∀ σ, 1 ≤ σ → σ < 2 →
      Tendsto (fun n => wasserstein σ (involution (exInvolutionTwoAtom (ε n))) (Measure.dirac 1))
        atTop (𝓝 0)) ∧
    ¬ Tendsto (fun n => wasserstein 2 (involution (exInvolutionTwoAtom (ε n))) (Measure.dirac 1))
        atTop (𝓝 0) :=
  sorry

end Involution

/-! ## Section 6.2 — annuity-measure swap-rate marginals -/

section Annuity

variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {𝔸 : Type*} [MetricSpace 𝔸] [CompactSpace 𝔸]

/-- §6.2, opening: a common bound on the annuities makes them uniformly
integrable. -/
theorem unifIntegrableOn_of_bounded {ι : Type*} (L : ι → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (L i)] (C : ℝ) (hC : ∀ i, ∀ᵐ p ∂(L i), p.1 ≤ C) :
    UnifIntegrableOn L fun p => ENNReal.ofReal p.1 :=
  sorry

/-- The hypotheses of §6.2, item 1: the compact model–contract setting and joint
continuity of Theorem 5.1 (`K` compact, `𝔸` compact metric, `(a, ω) ↦
(A_a(ω), B_a(ω))` jointly continuous into `(0, ∞) × ℝ`, so no law charges
`{A_a = 0}`); uniform integrability over the class of the annuities `A_a` and
of the floating legs `B_a`; and positive normalization `inf E_Q[A_a] > 0`.
No moment condition on `1/A_a` is imposed. -/
structure AnnuitySetting (F : 𝔸 → Ω → ℝ × ℝ) (K : Set (ProbabilityMeasure Ω)) : Prop where
  compact : IsCompact K
  cont : Continuous fun x : 𝔸 × Ω => F x.1 x.2
  pos : ∀ a ω, 0 < (F a ω).1
  ui : UnifIntegrableOn (fun x : K × 𝔸 => contractLaw F (x.1 : Measure Ω) x.2)
    fun p => ENNReal.ofReal p.1
  ui_leg : UnifIntegrableOn (fun x : K × 𝔸 => contractLaw F (x.1 : Measure Ω) x.2)
    fun p => ENNReal.ofReal |p.2|
  mean_pos : ∃ c : ℝ, 0 < c ∧
    ∀ x : K × 𝔸, c ≤ numeraireMean (contractLaw F (x.1 : Measure Ω) x.2)

variable {F : 𝔸 → Ω → ℝ × ℝ} {K : Set (ProbabilityMeasure Ω)}

/-- §6.2, item 1: the hypotheses supply the uniform ratio-tail condition (10)
at `s = 1`, so the setting of Theorem 5.1 holds at `s = 1`. -/
theorem annuity_ratioTail (h : AnnuitySetting F K) :
    Tendsto (ratioTailOn 1 fun x : K × 𝔸 => contractLaw F (x.1 : Measure Ω) x.2)
      atTop (𝓝 0) :=
  sorry

/-- §6.2, item 1: joint `W_1`-continuity of the annuity-measure marginals on
`K × 𝔸`, with no moment assumption on `1/A_a`. -/
theorem annuity_w1_continuity (h : AnnuitySetting F K) :
    ∀ x ∈ K ×ˢ (Set.univ : Set 𝔸),
      Tendsto (fun y : ProbabilityMeasure Ω × 𝔸 =>
          wasserstein 1 (reweightAt F (y.1 : Measure Ω) y.2)
            (reweightAt F (x.1 : Measure Ω) x.2))
        (𝓝[K ×ˢ Set.univ] x) (𝓝 0) :=
  sorry

/-- §6.2, item 1: the normalized call-price curves converge uniformly in the
strike as `(Q, a) → x` within `K × 𝔸`. -/
theorem annuity_calls_uniform (h : AnnuitySetting F K) (x : ProbabilityMeasure Ω × 𝔸)
    (hx : x ∈ K ×ˢ (Set.univ : Set 𝔸)) :
    TendstoUniformly (fun (y : ProbabilityMeasure Ω × 𝔸) (k : ℝ) =>
        normCall (reweightAt F (y.1 : Measure Ω) y.2) k)
      (fun k => normCall (reweightAt F (x.1 : Measure Ω) x.2) k) (𝓝[K ×ˢ Set.univ] x) :=
  sorry

/-- §6.2, item 1: the physically settled swaption prices `E_Q[(B_a - k A_a)⁺]`
converge at each fixed strike, uniformly over bounded sets of strikes. -/
theorem annuity_prices_uniform (h : AnnuitySetting F K) (x : ProbabilityMeasure Ω × 𝔸)
    (hx : x ∈ K ×ˢ (Set.univ : Set 𝔸)) (k₀ : ℝ) :
    TendstoUniformlyOn (fun (y : ProbabilityMeasure Ω × 𝔸) (k : ℝ) =>
        payerPrice F (y.1 : Measure Ω) y.2 k)
      (fun k => payerPrice F (x.1 : Measure Ω) x.2 k) (𝓝[K ×ˢ Set.univ] x)
      (Set.Icc (-k₀) k₀) :=
  sorry

/-- §6.2, item 2: the raw second moment is
`∫ z² dΓ_a(Q) = E_Q[B_a² / A_a] / E_Q[A_a]`. -/
theorem annuity_second_moment (h : AnnuitySetting F K) {Q : ProbabilityMeasure Ω}
    (hQ : Q ∈ K) (a : 𝔸) :
    ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F (Q : Measure Ω) a) =
      (∫⁻ ω, ENNReal.ofReal ((F a ω).2 ^ 2 / (F a ω).1) ∂(Q : Measure Ω)) /
        ENNReal.ofReal (numeraireMean (contractLaw F (Q : Measure Ω) a)) :=
  sorry

/-- §6.2, item 2: in the boundary-free setting, stability of the raw second
moment along `(Q_n, a_n) → (Q, a)` in `K × 𝔸` (finite second moments that
converge) is equivalent to uniform integrability of `{B_{a_n}² / A_{a_n}}`. -/
theorem annuity_second_moment_stability (h : AnnuitySetting F K)
    (y : ℕ → ProbabilityMeasure Ω × 𝔸) (x : ProbabilityMeasure Ω × 𝔸)
    (hy : ∀ n, (y n).1 ∈ K) (hx : x.1 ∈ K) (hlim : Tendsto y atTop (𝓝 x)) :
    ((∀ n, ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F ((y n).1 : Measure Ω) (y n).2) < ∞) ∧
        ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F (x.1 : Measure Ω) x.2) < ∞ ∧
        Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F ((y n).1 : Measure Ω) (y n).2))
          atTop (𝓝 (∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F (x.1 : Measure Ω) x.2)))) ↔
      UnifIntegrableFamily (fun n => contractLaw F ((y n).1 : Measure Ω) (y n).2)
        fun p => ENNReal.ofReal (p.2 ^ 2 / p.1) :=
  sorry

/-- §6.2, item 2, in the abstract model of Example 4.1 with `s = 2`: the whole
normalized call-price curve converges (uniformly in the strike) to that of the
limit `Γ = δ_0`, while the raw second moment tends to `1` and that of `δ_0`
is `0`. -/
theorem example_4_1_calls_second_moment {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly (fun (n : ℕ) (k : ℝ) => normCall (reweight (exTwoAtom 2 (ε n))) k)
      (fun k => normCall (Measure.dirac 0) k) atTop ∧
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweight (exTwoAtom 2 (ε n)))) atTop (𝓝 1) ∧
    ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(Measure.dirac (0 : ℝ)) = 0 :=
  sorry

/-- Non-vacuity of the hypotheses of §6.2, item 1: they hold for the class
`K = {δ_x : x ∈ [0, 1]}` on `Ω = ℝ`, `𝔸 = [0, 1]`, and the contract
`(A_a(ω), B_a(ω)) = (1 + a, sin ω)`. -/
theorem annuitySetting_example :
    AnnuitySetting (fun (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) => (1 + (a : ℝ), Real.sin ω))
      (diracProba '' Set.Icc (0 : ℝ) 1) :=
  sorry

end Annuity

/-- §6.2, item 3 (cash settlement).  For a law `ρ` of `S` and `G > 0` with
`E[G(S)] ∈ (0, ∞)`, set `A = G(S)` and `B = S G(S)`.  Then
`A (B/A - K)⁺ = G(S)(S - K)⁺`; the reweighting of the law of `(A, B)` is the
normalized `G`-weighted law of `S`, `G(S)/E[G(S)] · ρ`; and Proposition 2.1
gives its call prices `E[G(S)(S - K)⁺] / E[G(S)]`. -/
theorem cash_settled (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (G : ℝ → ℝ)
    (hG : Measurable G) (hGpos : ∀ x, 0 < G x) (hGint : Integrable G ρ) (K : ℝ) :
    (∀ x, G x * max ((x * G x) / G x - K) 0 = G x * max (x - K) 0) ∧
    reweight (ρ.map fun x => (G x, x * G x)) =
      ρ.withDensity (fun x => ENNReal.ofReal (G x / ∫ y, G y ∂ρ)) ∧
    ∫⁻ z, ENNReal.ofReal (max (z - K) 0) ∂(reweight (ρ.map fun x => (G x, x * G x))) =
      (∫⁻ x, ENNReal.ofReal (G x * max (x - K) 0) ∂ρ) / ENNReal.ofReal (∫ y, G y ∂ρ) :=
  sorry

end NumeraireStability
