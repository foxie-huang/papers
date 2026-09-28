/-
# Stability of Change-of-Numéraire Reweighting — Lean formalization

Formal statements and machine-checked proofs of the core results of

  S. Huang, "Stability of Change-of-Numéraire Reweighting: An Exact
  Wasserstein Boundary" (2026):

Proposition 2.1, the boundary-permitting limit identity of §3.1, Lemma 3.1,
Theorem 3.3, Corollary 3.4 and the sharpness Examples 4.1, 4.3 and 4.4
(Sections 2–4); and Theorem 5.1, eq. (11), Corollary 6.1 and the
consequences drawn in §6.1–§6.2 (Sections 5–6).

The statements below are exactly those reviewed in step 1 (kept verbatim in
`spec/Statements_step1.lean` for Sections 2–4 and `spec/Statements56_step1.lean`
for Sections 5–6); the proofs live in `NumeraireStability/`.
Every theorem depends only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); `lake env lean AxiomCheck.lean` prints them.

Conventions.  A law of `(A, B)` is a measure `Q` on `ℝ × ℝ`; `p.1` is the
numéraire coordinate `a` and `p.2` the payoff coordinate `b`.  Lean's
division convention `b / 0 = 0` is exactly the paper's `T(0, b) := 0`.
-/
import NumeraireStability.Defs
import NumeraireStability.Cancellation
import NumeraireStability.Stability
import NumeraireStability.Boundary
import NumeraireStability.Corollary
import NumeraireStability.Example41
import NumeraireStability.Example43_44
import NumeraireStability.JointContinuity
import NumeraireStability.Involution
import NumeraireStability.Annuity

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-! ## Section 2 — Proposition 2.1 (perspective cancellation) -/

section Cancellation

variable (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]

/-- `Γ(Q)` is a probability measure (paper, §2 and §3.1). -/
theorem reweight_isProbabilityMeasure (hsupp : P {p | p.1 < 0} = 0)
    (hm : 0 < numeraireMean P) :
    IsProbabilityMeasure (reweight P) :=
  isProbabilityMeasure_reweight P hsupp hm

/-- Proposition 2.1, general identity: `∫ f dΓ = E_Q[A f(B/A)] / A⁰` for every
measurable `f ≥ 0`, as an identity in `[0, ∞]`. -/
theorem cancellation_general (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(reweight P) =
      (∫⁻ p, ENNReal.ofReal p.1 * f (p.2 / p.1) ∂P) /
        ENNReal.ofReal (numeraireMean P) :=
  lintegral_reweight P hm f hf

/-- Proposition 2.1, call identity: `∫ (z - K)⁺ dΓ = E_Q[(B - K A)⁺] / A⁰`. -/
theorem cancellation_call (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (K : ℝ) :
    ∫⁻ z, ENNReal.ofReal (max (z - K) 0) ∂(reweight P) =
      (∫⁻ p, ENNReal.ofReal (max (p.2 - K * p.1) 0) ∂P) /
        ENNReal.ofReal (numeraireMean P) := by
  rw [lintegral_reweight P hm _ (by fun_prop)]
  congr 1
  refine lintegral_congr_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
  have h : p.1 * max (p.2 / p.1 - K) 0 = max (p.2 - K * p.1) 0 := by
    rw [mul_max_of_nonneg _ _ hp.le, mul_zero]
    congr 1
    field_simp
  dsimp only
  rw [← ENNReal.ofReal_mul hp.le, h]

/-- Proposition 2.1, first moment: `∫ |z| dΓ = E_Q|B| / A⁰`. -/
theorem cancellation_first_moment (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) :
    ∫⁻ z, ENNReal.ofReal |z| ∂(reweight P) =
      (∫⁻ p, ENNReal.ofReal |p.2| ∂P) / ENNReal.ofReal (numeraireMean P) := by
  rw [lintegral_reweight P hm _ (by fun_prop)]
  congr 1
  refine lintegral_congr_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
  have h : p.1 * |p.2 / p.1| = |p.2| := by
    rw [abs_div, abs_of_pos hp]
    field_simp
  dsimp only
  rw [← ENNReal.ofReal_mul hp.le, h]

/-- Proposition 2.1, `s`-th moment for `s > 1`:
`∫ |z|^s dΓ = E_Q[|B|^s A^{1-s}] / A⁰`. -/
theorem cancellation_moment (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) {s : ℝ} (hs : 1 < s) :
    ∫⁻ z, ENNReal.ofReal (|z| ^ s) ∂(reweight P) =
      (∫⁻ p, boundaryFamily s p ∂P) / ENNReal.ofReal (numeraireMean P) := by
  rw [lintegral_reweight P hm _ (by fun_prop)]
  congr 1
  refine lintegral_congr_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
  have hps : 0 < p.1 ^ s := Real.rpow_pos_of_pos hp s
  have h : p.1 * |p.2 / p.1| ^ s = |p.2| ^ s * p.1 ^ (1 - s) := by
    rw [abs_div, abs_of_pos hp, Real.div_rpow (abs_nonneg _) hp.le, Real.rpow_sub hp,
      Real.rpow_one]
    field_simp
  dsimp only
  rw [boundaryFamily, ← ENNReal.ofReal_mul hp.le, h]

/-- Proposition 2.1, "in particular": the first moment is finite whenever
`E_Q|B| < ∞`, with no condition on `1/A`. -/
theorem hasFiniteMoment_one_of_integrable (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (hB : ∫⁻ p, ENNReal.ofReal |p.2| ∂P < ∞) :
    HasFiniteMoment 1 (reweight P) := by
  unfold HasFiniteMoment
  simp only [Real.rpow_one]
  rw [cancellation_first_moment P hpos hm]
  exact ENNReal.div_lt_top hB.ne (ENNReal.ofReal_pos.2 hm).ne'

/-- Proposition 2.1, "in particular": for `s > 1` the `s`-moment is finite
exactly when `E_Q[|B|^s A^{1-s}] < ∞`. -/
theorem hasFiniteMoment_iff (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) {s : ℝ} (hs : 1 < s) :
    HasFiniteMoment s (reweight P) ↔ ∫⁻ p, boundaryFamily s p ∂P < ∞ := by
  unfold HasFiniteMoment
  rw [cancellation_moment P hpos hm hs]
  constructor
  · intro h
    by_contra hW
    rw [not_lt, top_le_iff] at hW
    rw [hW, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h
    exact lt_irrefl _ h
  · intro h
    exact ENNReal.div_lt_top h.ne (ENNReal.ofReal_pos.2 hm).ne'

/-- §3.1, the boundary-permitting limit object: when `Q` may charge
`{a = 0}`, `∫ f dΓ = m⁻¹ ∫_{a > 0} a f(b/a) dQ` for every Borel `f ≥ 0`.
This identifies `reweight` with the paper's limit `Γ`. -/
theorem reweight_lintegral_boundary (hsupp : P {p | p.1 < 0} = 0)
    (hm : 0 < numeraireMean P) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(reweight P) =
      (∫⁻ p in {p | 0 < p.1}, ENNReal.ofReal p.1 * f (p.2 / p.1) ∂P) /
        ENNReal.ofReal (numeraireMean P) :=
  lintegral_reweight_pos P hm f hf

end Cancellation

/-! ## Section 3 — the two-way stability theorem -/

section Stability

variable {Q : ℕ → Measure (ℝ × ℝ)} {Qlim : Measure (ℝ × ℝ)}

/-- §3.1: "Under (S1)–(S2), `E[A_n] → m`." -/
theorem mean_tendsto (h : StandingSetting Q Qlim) :
    Tendsto (fun n => numeraireMean (Q n)) atTop (𝓝 (numeraireMean Qlim)) :=
  h.tendsto_mean

/-- Lemma 3.1 (weak stability under numéraire uniform integrability):
under (S1)–(S2), `Γ_n → Γ` weakly. -/
theorem weak_stability (h : StandingSetting Q Qlim) :
    WeakConv (fun n => reweight (Q n)) (reweight Qlim) :=
  h.weakConv_reweight

/-- Theorem 3.3 (exact two-way `W_s` boundary).  Assume (S1)–(S2) and fix
`s ≥ 1`.  The following are equivalent:
(i)   `Γ ∈ 𝒫_s(ℝ)`, `Γ_n ∈ 𝒫_s(ℝ)` for every `n`, and `W_s(Γ_n, Γ) → 0`;
(ii)  `W_n` is integrable for every `n`, `I_s < ∞`, and `E[W_n] → I_s`;
(iii) `lim_{R → ∞} sup_n E[W_n ; |B_n| > R A_n] = 0`. -/
theorem exact_two_way_boundary (h : StandingSetting Q Qlim) {s : ℝ} (hs : 1 ≤ s) :
    List.TFAE
      [ HasFiniteMoment s (reweight Qlim) ∧ (∀ n, HasFiniteMoment s (reweight (Q n))) ∧
          Tendsto (fun n => wasserstein s (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0),
        (∀ n, ∫⁻ p, boundaryFamily s p ∂(Q n) < ∞) ∧ boundaryIntegral s Qlim < ∞ ∧
          Tendsto (fun n => ∫⁻ p, boundaryFamily s p ∂(Q n)) atTop
            (𝓝 (boundaryIntegral s Qlim)),
        Tendsto (ratioTail s Q) atTop (𝓝 0) ] :=
  h.exact_two_way hs

/-- Corollary 3.4(a).  If `{|B_n|}` is uniformly integrable, then
`Γ, Γ_n ∈ 𝒫_1(ℝ)`, and `W_1(Γ_n, Γ) → 0` iff `∫_{a = 0} |b| dQ = 0`. -/
theorem sharp_cancellation (h : StandingSetting Q Qlim)
    (hB : UnifIntegrableFamily Q fun p => ENNReal.ofReal |p.2|) :
    HasFiniteMoment 1 (reweight Qlim) ∧ (∀ n, HasFiniteMoment 1 (reweight (Q n))) ∧
      (Tendsto (fun n => wasserstein 1 (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0) ↔
        ∫⁻ p in {p | p.1 = 0}, ENNReal.ofReal |p.2| ∂Qlim = 0) :=
  h.sharp_cancellation' hB

/-- Corollary 3.4(a), "in particular": if `Q({a = 0}) = 0`, then
`W_1(Γ_n, Γ) → 0`, with no hypothesis on `{1/A_n}`. -/
theorem sharp_cancellation_of_no_boundary (h : StandingSetting Q Qlim)
    (hB : UnifIntegrableFamily Q fun p => ENNReal.ofReal |p.2|)
    (h0 : Qlim {p | p.1 = 0} = 0) :
    Tendsto (fun n => wasserstein 1 (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0) :=
  h.sharp_cancellation_of_no_boundary' hB h0

/-- Corollary 3.4(b).  If `Q({a = 0}) = 0` and `s ≥ 1`, then
`Γ, Γ_n ∈ 𝒫_s(ℝ)` with `W_s(Γ_n, Γ) → 0` iff `{W_n}` is uniformly integrable. -/
theorem boundary_free_iff_unifIntegrable (h : StandingSetting Q Qlim)
    (h0 : Qlim {p | p.1 = 0} = 0) {s : ℝ} (hs : 1 ≤ s) :
    (HasFiniteMoment s (reweight Qlim) ∧ (∀ n, HasFiniteMoment s (reweight (Q n))) ∧
        Tendsto (fun n => wasserstein s (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0)) ↔
      UnifIntegrableFamily Q (boundaryFamily s) :=
  h.boundary_free_iff h0 hs

end Stability

/-! ## Section 4 — sharpness -/

section Sharpness

/-- Example 4.1: `E[A_n] = 1 - ε_n + ε_n a_n`. -/
theorem exTwoAtom_mean {s ε : ℝ} (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    numeraireMean (exTwoAtom s ε) = 1 - ε + ε * ε ^ (1 / (s - 1)) :=
  exTwoAtom_mean' hs hε

/-- Example 4.1: `Γ_n` has an atom at `0` of mass `(1 - ε_n)/E[A_n]` and an
atom at `1/a_n` of mass `ε_n a_n / E[A_n]`. -/
theorem reweight_exTwoAtom {s ε : ℝ} (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    reweight (exTwoAtom s ε) =
      ENNReal.ofReal ((1 - ε) / numeraireMean (exTwoAtom s ε)) • Measure.dirac 0 +
        ENNReal.ofReal (ε * ε ^ (1 / (s - 1)) / numeraireMean (exTwoAtom s ε)) •
          Measure.dirac (1 / ε ^ (1 / (s - 1))) :=
  reweight_exTwoAtom' hs hε

/-- Example 4.1: for every `σ ≥ 1`,
`∫ |z|^σ dΓ_n = ε_n^{(s-σ)/(s-1)} / E[A_n]`. -/
theorem exTwoAtom_moment {s ε σ : ℝ} (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) (hσ : 1 ≤ σ) :
    ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s ε)) =
      ENNReal.ofReal (ε ^ ((s - σ) / (s - 1)) / numeraireMean (exTwoAtom s ε)) :=
  exTwoAtom_moment' hs hε hσ

/-- Example 4.1 (the boundary is attained: bounded inputs, exact threshold).
Fix `s > 1` and `ε_n → 0` in `(0, 1)`.  Then (S1)–(S2) hold with limit
`Q = δ_{(1,0)}`, which does not charge `{a = 0}`; `Γ = δ_0`; `Γ_n → Γ`
weakly; the `σ`-th moments of `Γ_n` tend to `0`, `1`, `∞` for `σ < s`,
`σ = s`, `σ > s`; `W_σ(Γ_n, Γ) → 0` for `1 ≤ σ < s` but not for `σ = s`;
and `{|B_n|^σ A_n^{1-σ}}` is uniformly integrable for `1 ≤ σ < s` but not
for `σ = s`. -/
theorem example_4_1 {s : ℝ} (hs : 1 < s) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    StandingSetting (fun n => exTwoAtom s (ε n)) (Measure.dirac (1, 0)) ∧
    Measure.dirac ((1 : ℝ), (0 : ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 ∧
    reweight (Measure.dirac ((1 : ℝ), (0 : ℝ))) = Measure.dirac 0 ∧
    WeakConv (fun n => reweight (exTwoAtom s (ε n))) (Measure.dirac 0) ∧
    (∀ σ, 1 ≤ σ → σ < s →
      Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n))))
        atTop (𝓝 0)) ∧
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ s) ∂(reweight (exTwoAtom s (ε n))))
      atTop (𝓝 1) ∧
    (∀ σ, s < σ →
      Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n))))
        atTop (𝓝 ∞)) ∧
    (∀ σ, 1 ≤ σ → σ < s →
      Tendsto (fun n => wasserstein σ (reweight (exTwoAtom s (ε n))) (Measure.dirac 0))
        atTop (𝓝 0)) ∧
    ¬ Tendsto (fun n => wasserstein s (reweight (exTwoAtom s (ε n))) (Measure.dirac 0))
        atTop (𝓝 0) ∧
    (∀ σ, 1 ≤ σ → σ < s →
      UnifIntegrableFamily (fun n => exTwoAtom s (ε n)) (boundaryFamily σ)) ∧
    ¬ UnifIntegrableFamily (fun n => exTwoAtom s (ε n)) (boundaryFamily s) :=
  example_4_1' hs hε hεlim

/-- Example 4.3 (nonzero payoff mass on the vanishing-numéraire boundary
defeats `W_1`-stability).  Fix `ε ∈ (0, 1)` and `α_n → 0` with `α_n > 0`.
Then (S1)–(S2) hold with limit `Q = (1 - ε) δ_{(1,0)} + ε δ_{(0,1)}`, which
charges `{a = 0}`; `m = 1 - ε`; `{|B_n|}` is uniformly integrable;
`Γ = δ_0` and `Γ_n → Γ` weakly; but `∫ |z| dΓ_n → ε/(1 - ε) ≠ 0`, so
`W_1(Γ_n, Γ) ↛ 0`, and the ratio-tail condition (iii) fails at `s = 1`. -/
theorem example_4_3 {ε : ℝ} (hε : 0 < ε ∧ ε < 1) {α : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    (hαlim : Tendsto α atTop (𝓝 0)) :
    StandingSetting (fun n => exBoundaryMass ε (α n)) (exBoundaryMass ε 0) ∧
    exBoundaryMass ε 0 {p : ℝ × ℝ | p.1 = 0} ≠ 0 ∧
    numeraireMean (exBoundaryMass ε 0) = 1 - ε ∧
    UnifIntegrableFamily (fun n => exBoundaryMass ε (α n)) (fun p => ENNReal.ofReal |p.2|) ∧
    reweight (exBoundaryMass ε 0) = Measure.dirac 0 ∧
    WeakConv (fun n => reweight (exBoundaryMass ε (α n))) (Measure.dirac 0) ∧
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal |z| ∂(reweight (exBoundaryMass ε (α n))))
      atTop (𝓝 (ENNReal.ofReal (ε / (1 - ε)))) ∧
    ¬ Tendsto (fun n => wasserstein 1 (reweight (exBoundaryMass ε (α n))) (Measure.dirac 0))
        atTop (𝓝 0) ∧
    ¬ Tendsto (ratioTail 1 fun n => exBoundaryMass ε (α n)) atTop (𝓝 0) :=
  example_4_3' hε hα hαlim

/-- Example 4.4 (numéraire uniform integrability is needed for weak
stability).  With `ε_n → 0` in `(0, 1)`: `Q_n → δ_{(1,0)}` weakly, `{A_n}`
is not uniformly integrable, `E[A_n] → 2`, and `Γ_n → ½ δ_0 + ½ δ_1`
weakly, whereas `Γ = δ_0`: even weak stability fails. -/
theorem example_4_4 {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    WeakConv (fun n => exNoUnifIntegrable (ε n)) (Measure.dirac (1, 0)) ∧
    ¬ UnifIntegrableFamily (fun n => exNoUnifIntegrable (ε n)) (fun p => ENNReal.ofReal p.1) ∧
    Tendsto (fun n => numeraireMean (exNoUnifIntegrable (ε n))) atTop (𝓝 2) ∧
    reweight (Measure.dirac ((1 : ℝ), (0 : ℝ))) = Measure.dirac 0 ∧
    WeakConv (fun n => reweight (exNoUnifIntegrable (ε n)))
      ((2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1) ∧
    ¬ WeakConv (fun n => reweight (exNoUnifIntegrable (ε n))) (Measure.dirac 0) :=
  example_4_4' hε hεlim

end Sharpness

/-! ## Section 5 — Theorem 5.1 -/

section JointContinuity

variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {𝔸 : Type*} [MetricSpace 𝔸] [CompactSpace 𝔸]

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
  h.joint_continuity' hs

/-- Theorem 5.1(ii).  The image `{Γ_a(Q) : (Q, a) ∈ K × 𝔸}` is compact in
`(𝒫_s(ℝ), W_s)`, stated as sequential compactness (equivalent in a metric
space): for every sequence `(Q_n, a_n)` in `K × 𝔸` there are `(Q, a) ∈ K × 𝔸`
and a subsequence along which `W_s(Γ_{a_n}(Q_n), Γ_a(Q)) → 0`. -/
theorem image_compact (h : JointSetting F K s) (hs : 1 ≤ s)
    (y : ℕ → ProbabilityMeasure Ω × 𝔸) (hy : ∀ n, (y n).1 ∈ K) :
    ∃ x ∈ K ×ˢ (Set.univ : Set 𝔸), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => wasserstein s (reweightAt F ((y (φ k)).1 : Measure Ω) (y (φ k)).2)
          (reweightAt F (x.1 : Measure Ω) x.2)) atTop (𝓝 0) :=
  h.image_compact' hs y hy

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
  h.reweightAt_projective' a

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
  h.mixture_formula' h₁ h₂ a ht0 ht1

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
  h.affine_on_slice' h₁ h₂ a hc₁ hc₂ ht0 ht1

/-- Non-vacuity of the hypotheses of Theorem 5.1: for every `s ≥ 1` they hold
for the compact class `K = {δ_x : x ∈ [0, 1]}` of laws on `Ω = ℝ`, the
parameter space `𝔸 = [0, 1]`, and the contract `(A_a(ω), B_a(ω)) = (1 + a, sin ω)`. -/
theorem jointSetting_example {s : ℝ} (hs : 1 ≤ s) :
    JointSetting (fun (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) => (1 + (a : ℝ), Real.sin ω))
      (diracProba '' Set.Icc (0 : ℝ) 1) s :=
  jointSetting_example'

end JointContinuity

/-! ## Section 6.1 — the change-of-numéraire involution -/

section Involution

/-- §6.1, eq. (11).  For a probability law `μ` on `(0, ∞)` with mean
`m(μ) ∈ (0, ∞)` and `s ≥ 1`: `S(μ)` is a law on `(0, ∞)` and
`∫ y^s dS(μ) = E_μ[X^{1-s}] / m(μ)` (on `(0, ∞)`, `y^s = |y|^s`). -/
theorem involution_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : μ (Set.Iic 0) = 0) (hm : 0 < ∫ x, x ∂μ) {s : ℝ} (hs : 1 ≤ s) :
    involution μ (Set.Iic 0) = 0 ∧
    ∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂(involution μ) =
      (∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂μ) / ENNReal.ofReal (∫ x, x ∂μ) :=
  involution_moment' μ hpos hm

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
  h.stability hs

/-- Corollary 6.1, last sentence: at `s = 1` the conditions are automatic, so
`W_1`-stability needs no assumption beyond the standing ones. -/
theorem involution_w1 (h : InvolutionSetting μ μlim) :
    HasFiniteMoment 1 (involution μlim) ∧ (∀ n, HasFiniteMoment 1 (involution (μ n))) ∧
      Tendsto (fun n => wasserstein 1 (involution (μ n)) (involution μlim)) atTop (𝓝 0) :=
  h.w1

/-- §6.1, first consequence (static part): for a probability law `ν` on
`(0, ∞)` with mean in `(0, ∞)`, `S(ν)` has a finite second moment (the
standing assumption of Beiglböck–Pammer–Riess) iff `E_ν[X^{-1}] < ∞`. -/
theorem involution_second_moment_iff (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : ν (Set.Iic 0) = 0) (hm : 0 < ∫ x, x ∂ν) :
    HasFiniteMoment 2 (involution ν) ↔ ∫⁻ x, ENNReal.ofReal x⁻¹ ∂ν < ∞ :=
  involution_second_moment_iff' ν hpos hm

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
  involution_w2_iff' hprob hpos hpos_lim hweak hfin hmean hm

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
  involution_two_atom' hε hεlim

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
  unifIntegrableOn_of_bounded' L C hC

variable {F : 𝔸 → Ω → ℝ × ℝ} {K : Set (ProbabilityMeasure Ω)}

/-- §6.2, item 1: the hypotheses supply the uniform ratio-tail condition (10)
at `s = 1`, so the setting of Theorem 5.1 holds at `s = 1`. -/
theorem annuity_ratioTail (h : AnnuitySetting F K) :
    Tendsto (ratioTailOn 1 fun x : K × 𝔸 => contractLaw F (x.1 : Measure Ω) x.2)
      atTop (𝓝 0) :=
  h.ratioTail'

/-- §6.2, item 1: joint `W_1`-continuity of the annuity-measure marginals on
`K × 𝔸`, with no moment assumption on `1/A_a`. -/
theorem annuity_w1_continuity (h : AnnuitySetting F K) :
    ∀ x ∈ K ×ˢ (Set.univ : Set 𝔸),
      Tendsto (fun y : ProbabilityMeasure Ω × 𝔸 =>
          wasserstein 1 (reweightAt F (y.1 : Measure Ω) y.2)
            (reweightAt F (x.1 : Measure Ω) x.2))
        (𝓝[K ×ˢ Set.univ] x) (𝓝 0) :=
  h.w1_continuity'

/-- §6.2, item 1: the normalized call-price curves converge uniformly in the
strike as `(Q, a) → x` within `K × 𝔸`. -/
theorem annuity_calls_uniform (h : AnnuitySetting F K) (x : ProbabilityMeasure Ω × 𝔸)
    (hx : x ∈ K ×ˢ (Set.univ : Set 𝔸)) :
    TendstoUniformly (fun (y : ProbabilityMeasure Ω × 𝔸) (k : ℝ) =>
        normCall (reweightAt F (y.1 : Measure Ω) y.2) k)
      (fun k => normCall (reweightAt F (x.1 : Measure Ω) x.2) k) (𝓝[K ×ˢ Set.univ] x) :=
  h.calls_uniform' x hx

/-- §6.2, item 1: the physically settled swaption prices `E_Q[(B_a - k A_a)⁺]`
converge at each fixed strike, uniformly over bounded sets of strikes. -/
theorem annuity_prices_uniform (h : AnnuitySetting F K) (x : ProbabilityMeasure Ω × 𝔸)
    (hx : x ∈ K ×ˢ (Set.univ : Set 𝔸)) (k₀ : ℝ) :
    TendstoUniformlyOn (fun (y : ProbabilityMeasure Ω × 𝔸) (k : ℝ) =>
        payerPrice F (y.1 : Measure Ω) y.2 k)
      (fun k => payerPrice F (x.1 : Measure Ω) x.2 k) (𝓝[K ×ˢ Set.univ] x)
      (Set.Icc (-k₀) k₀) :=
  h.prices_uniform' x hx k₀

/-- §6.2, item 2: the raw second moment is
`∫ z² dΓ_a(Q) = E_Q[B_a² / A_a] / E_Q[A_a]`. -/
theorem annuity_second_moment (h : AnnuitySetting F K) {Q : ProbabilityMeasure Ω}
    (hQ : Q ∈ K) (a : 𝔸) :
    ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F (Q : Measure Ω) a) =
      (∫⁻ ω, ENNReal.ofReal ((F a ω).2 ^ 2 / (F a ω).1) ∂(Q : Measure Ω)) /
        ENNReal.ofReal (numeraireMean (contractLaw F (Q : Measure Ω) a)) :=
  h.second_moment' hQ a

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
  h.second_moment_stability' y x hy hx hlim

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
  example_4_1_calls_second_moment' hε hεlim

/-- Non-vacuity of the hypotheses of §6.2, item 1: they hold for the class
`K = {δ_x : x ∈ [0, 1]}` on `Ω = ℝ`, `𝔸 = [0, 1]`, and the contract
`(A_a(ω), B_a(ω)) = (1 + a, sin ω)`. -/
theorem annuitySetting_example :
    AnnuitySetting (fun (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) => (1 + (a : ℝ), Real.sin ω))
      (diracProba '' Set.Icc (0 : ℝ) 1) :=
  annuitySetting_example'

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
  cash_settled' ρ G hG hGpos hGint K

end NumeraireStability
