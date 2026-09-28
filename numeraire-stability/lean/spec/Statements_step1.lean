/-
# Stability of Change-of-Numéraire Reweighting — Lean statements (step 1)

Formal statements of the core results of

  S. Huang, "Stability of Change-of-Numéraire Reweighting: An Exact
  Wasserstein Boundary" (2026),

Proposition 2.1, the boundary-permitting limit identity of §3.1, Lemma 3.1,
Theorem 3.3, Corollary 3.4 and the sharpness Examples 4.1, 4.3 and 4.4.

Every proof is `sorry`.  This file exists to be REVIEWED: each statement
must say what the paper says.  `README.md` lists the correspondence and
the modelling choices to check.

Conventions.  A law of `(A, B)` is a measure `Q` on `ℝ × ℝ`; `p.1` is the
numéraire coordinate `a` and `p.2` the payoff coordinate `b`.  Lean's
division convention `b / 0 = 0` is exactly the paper's `T(0, b) := 0`.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.List.TFAE

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-! ## Definitions -/

/-- Weak convergence of measures: the integral of every bounded continuous
function converges. -/
def WeakConv {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) (ν : Measure X) : Prop :=
  ∀ f : X →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

/-- Uniform integrability of the random variables `g(A_n, B_n)`, where
`(A_n, B_n)` has law `Q n`:
`lim_{M → ∞} sup_n E_{Q n}[g ; g > M] = 0`. -/
def UnifIntegrableFamily (Q : ℕ → Measure (ℝ × ℝ)) (g : ℝ × ℝ → ℝ≥0∞) : Prop :=
  Tendsto (fun M : ℝ => ⨆ n, ∫⁻ p in {p | ENNReal.ofReal M < g p}, g p ∂(Q n))
    atTop (𝓝 0)

/-- Finite `s`-th moment; for a probability measure this is membership of
`𝒫_s(ℝ)`. -/
def HasFiniteMoment (s : ℝ) (μ : Measure ℝ) : Prop :=
  ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂μ < ∞

/-- `π` is a coupling of `μ` and `ν`. -/
def IsCoupling (π : Measure (ℝ × ℝ)) (μ ν : Measure ℝ) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = ν

/-- The `s`-Wasserstein distance on `ℝ` (used for `s ≥ 1`), valued in
`[0, ∞]`:  `W_s(μ, ν) = (inf_π ∫ |x - y|^s dπ)^{1/s}` over couplings `π`. -/
def wasserstein (s : ℝ) (μ ν : Measure ℝ) : ℝ≥0∞ :=
  (⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling π μ ν),
      ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| ^ s) ∂π) ^ (1 / s)

/-- The numéraire mean `E_Q[A] = ∫ a dQ`.  (Bochner integral: it is `0` when
`A` is not integrable, so a hypothesis `0 < numeraireMean Q` also asserts
`E_Q[A] ∈ (0, ∞)`.) -/
def numeraireMean (Q : Measure (ℝ × ℝ)) : ℝ :=
  ∫ p, p.1 ∂Q

/-- The change-of-numéraire reweighting `Γ(Q) := Z_#(D dQ)` with
`D = A / E_Q[A]` and `Z = B / A` (paper, §1).

The same definition is the paper's boundary-permitting limit object (§3.1),
`Γ := T_#μ` with `μ = (a/m) 1{a > 0} Q` and `T(0, b) := 0`: the density
`a / m` already vanishes on `{a = 0}`, and Lean's `b / 0 = 0` is `T(0, b)`.
`reweight_lintegral_boundary` below states this identification. -/
def reweight (Q : Measure (ℝ × ℝ)) : Measure ℝ :=
  (Q.withDensity fun p => ENNReal.ofReal (p.1 / numeraireMean Q)).map
    fun p => p.2 / p.1

/-- The boundary family `W = |B|^s A^{1-s}` (paper, eq. (2)).  Only its values
on `{a > 0}` ever matter: the inputs `Q n` do not charge `{a ≤ 0}`, and the
limit integral `boundaryIntegral` is restricted to `{a > 0}`. -/
def boundaryFamily (s : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|p.2| ^ s * p.1 ^ (1 - s))

/-- `I_s := ∫_{a > 0} |b|^s a^{1-s} Q(da, db)` (Theorem 3.3). -/
def boundaryIntegral (s : ℝ) (Q : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p in {p | 0 < p.1}, boundaryFamily s p ∂Q

/-- The ratio tail `sup_n E_{Q n}[W ; |B| > R A]` at level `R` (Theorem 3.3(iii)). -/
def ratioTail (s : ℝ) (Q : ℕ → Measure (ℝ × ℝ)) (R : ℝ) : ℝ≥0∞ :=
  ⨆ n, ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂(Q n)

/-- The standing hypotheses (S1)–(S2) of §3.1.  `Q n` is the law of
`(A_n, B_n)`; `Qlim` is the limit law `Q`. -/
structure StandingSetting (Q : ℕ → Measure (ℝ × ℝ)) (Qlim : Measure (ℝ × ℝ)) :
    Prop where
  prob : ∀ n, IsProbabilityMeasure (Q n)
  prob_lim : IsProbabilityMeasure Qlim
  /-- `(A_n, B_n)` takes values in `(0, ∞) × ℝ`. -/
  pos : ∀ n, Q n {p | p.1 ≤ 0} = 0
  /-- `Q` is a law on the closed half-plane `[0, ∞) × ℝ`. -/
  lim_supp : Qlim {p | p.1 < 0} = 0
  /-- (S1) `Q_n → Q` weakly.  (For laws carried by the closed half-plane,
  weak convergence on `ℝ × ℝ` and on `[0, ∞) × ℝ` coincide.) -/
  weak : WeakConv Q Qlim
  /-- (S2) the numéraires `{A_n}` are uniformly integrable. -/
  ui : UnifIntegrableFamily Q fun p => ENNReal.ofReal p.1
  /-- (S2) `m := ∫ a dQ > 0`. -/
  mean_pos : 0 < numeraireMean Qlim

/-! ## Section 2 — Proposition 2.1 (perspective cancellation) -/

section Cancellation

variable (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]

/-- `Γ(Q)` is a probability measure (paper, §2 and §3.1). -/
theorem reweight_isProbabilityMeasure (hsupp : P {p | p.1 < 0} = 0)
    (hm : 0 < numeraireMean P) :
    IsProbabilityMeasure (reweight P) := by
  sorry

/-- Proposition 2.1, general identity: `∫ f dΓ = E_Q[A f(B/A)] / A⁰` for every
measurable `f ≥ 0`, as an identity in `[0, ∞]`. -/
theorem cancellation_general (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(reweight P) =
      (∫⁻ p, ENNReal.ofReal p.1 * f (p.2 / p.1) ∂P) /
        ENNReal.ofReal (numeraireMean P) := by
  sorry

/-- Proposition 2.1, call identity: `∫ (z - K)⁺ dΓ = E_Q[(B - K A)⁺] / A⁰`. -/
theorem cancellation_call (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (K : ℝ) :
    ∫⁻ z, ENNReal.ofReal (max (z - K) 0) ∂(reweight P) =
      (∫⁻ p, ENNReal.ofReal (max (p.2 - K * p.1) 0) ∂P) /
        ENNReal.ofReal (numeraireMean P) := by
  sorry

/-- Proposition 2.1, first moment: `∫ |z| dΓ = E_Q|B| / A⁰`. -/
theorem cancellation_first_moment (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) :
    ∫⁻ z, ENNReal.ofReal |z| ∂(reweight P) =
      (∫⁻ p, ENNReal.ofReal |p.2| ∂P) / ENNReal.ofReal (numeraireMean P) := by
  sorry

/-- Proposition 2.1, `s`-th moment for `s > 1`:
`∫ |z|^s dΓ = E_Q[|B|^s A^{1-s}] / A⁰`. -/
theorem cancellation_moment (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) {s : ℝ} (hs : 1 < s) :
    ∫⁻ z, ENNReal.ofReal (|z| ^ s) ∂(reweight P) =
      (∫⁻ p, boundaryFamily s p ∂P) / ENNReal.ofReal (numeraireMean P) := by
  sorry

/-- Proposition 2.1, "in particular": the first moment is finite whenever
`E_Q|B| < ∞`, with no condition on `1/A`. -/
theorem hasFiniteMoment_one_of_integrable (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (hB : ∫⁻ p, ENNReal.ofReal |p.2| ∂P < ∞) :
    HasFiniteMoment 1 (reweight P) := by
  sorry

/-- Proposition 2.1, "in particular": for `s > 1` the `s`-moment is finite
exactly when `E_Q[|B|^s A^{1-s}] < ∞`. -/
theorem hasFiniteMoment_iff (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) {s : ℝ} (hs : 1 < s) :
    HasFiniteMoment s (reweight P) ↔ ∫⁻ p, boundaryFamily s p ∂P < ∞ := by
  sorry

/-- §3.1, the boundary-permitting limit object: when `Q` may charge
`{a = 0}`, `∫ f dΓ = m⁻¹ ∫_{a > 0} a f(b/a) dQ` for every Borel `f ≥ 0`.
This identifies `reweight` with the paper's limit `Γ`. -/
theorem reweight_lintegral_boundary (hsupp : P {p | p.1 < 0} = 0)
    (hm : 0 < numeraireMean P) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(reweight P) =
      (∫⁻ p in {p | 0 < p.1}, ENNReal.ofReal p.1 * f (p.2 / p.1) ∂P) /
        ENNReal.ofReal (numeraireMean P) := by
  sorry

end Cancellation

/-! ## Section 3 — the two-way stability theorem -/

section Stability

variable {Q : ℕ → Measure (ℝ × ℝ)} {Qlim : Measure (ℝ × ℝ)}

/-- §3.1: "Under (S1)–(S2), `E[A_n] → m`." -/
theorem mean_tendsto (h : StandingSetting Q Qlim) :
    Tendsto (fun n => numeraireMean (Q n)) atTop (𝓝 (numeraireMean Qlim)) := by
  sorry

/-- Lemma 3.1 (weak stability under numéraire uniform integrability):
under (S1)–(S2), `Γ_n → Γ` weakly. -/
theorem weak_stability (h : StandingSetting Q Qlim) :
    WeakConv (fun n => reweight (Q n)) (reweight Qlim) := by
  sorry

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
        Tendsto (ratioTail s Q) atTop (𝓝 0) ] := by
  sorry

/-- Corollary 3.4(a).  If `{|B_n|}` is uniformly integrable, then
`Γ, Γ_n ∈ 𝒫_1(ℝ)`, and `W_1(Γ_n, Γ) → 0` iff `∫_{a = 0} |b| dQ = 0`. -/
theorem sharp_cancellation (h : StandingSetting Q Qlim)
    (hB : UnifIntegrableFamily Q fun p => ENNReal.ofReal |p.2|) :
    HasFiniteMoment 1 (reweight Qlim) ∧ (∀ n, HasFiniteMoment 1 (reweight (Q n))) ∧
      (Tendsto (fun n => wasserstein 1 (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0) ↔
        ∫⁻ p in {p | p.1 = 0}, ENNReal.ofReal |p.2| ∂Qlim = 0) := by
  sorry

/-- Corollary 3.4(a), "in particular": if `Q({a = 0}) = 0`, then
`W_1(Γ_n, Γ) → 0`, with no hypothesis on `{1/A_n}`. -/
theorem sharp_cancellation_of_no_boundary (h : StandingSetting Q Qlim)
    (hB : UnifIntegrableFamily Q fun p => ENNReal.ofReal |p.2|)
    (h0 : Qlim {p | p.1 = 0} = 0) :
    Tendsto (fun n => wasserstein 1 (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0) := by
  sorry

/-- Corollary 3.4(b).  If `Q({a = 0}) = 0` and `s ≥ 1`, then
`Γ, Γ_n ∈ 𝒫_s(ℝ)` with `W_s(Γ_n, Γ) → 0` iff `{W_n}` is uniformly integrable. -/
theorem boundary_free_iff_unifIntegrable (h : StandingSetting Q Qlim)
    (h0 : Qlim {p | p.1 = 0} = 0) {s : ℝ} (hs : 1 ≤ s) :
    (HasFiniteMoment s (reweight Qlim) ∧ (∀ n, HasFiniteMoment s (reweight (Q n))) ∧
        Tendsto (fun n => wasserstein s (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0)) ↔
      UnifIntegrableFamily Q (boundaryFamily s) := by
  sorry

end Stability

/-! ## Section 4 — sharpness -/

section Sharpness

/-- Example 4.1 inputs: mass `1 - ε` at `(1, 0)` and mass `ε` at `(a, 1)`,
with `a = ε^{1/(s-1)}`. -/
def exTwoAtom (s ε : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac ((1 : ℝ), (0 : ℝ)) +
    ENNReal.ofReal ε • Measure.dirac (ε ^ (1 / (s - 1)), (1 : ℝ))

/-- Example 4.1: `E[A_n] = 1 - ε_n + ε_n a_n`. -/
theorem exTwoAtom_mean {s ε : ℝ} (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    numeraireMean (exTwoAtom s ε) = 1 - ε + ε * ε ^ (1 / (s - 1)) := by
  sorry

/-- Example 4.1: `Γ_n` has an atom at `0` of mass `(1 - ε_n)/E[A_n]` and an
atom at `1/a_n` of mass `ε_n a_n / E[A_n]`. -/
theorem reweight_exTwoAtom {s ε : ℝ} (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    reweight (exTwoAtom s ε) =
      ENNReal.ofReal ((1 - ε) / numeraireMean (exTwoAtom s ε)) • Measure.dirac 0 +
        ENNReal.ofReal (ε * ε ^ (1 / (s - 1)) / numeraireMean (exTwoAtom s ε)) •
          Measure.dirac (1 / ε ^ (1 / (s - 1))) := by
  sorry

/-- Example 4.1: for every `σ ≥ 1`,
`∫ |z|^σ dΓ_n = ε_n^{(s-σ)/(s-1)} / E[A_n]`. -/
theorem exTwoAtom_moment {s ε σ : ℝ} (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) (hσ : 1 ≤ σ) :
    ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s ε)) =
      ENNReal.ofReal (ε ^ ((s - σ) / (s - 1)) / numeraireMean (exTwoAtom s ε)) := by
  sorry

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
    ¬ UnifIntegrableFamily (fun n => exTwoAtom s (ε n)) (boundaryFamily s) := by
  sorry

/-- Example 4.3 inputs: mass `1 - ε` at `(1, 0)` and mass `ε` at `(α, 1)`.
With `α = 0` this is the limit law `(1 - ε) δ_{(1,0)} + ε δ_{(0,1)}`. -/
def exBoundaryMass (ε α : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac ((1 : ℝ), (0 : ℝ)) +
    ENNReal.ofReal ε • Measure.dirac (α, (1 : ℝ))

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
    ¬ Tendsto (ratioTail 1 fun n => exBoundaryMass ε (α n)) atTop (𝓝 0) := by
  sorry

/-- Example 4.4 inputs: mass `1 - ε` at `(1, 0)` and mass `ε` at `(1/ε, 1/ε)`. -/
def exNoUnifIntegrable (ε : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac ((1 : ℝ), (0 : ℝ)) +
    ENNReal.ofReal ε • Measure.dirac (1 / ε, 1 / ε)

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
    ¬ WeakConv (fun n => reweight (exNoUnifIntegrable (ε n))) (Measure.dirac 0) := by
  sorry

end Sharpness

end NumeraireStability
