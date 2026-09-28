/-
# Definitions for Sections 5 and 6

Moved verbatim from the step-1 statements file (`spec/Statements56_step1.lean`).
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

/-! ## Hypothesis bundles -/

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

end JointContinuity

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

end Involution

section Annuity

variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {𝔸 : Type*} [MetricSpace 𝔸] [CompactSpace 𝔸]

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

end Annuity

end NumeraireStability
