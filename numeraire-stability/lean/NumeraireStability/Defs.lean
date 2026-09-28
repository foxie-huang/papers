/-
# Definitions for the Lean formalization of
"Stability of Change-of-Numéraire Reweighting: An Exact Wasserstein Boundary".

Moved verbatim from the step-1 statements file (`spec/Statements_step1.lean`).
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

/-! ## The example inputs of Section 4 -/

/-- Example 4.1 inputs: mass `1 - ε` at `(1, 0)` and mass `ε` at `(a, 1)`,
with `a = ε^{1/(s-1)}`. -/
def exTwoAtom (s ε : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac ((1 : ℝ), (0 : ℝ)) +
    ENNReal.ofReal ε • Measure.dirac (ε ^ (1 / (s - 1)), (1 : ℝ))

/-- Example 4.3 inputs: mass `1 - ε` at `(1, 0)` and mass `ε` at `(α, 1)`.
With `α = 0` this is the limit law `(1 - ε) δ_{(1,0)} + ε δ_{(0,1)}`. -/
def exBoundaryMass (ε α : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac ((1 : ℝ), (0 : ℝ)) +
    ENNReal.ofReal ε • Measure.dirac (α, (1 : ℝ))

/-- Example 4.4 inputs: mass `1 - ε` at `(1, 0)` and mass `ε` at `(1/ε, 1/ε)`. -/
def exNoUnifIntegrable (ε : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac ((1 : ℝ), (0 : ℝ)) +
    ENNReal.ofReal ε • Measure.dirac (1 / ε, 1 / ε)

end NumeraireStability
