/-
# Computations with two-atom laws (for the examples of Section 4)
-/
import NumeraireStability.Stability
import NumeraireStability.Wasserstein

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-- A two-atom measure `c₁ δ_x + c₂ δ_y` with nonnegative real weights. -/
abbrev twoAtoms {X : Type*} [MeasurableSpace X] (c1 c2 : ℝ) (x y : X) : Measure X :=
  ENNReal.ofReal c1 • Measure.dirac x + ENNReal.ofReal c2 • Measure.dirac y

section General

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

lemma twoAtoms_apply (c1 c2 : ℝ) (x y : X) (S : Set X) :
    twoAtoms c1 c2 x y S = ENNReal.ofReal c1 * S.indicator 1 x +
      ENNReal.ofReal c2 * S.indicator 1 y := by
  simp [twoAtoms, Measure.dirac_apply]

lemma lintegral_twoAtoms (c1 c2 : ℝ) (x y : X) (f : X → ℝ≥0∞) :
    ∫⁻ z, f z ∂(twoAtoms c1 c2 x y) = ENNReal.ofReal c1 * f x + ENNReal.ofReal c2 * f y := by
  rw [twoAtoms, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  rfl

lemma twoAtoms_null (c1 c2 : ℝ) (x y : X) {S : Set X} (hx : x ∉ S) (hy : y ∉ S) :
    twoAtoms c1 c2 x y S = 0 := by
  rw [twoAtoms_apply, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  simp

lemma isProbabilityMeasure_twoAtoms {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (h : c1 + c2 = 1) (x y : X) : IsProbabilityMeasure (twoAtoms c1 c2 x y) := by
  constructor
  rw [twoAtoms_apply]
  simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add hc1 hc2, h, ENNReal.ofReal_one]

end General

section Integral

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MeasurableSingletonClass X]

lemma integral_twoAtoms (f : X →ᵇ ℝ) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (x y : X) :
    ∫ z, f z ∂(twoAtoms c1 c2 x y) = c1 * f x + c2 * f y := by
  rw [twoAtoms, integral_add_measure
      ((f.integrable (Measure.dirac x)).smul_measure ENNReal.ofReal_ne_top)
      ((f.integrable (Measure.dirac y)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal hc1, ENNReal.toReal_ofReal hc2, smul_eq_mul, smul_eq_mul]

end Integral

/-- The numéraire mean of a two-atom law with nonnegative numéraires. -/
lemma numeraireMean_twoAtoms {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) {x y : ℝ × ℝ}
    (hx : 0 ≤ x.1) (hy : 0 ≤ y.1) :
    numeraireMean (twoAtoms c1 c2 x y) = c1 * x.1 + c2 * y.1 := by
  have hneg : twoAtoms c1 c2 x y {p | p.1 < 0} = 0 :=
    twoAtoms_null c1 c2 x y (fun h => absurd h (not_lt.2 hx)) (fun h => absurd h (not_lt.2 hy))
  rw [numeraireMean_eq_toReal hneg, lintegral_twoAtoms, ← ENNReal.ofReal_mul hc1,
    ← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add (mul_nonneg hc1 hx) (mul_nonneg hc2 hy),
    ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hc1 hx) (mul_nonneg hc2 hy))]

/-- The reweighting of a two-atom law is a two-atom law. -/
lemma reweight_twoAtoms {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (x y : ℝ × ℝ) :
    reweight (twoAtoms c1 c2 x y) =
      twoAtoms (c1 * (x.1 / numeraireMean (twoAtoms c1 c2 x y)))
        (c2 * (y.1 / numeraireMean (twoAtoms c1 c2 x y))) (x.2 / x.1) (y.2 / y.1) := by
  rw [reweight, twoAtoms, withDensity_add_measure, withDensity_smul_measure,
    withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
    Measure.map_add _ _ measurable_ratio, Measure.map_smul, Measure.map_smul, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' measurable_ratio, Measure.map_dirac' measurable_ratio,
    smul_smul, smul_smul, ← ENNReal.ofReal_mul hc1, ← ENNReal.ofReal_mul hc2]
  all_goals exact measurable_ratio.aemeasurable

/-- The reweighting of a point mass at `(a, b)`, `a > 0`, is the point mass at `b/a`. -/
lemma reweight_dirac {x : ℝ × ℝ} (hx : 0 < x.1) :
    reweight (Measure.dirac x) = Measure.dirac (x.2 / x.1) := by
  have hm : numeraireMean (Measure.dirac x) = x.1 := by
    rw [numeraireMean, integral_dirac]
  rw [reweight, dirac_withDensity, Measure.map_smul, Measure.map_dirac' measurable_ratio, hm,
    div_self hx.ne', ENNReal.ofReal_one, one_smul]
  exact measurable_ratio.aemeasurable

end NumeraireStability
