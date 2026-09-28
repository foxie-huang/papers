/-
# The cancellation identity behind Proposition 2.1

`∫ f dΓ(Q) = (∫ a f(b/a) dQ) / E_Q[A]`, in `[0, ∞]` for Borel `f ≥ 0` and as a
Bochner integral for bounded Borel `f`.
-/
import NumeraireStability.Defs

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

lemma measurable_ratio : Measurable fun p : ℝ × ℝ => p.2 / p.1 :=
  measurable_snd.div measurable_fst

lemma measurable_density (m : ℝ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.1 / m) :=
  ENNReal.measurable_ofReal.comp (measurable_fst.div_const m)

/-- If `Q` does not charge `{a ≤ 0}` then `a > 0` almost surely. -/
lemma ae_pos_of_null {Q : Measure (ℝ × ℝ)} (h : Q {p | p.1 ≤ 0} = 0) :
    ∀ᵐ p ∂Q, 0 < p.1 :=
  (measure_eq_zero_iff_ae_notMem.1 h).mono fun _ hp => not_le.1 hp

/-- If `Q` does not charge `{a < 0}` then `a ≥ 0` almost surely. -/
lemma ae_nonneg_of_null {Q : Measure (ℝ × ℝ)} (h : Q {p | p.1 < 0} = 0) :
    ∀ᵐ p ∂Q, 0 ≤ p.1 :=
  (measure_eq_zero_iff_ae_notMem.1 h).mono fun _ hp => not_lt.1 hp

lemma integrable_fst_of_mean_pos {Q : Measure (ℝ × ℝ)} (hm : 0 < numeraireMean Q) :
    Integrable (fun p : ℝ × ℝ => p.1) Q :=
  Integrable.of_integral_ne_zero hm.ne'

/-- The cancellation identity in `[0, ∞]`. -/
theorem lintegral_reweight (Q : Measure (ℝ × ℝ)) (hm : 0 < numeraireMean Q)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(reweight Q) =
      (∫⁻ p, ENNReal.ofReal p.1 * f (p.2 / p.1) ∂Q) /
        ENNReal.ofReal (numeraireMean Q) := by
  have hc : (ENNReal.ofReal (numeraireMean Q))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hm).ne'
  rw [reweight, lintegral_map hf measurable_ratio,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_density _)
      (show Measurable fun p : ℝ × ℝ => f (p.2 / p.1) from hf.comp measurable_ratio),
    ENNReal.div_eq_inv_mul, ← lintegral_const_mul' _ _ hc]
  congr 1
  ext p
  simp only [Pi.mul_apply, ENNReal.ofReal_div_of_pos hm,
    ENNReal.div_eq_inv_mul]
  ring

/-- The cancellation identity with the integral restricted to `{a > 0}`;
valid for every `Q`, since the weight `a⁺` vanishes elsewhere. -/
theorem lintegral_reweight_pos (Q : Measure (ℝ × ℝ)) (hm : 0 < numeraireMean Q)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(reweight Q) =
      (∫⁻ p in {p | 0 < p.1}, ENNReal.ofReal p.1 * f (p.2 / p.1) ∂Q) /
        ENNReal.ofReal (numeraireMean Q) := by
  rw [lintegral_reweight Q hm f hf,
    ← lintegral_indicator (measurableSet_lt measurable_const measurable_fst)]
  congr 2
  ext p
  by_cases hp : 0 < p.1
  · simp [Set.indicator_of_mem, hp]
  · simp [Set.indicator_of_notMem, hp, ENNReal.ofReal_eq_zero.2 (not_lt.1 hp)]

/-- `Γ(Q)` is a probability measure when `Q` is carried by `{a ≥ 0}` and
`E_Q[A] > 0`. -/
theorem isProbabilityMeasure_reweight (Q : Measure (ℝ × ℝ))
    (hsupp : Q {p | p.1 < 0} = 0) (hm : 0 < numeraireMean Q) :
    IsProbabilityMeasure (reweight Q) := by
  constructor
  have h1 := lintegral_reweight Q hm (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, mul_one] at h1
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal (integrable_fst_of_mean_pos hm)
    (ae_nonneg_of_null hsupp)]
  exact ENNReal.div_self (ENNReal.ofReal_pos.2 hm).ne' ENNReal.ofReal_ne_top

end NumeraireStability
