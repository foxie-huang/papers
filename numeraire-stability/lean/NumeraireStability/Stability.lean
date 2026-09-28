/-
# Weak stability of the reweighting (Lemma 3.1) and convergence of means
-/
import NumeraireStability.Cancellation
import NumeraireStability.WeakLimits

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-- `(a, b) ↦ a⁺ F(b/a)` is continuous for bounded continuous `F`: it extends
by `0` across `a = 0` (paper, proof of Lemma 3.1). -/
lemma continuous_perspective (F : ℝ → ℝ) (hF : Continuous F) (C : ℝ)
    (hC : ∀ x, |F x| ≤ C) :
    Continuous fun p : ℝ × ℝ => max p.1 0 * F (p.2 / p.1) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.1 = 0
  · have hlim : Tendsto (fun q : ℝ × ℝ => C * max q.1 0) (𝓝 p) (𝓝 0) := by
      have hc : Continuous fun q : ℝ × ℝ => C * max q.1 0 :=
        continuous_const.mul (continuous_fst.max continuous_const)
      simpa [hp] using hc.tendsto p
    show Tendsto _ (𝓝 p) (𝓝 (max p.1 0 * F (p.2 / p.1)))
    rw [hp, max_self, zero_mul]
    refine squeeze_zero_norm (fun q => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_max_right _ _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (le_max_right _ _)
  · exact (continuous_fst.max continuous_const).continuousAt.mul
      (hF.continuousAt.comp (continuousAt_snd.div continuousAt_fst hp))

lemma numeraireMean_eq_toReal {ρ : Measure (ℝ × ℝ)} (h : ρ {p | p.1 < 0} = 0) :
    numeraireMean ρ = (∫⁻ p, ENNReal.ofReal p.1 ∂ρ).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_nonneg_of_null h)
    measurable_fst.aestronglyMeasurable

section Standing

variable {Q : ℕ → Measure (ℝ × ℝ)} {Qlim : Measure (ℝ × ℝ)}

lemma StandingSetting.neg_null (h : StandingSetting Q Qlim) (n : ℕ) :
    Q n {p | p.1 < 0} = 0 := by
  refine measure_mono_null ?_ (h.pos n)
  intro p hp
  exact le_of_lt (show p.1 < 0 from hp)

lemma StandingSetting.uiTails_pos (h : StandingSetting Q Qlim) :
    UITails Q fun p => ENNReal.ofReal (max p.1 0) := by
  simp_rw [ofReal_max_zero]
  exact h.ui

lemma StandingSetting.lintegral_fst_lt_top (h : StandingSetting Q Qlim) (n : ℕ) :
    ∫⁻ p, ENNReal.ofReal p.1 ∂(Q n) < ∞ := by
  obtain ⟨C, hC, hCb⟩ := exists_bound_of_uiTails h.prob _
    (continuous_fst.max continuous_const) h.uiTails_pos
  have := hCb n
  simp_rw [ofReal_max_zero] at this
  exact this.trans_lt hC

/-- Each `E[A_n]` is strictly positive. -/
lemma StandingSetting.mean_pos_n (h : StandingSetting Q Qlim) (n : ℕ) :
    0 < numeraireMean (Q n) := by
  have := h.prob n
  rw [numeraireMean_eq_toReal (h.neg_null n)]
  refine ENNReal.toReal_pos (fun h0 => ?_) (h.lintegral_fst_lt_top n).ne
  rw [lintegral_eq_zero_iff measurable_fst.ennreal_ofReal] at h0
  have hfalse : ∀ᵐ p ∂(Q n), False := (h0.and (ae_pos_of_null (h.pos n))).mono
    fun p hp => by
      have h1 := hp.1
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h1
      linarith [hp.2]
  exact absurd (ae_iff.1 hfalse) (by simp)

/-- §3.1: `E[A_n] → m`. -/
theorem StandingSetting.tendsto_mean (h : StandingSetting Q Qlim) :
    Tendsto (fun n => numeraireMean (Q n)) atTop (𝓝 (numeraireMean Qlim)) := by
  obtain ⟨hfin, htend⟩ := tendsto_lintegral_of_uiTails h.prob h.prob_lim h.weak _
    (continuous_fst.max continuous_const) (fun p => le_max_right _ _) h.uiTails_pos
  simp_rw [ofReal_max_zero] at hfin htend
  have e : (fun n => numeraireMean (Q n)) =
      fun n => (∫⁻ p, ENNReal.ofReal p.1 ∂(Q n)).toReal :=
    funext fun n => numeraireMean_eq_toReal (h.neg_null n)
  rw [e, numeraireMean_eq_toReal h.lim_supp]
  exact (ENNReal.tendsto_toReal hfin.ne).comp htend

lemma StandingSetting.isProbabilityMeasure_reweight_n (h : StandingSetting Q Qlim) (n : ℕ) :
    IsProbabilityMeasure (reweight (Q n)) :=
  NumeraireStability.isProbabilityMeasure_reweight _ (h.neg_null n) (h.mean_pos_n n)

lemma StandingSetting.isProbabilityMeasure_reweight_lim' (h : StandingSetting Q Qlim) :
    IsProbabilityMeasure (reweight Qlim) :=
  NumeraireStability.isProbabilityMeasure_reweight _ h.lim_supp h.mean_pos

/-- The weighted integrand `a⁺ G(b/a)⁺` behind `∫ G⁺ dΓ`. -/
lemma lintegral_reweight_eq_perspective (ρ : Measure (ℝ × ℝ)) (hm : 0 < numeraireMean ρ)
    (G : ℝ → ℝ) (hGc : Continuous G) :
    ∫⁻ z, ENNReal.ofReal (G z) ∂(reweight ρ) =
      (∫⁻ p, ENNReal.ofReal (max p.1 0 * max (G (p.2 / p.1)) 0) ∂ρ) /
        ENNReal.ofReal (numeraireMean ρ) := by
  rw [lintegral_reweight ρ hm _ hGc.measurable.ennreal_ofReal]
  congr 2
  ext p
  rw [ENNReal.ofReal_mul (le_max_right _ _), ofReal_max_zero, ofReal_max_zero]

/-- Positive parts: `∫ G⁺ dΓ_n → ∫ G⁺ dΓ` for continuous `G ≤ 1`. -/
lemma StandingSetting.tendsto_lintegral_reweight (h : StandingSetting Q Qlim) (G : ℝ → ℝ)
    (hGc : Continuous G) (hG1 : ∀ z, |G z| ≤ 1) :
    ∫⁻ z, ENNReal.ofReal (G z) ∂(reweight Qlim) < ∞ ∧
      Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (G z) ∂(reweight (Q n))) atTop
        (𝓝 (∫⁻ z, ENNReal.ofReal (G z) ∂(reweight Qlim))) := by
  set φ : ℝ × ℝ → ℝ := fun p => max p.1 0 * max (G (p.2 / p.1)) 0
  have hGp : ∀ z, |max (G z) 0| ≤ 1 := fun z => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hG1 z)) zero_le_one
  have hφc : Continuous φ :=
    continuous_perspective (fun z => max (G z) 0) (hGc.max continuous_const) 1 hGp
  have hφ0 : ∀ p, 0 ≤ φ p := fun p => mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hφle : ∀ p, φ p ≤ max p.1 0 := fun p => by
    have := hGp (p.2 / p.1)
    rw [abs_of_nonneg (le_max_right _ _)] at this
    exact mul_le_of_le_one_right (le_max_right _ _) this
  obtain ⟨hfin, htend⟩ := tendsto_lintegral_of_uiTails h.prob h.prob_lim h.weak φ hφc hφ0
    (uiTails_mono hφle h.uiTails_pos)
  have hm0 : ENNReal.ofReal (numeraireMean Qlim) ≠ 0 := (ENNReal.ofReal_pos.2 h.mean_pos).ne'
  rw [lintegral_reweight_eq_perspective _ h.mean_pos G hGc]
  refine ⟨ENNReal.div_lt_top hfin.ne hm0, ?_⟩
  have e : (fun n => ∫⁻ z, ENNReal.ofReal (G z) ∂(reweight (Q n))) =
      fun n => (∫⁻ p, ENNReal.ofReal (φ p) ∂(Q n)) / ENNReal.ofReal (numeraireMean (Q n)) :=
    funext fun n => lintegral_reweight_eq_perspective _ (h.mean_pos_n n) G hGc
  rw [e]
  exact ENNReal.Tendsto.div htend (Or.inr hm0)
    (ENNReal.tendsto_ofReal h.tendsto_mean) (Or.inl ENNReal.ofReal_ne_top)

/-- Bounded continuous `F` with `|F| ≤ 1`: `∫ F dΓ_n → ∫ F dΓ`. -/
lemma StandingSetting.tendsto_integral_reweight (h : StandingSetting Q Qlim) (F : ℝ → ℝ)
    (hFc : Continuous F) (hF1 : ∀ z, |F z| ≤ 1) :
    Tendsto (fun n => ∫ z, F z ∂(reweight (Q n))) atTop (𝓝 (∫ z, F z ∂(reweight Qlim))) := by
  have hint : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → Integrable F ρ := fun ρ _ =>
    Integrable.of_bound hFc.aestronglyMeasurable 1
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hF1 z)
  have hsplit : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
      ∫ z, F z ∂ρ = (∫⁻ z, ENNReal.ofReal (F z) ∂ρ).toReal -
        (∫⁻ z, ENNReal.ofReal (-F z) ∂ρ).toReal := fun ρ hρ =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint ρ hρ)
  obtain ⟨hpfin, hptend⟩ := h.tendsto_lintegral_reweight F hFc hF1
  obtain ⟨hmfin, hmtend⟩ := h.tendsto_lintegral_reweight (fun z => -F z) hFc.neg
    (fun z => by simpa using hF1 z)
  have e : (fun n => ∫ z, F z ∂(reweight (Q n))) = fun n =>
      (∫⁻ z, ENNReal.ofReal (F z) ∂(reweight (Q n))).toReal -
        (∫⁻ z, ENNReal.ofReal (-F z) ∂(reweight (Q n))).toReal :=
    funext fun n => hsplit _ (h.isProbabilityMeasure_reweight_n n)
  rw [e, hsplit _ h.isProbabilityMeasure_reweight_lim']
  exact ((ENNReal.tendsto_toReal hpfin.ne).comp hptend).sub
    ((ENNReal.tendsto_toReal hmfin.ne).comp hmtend)

/-- **Lemma 3.1.**  Under (S1)–(S2), `Γ_n → Γ` weakly. -/
theorem StandingSetting.weakConv_reweight (h : StandingSetting Q Qlim) :
    WeakConv (fun n => reweight (Q n)) (reweight Qlim) := by
  intro f
  set c : ℝ := ‖f‖ + 1
  have hc : 0 < c := by positivity
  have hF1 : ∀ z, |f z / c| ≤ 1 := fun z => by
    rw [abs_div, abs_of_pos hc, div_le_one hc, ← Real.norm_eq_abs]
    exact (f.norm_coe_le_norm z).trans (by linarith)
  have hfF : ∀ ρ : Measure ℝ, ∫ z, f z ∂ρ = c * ∫ z, f z / c ∂ρ := fun ρ => by
    rw [← integral_const_mul]
    congr 1
    ext z
    field_simp
  simp_rw [hfF]
  exact (h.tendsto_integral_reweight (fun z => f z / c) (f.continuous.div_const c) hF1).const_mul c

end Standing

end NumeraireStability
