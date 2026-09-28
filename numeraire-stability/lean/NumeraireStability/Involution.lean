/-
# Section 6.1: the change-of-numéraire involution

`S(μ)` is the reweighting of the law of `(X, 1)`.  Under the hypotheses of
Corollary 6.1 these laws satisfy (S1)–(S2) and do not charge `{a = 0}`, so
Theorem 3.3 and Corollary 3.4(b) apply with `W_n = X_n^{1-s}` and
`{|B_n| > R A_n} = {X_n < 1/R}`.
-/
import NumeraireStability.Defs56
import NumeraireStability.Corollary
import NumeraireStability.TwoAtoms

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-- `x ↦ (x, 1)`. -/
abbrev lift1 : ℝ → ℝ × ℝ := fun x => (x, 1)

lemma measurable_lift1 : Measurable lift1 := measurable_id.prodMk measurable_const

lemma continuous_lift1 : Continuous lift1 := continuous_id.prodMk continuous_const

lemma involution_eq (μ : Measure ℝ) : involution μ = reweight (μ.map lift1) := rfl

lemma lintegral_lift (μ : Measure ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(μ.map lift1) = ∫⁻ x, f (x, 1) ∂μ :=
  lintegral_map hf measurable_lift1

lemma setLIntegral_lift (μ : Measure ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    ∫⁻ p in S, f p ∂(μ.map lift1) = ∫⁻ x in lift1 ⁻¹' S, f (x, 1) ∂μ :=
  setLIntegral_map hS hf measurable_lift1

lemma boundaryFamily_lift (s x : ℝ) :
    boundaryFamily s (x, 1) = ENNReal.ofReal (x ^ (1 - s)) := by
  simp [boundaryFamily]

lemma lift_apply_fst_le (μ : Measure ℝ) : (μ.map lift1) {p | p.1 ≤ 0} = μ (Set.Iic 0) := by
  rw [Measure.map_apply measurable_lift1 (measurableSet_le measurable_fst measurable_const)]
  rfl

lemma numeraireMean_lift (μ : Measure ℝ) : numeraireMean (μ.map lift1) = ∫ x, x ∂μ := by
  unfold numeraireMean
  rw [integral_map measurable_lift1.aemeasurable measurable_fst.aestronglyMeasurable]

lemma ae_pos_of_Iic_null {μ : Measure ℝ} (h : μ (Set.Iic 0) = 0) : ∀ᵐ x ∂μ, 0 < x :=
  (measure_eq_zero_iff_ae_notMem.1 h).mono fun _x hx => not_le.1 hx

section Setting

variable {μ : ℕ → Measure ℝ} {μlim : Measure ℝ}

/-- The laws of `(X_n, 1)` satisfy the standing hypotheses (S1)–(S2). -/
theorem InvolutionSetting.standing (h : InvolutionSetting μ μlim) :
    StandingSetting (fun n => (μ n).map lift1) (μlim.map lift1) where
  prob n := by
    have := h.prob n
    infer_instance
  prob_lim := by
    have := h.prob_lim
    infer_instance
  pos n := by
    rw [lift_apply_fst_le]
    exact h.pos n
  lim_supp := by
    have h0 : (μlim.map lift1) {p : ℝ × ℝ | p.1 ≤ 0} = 0 := by
      rw [lift_apply_fst_le]
      exact h.pos_lim
    exact measure_mono_null (fun p (hp : p ∈ {p : ℝ × ℝ | p.1 < 0}) =>
      show p.1 ≤ 0 from (show p.1 < 0 from hp).le) h0
  weak := by
    intro f
    have := h.weak (f.compContinuous ⟨lift1, continuous_lift1⟩)
    simpa [integral_map measurable_lift1.aemeasurable f.continuous.aestronglyMeasurable]
      using this
  ui := by
    have e : ∀ (M : ℝ) (n : ℕ),
        ∫⁻ p in {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal p.1}, ENNReal.ofReal p.1
          ∂((μ n).map lift1) =
        ∫⁻ x in {x : ℝ | ENNReal.ofReal M < ENNReal.ofReal x}, ENNReal.ofReal x ∂(μ n) := by
      intro M n
      rw [setLIntegral_lift _ measurable_fst.ennreal_ofReal
        (measurableSet_lt measurable_const measurable_fst.ennreal_ofReal)]
      rfl
    unfold UnifIntegrableFamily
    simp_rw [e]
    exact h.ui
  mean_pos := by
    rw [numeraireMean_lift]
    exact h.mean_pos

lemma InvolutionSetting.boundary_free (h : InvolutionSetting μ μlim) :
    (μlim.map lift1) {p | p.1 = 0} = 0 := by
  have h0 : (μlim.map lift1) {p : ℝ × ℝ | p.1 ≤ 0} = 0 := by
    rw [lift_apply_fst_le]
    exact h.pos_lim
  exact measure_mono_null (fun p (hp : p ∈ {p : ℝ × ℝ | p.1 = 0}) =>
    show p.1 ≤ 0 from (show p.1 = 0 from hp).le) h0

end Setting

/-- **§6.1, eq. (11).** -/
theorem involution_moment' (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : μ (Set.Iic 0) = 0) (hm : 0 < ∫ x, x ∂μ) {s : ℝ} :
    involution μ (Set.Iic 0) = 0 ∧
    ∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂(involution μ) =
      (∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂μ) / ENNReal.ofReal (∫ x, x ∂μ) := by
  have hpos' : (μ.map lift1) {p | p.1 ≤ 0} = 0 := by
    rw [lift_apply_fst_le]
    exact hpos
  have hm' : 0 < numeraireMean (μ.map lift1) := by
    rw [numeraireMean_lift]
    exact hm
  refine ⟨?_, ?_⟩
  · rw [involution_eq, reweight, Measure.map_apply measurable_ratio measurableSet_Iic,
      withDensity_apply _ (measurable_ratio measurableSet_Iic)]
    refine setLIntegral_measure_zero _ _ ?_
    rw [Measure.map_apply measurable_lift1 (measurable_ratio measurableSet_Iic)]
    refine measure_mono_null (fun x hx => ?_) hpos
    simp only [mem_preimage, mem_Iic] at hx ⊢
    by_contra hcon
    have : 0 < 1 / x := one_div_pos.2 (not_le.1 hcon)
    linarith
  · have h := moment_reweight (μ.map lift1) hpos' hm' s
    rw [moment, lintegral_lift μ (measurable_boundaryFamily s), numeraireMean_lift] at h
    simp_rw [boundaryFamily_lift] at h
    exact h

section Corollary

variable {μ : ℕ → Measure ℝ} {μlim : Measure ℝ}

/-- **Corollary 6.1.** -/
theorem InvolutionSetting.stability (h : InvolutionSetting μ μlim) {s : ℝ} (hs : 1 ≤ s) :
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
          atTop (𝓝 0) ] := by
  have hS := h.standing
  refine ⟨hS.weakConv_reweight, ?_⟩
  have hT := hS.exact_two_way hs
  have hC := hS.boundary_free_iff h.boundary_free hs
  have e2 : ∀ n, ∫⁻ p, boundaryFamily s p ∂((μ n).map lift1) =
      ∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂(μ n) := fun n => by
    rw [lintegral_lift _ (measurable_boundaryFamily s)]
    simp_rw [boundaryFamily_lift]
  have eI : boundaryIntegral s (μlim.map lift1) = ∫⁻ x, ENNReal.ofReal (x ^ (1 - s)) ∂μlim := by
    rw [boundaryIntegral, setLIntegral_lift _ (measurable_boundaryFamily s)
      (measurableSet_lt measurable_const measurable_fst)]
    simp_rw [boundaryFamily_lift]
    rw [Measure.restrict_eq_self_of_ae_mem ((ae_pos_of_Iic_null h.pos_lim).mono
      fun x hx => show x ∈ lift1 ⁻¹' {p : ℝ × ℝ | 0 < p.1} from hx)]
  have eU : UnifIntegrableFamily (fun n => (μ n).map lift1) (boundaryFamily s) ↔
      UnifIntegrableReal μ fun x => ENNReal.ofReal (x ^ (1 - s)) := by
    have e : ∀ (M : ℝ) (n : ℕ),
        ∫⁻ p in {p | ENNReal.ofReal M < boundaryFamily s p}, boundaryFamily s p
          ∂((μ n).map lift1) =
        ∫⁻ x in {x : ℝ | ENNReal.ofReal M < ENNReal.ofReal (x ^ (1 - s))},
          ENNReal.ofReal (x ^ (1 - s)) ∂(μ n) := by
      intro M n
      rw [setLIntegral_lift _ (measurable_boundaryFamily s)
        (measurableSet_lt measurable_const (measurable_boundaryFamily s))]
      have hset : lift1 ⁻¹' {p : ℝ × ℝ | ENNReal.ofReal M < boundaryFamily s p} =
          {x : ℝ | ENNReal.ofReal M < ENNReal.ofReal (x ^ (1 - s))} := by
        ext x
        simp only [mem_preimage, mem_ofPred_eq, boundaryFamily_lift]
      rw [hset]
      simp_rw [boundaryFamily_lift]
    unfold UnifIntegrableFamily UnifIntegrableReal
    simp_rw [e]
  have eR : ∀ R : ℝ, 0 < R → ratioTail s (fun n => (μ n).map lift1) R =
      ⨆ n, ∫⁻ x in {x | x < 1 / R}, ENNReal.ofReal (x ^ (1 - s)) ∂(μ n) := by
    intro R hR
    unfold ratioTail
    congr 1
    ext n
    have hmeas : MeasurableSet {p : ℝ × ℝ | R * p.1 < |p.2|} :=
      measurableSet_lt (measurable_const.mul measurable_fst)
        (continuous_abs.measurable.comp measurable_snd)
    have hset : lift1 ⁻¹' {p : ℝ × ℝ | R * p.1 < |p.2|} = {x : ℝ | x < 1 / R} := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, abs_one]
      rw [lt_div_iff₀ hR, mul_comm]
    dsimp only
    rw [setLIntegral_lift _ (measurable_boundaryFamily s) hmeas, hset]
    simp_rw [boundaryFamily_lift]
  have hT' : List.TFAE
      [ HasFiniteMoment s (involution μlim) ∧ (∀ n, HasFiniteMoment s (involution (μ n))) ∧
          Tendsto (fun n => wasserstein s (involution (μ n)) (involution μlim)) atTop (𝓝 0),
        (∀ n, ∫⁻ p, boundaryFamily s p ∂((μ n).map lift1) < ∞) ∧
          boundaryIntegral s (μlim.map lift1) < ∞ ∧
          Tendsto (fun n => ∫⁻ p, boundaryFamily s p ∂((μ n).map lift1)) atTop
            (𝓝 (boundaryIntegral s (μlim.map lift1))),
        Tendsto (ratioTail s fun n => (μ n).map lift1) atTop (𝓝 0) ] := hT
  tfae_have 1 ↔ 2 := by
    refine (hT'.out 1 2).trans ?_
    simp_rw [e2, eI]
  tfae_have 1 ↔ 3 := hC.trans eU
  tfae_have 1 ↔ 4 := by
    refine (hT'.out 1 3).trans ?_
    exact tendsto_congr' ((eventually_gt_atTop 0).mono fun R hR => eR R hR)
  tfae_finish

/-- **Corollary 6.1**, `s = 1`. -/
theorem InvolutionSetting.w1 (h : InvolutionSetting μ μlim) :
    HasFiniteMoment 1 (involution μlim) ∧ (∀ n, HasFiniteMoment 1 (involution (μ n))) ∧
      Tendsto (fun n => wasserstein 1 (involution (μ n)) (involution μlim)) atTop (𝓝 0) := by
  refine ((h.stability le_rfl).2.out 1 3).2 ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with M hM
  refine (le_antisymm (iSup_le fun n => ?_) zero_le).symm
  have hempty : {x : ℝ | ENNReal.ofReal M < ENNReal.ofReal (x ^ ((1 : ℝ) - 1))} = ∅ := by
    ext x
    simp only [sub_self, Real.rpow_zero, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact ENNReal.ofReal_le_ofReal hM
  rw [hempty, Measure.restrict_empty, lintegral_zero_measure]

end Corollary

/-- **§6.1, first consequence (static part).** -/
theorem involution_second_moment_iff' (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : ν (Set.Iic 0) = 0) (hm : 0 < ∫ x, x ∂ν) :
    HasFiniteMoment 2 (involution ν) ↔ ∫⁻ x, ENNReal.ofReal x⁻¹ ∂ν < ∞ := by
  have h2 := (involution_moment' ν hpos hm (s := 2)).2
  have e : ∀ x : ℝ, x ^ ((1 : ℝ) - 2) = x⁻¹ := fun x => by
    rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  simp_rw [e] at h2
  unfold HasFiniteMoment
  rw [h2]
  constructor
  · intro hlt
    by_contra hW
    rw [not_lt, top_le_iff] at hW
    rw [hW, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hlt
    exact lt_irrefl _ hlt
  · intro hN
    exact ENNReal.div_lt_top hN.ne (ENNReal.ofReal_pos.2 hm).ne'

lemma rpow_one_sub_two (x : ℝ) : ENNReal.ofReal (x ^ ((1 : ℝ) - 2)) = ENNReal.ofReal x⁻¹ := by
  rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]

/-- **§6.1, first consequence (stability part).** -/
theorem involution_w2_iff' {μ : ℕ → Measure ℝ} {μlim : Measure ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure μlim]
    (hpos : ∀ n, μ n (Set.Iic 0) = 0) (hpos_lim : μlim (Set.Iic 0) = 0)
    (hweak : WeakConv μ μlim)
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
        UnifIntegrableReal μ fun x => ENNReal.ofReal x⁻¹ ] := by
  have hint : Integrable (fun x : ℝ => x) μlim := Integrable.of_integral_ne_zero hm.ne'
  have hlimfin : ∫⁻ x, ENNReal.ofReal x ∂μlim < ∞ := hint.lintegral_lt_top
  have hui : UnifIntegrableReal μ fun x => ENNReal.ofReal x := by
    have hφ := uiTails_of_tendsto_lintegral hprob inferInstance hweak (fun x : ℝ => max x 0)
      (continuous_id.max continuous_const) (fun x => le_max_right _ _)
      (fun n => by simpa [ofReal_max_zero] using hfin n) (by simpa [ofReal_max_zero] using hlimfin)
      (by simpa [ofReal_max_zero] using hmean)
    simpa [UITails, UnifIntegrableReal, ofReal_max_zero] using hφ
  have h : InvolutionSetting μ μlim := ⟨hprob, inferInstance, hpos, hpos_lim, hweak, hui, hm⟩
  have hT := (h.stability (s := 2) (by norm_num)).2
  simp_rw [rpow_one_sub_two] at hT
  tfae_have 1 ↔ 2 := hT.out 1 2
  tfae_have 1 ↔ 3 := hT.out 1 3
  tfae_finish

/-! ### The two-atom example -/

lemma exInvolutionTwoAtom_eq (ε : ℝ) : exInvolutionTwoAtom ε = twoAtoms (1 - ε) ε 1 ε := rfl

lemma involution_dirac_one : involution (Measure.dirac (1 : ℝ)) = Measure.dirac 1 := by
  rw [involution_eq, Measure.map_dirac' measurable_lift1, reweight_dirac (by norm_num)]
  norm_num

lemma exInvolution_lintegral (ε : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(exInvolutionTwoAtom ε) = ENNReal.ofReal (1 - ε) * f 1 + ENNReal.ofReal ε * f ε :=
  lintegral_twoAtoms _ _ _ _ f

lemma exInvolution_mean {ε : ℝ} (hε : 0 < ε ∧ ε < 1) :
    ∫ x, x ∂(exInvolutionTwoAtom ε) = 1 - ε + ε * ε := by
  have hprob : IsProbabilityMeasure (exInvolutionTwoAtom ε) :=
    isProbabilityMeasure_twoAtoms (by linarith [hε.2]) hε.1.le (by ring) _ _
  have hnn : 0 ≤ᵐ[exInvolutionTwoAtom ε] fun x : ℝ => x := by
    refine (measure_eq_zero_iff_ae_notMem.1 (twoAtoms_null (1 - ε) ε 1 ε
      (S := Set.Iio 0) (by simp) (by simp [hε.1.le]))).mono fun x hx => ?_
    simpa using hx
  rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable,
    exInvolution_lintegral, ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_mul hε.1.le,
    ← ENNReal.ofReal_add (by linarith [hε.2]) (mul_nonneg hε.1.le hε.1.le),
    ENNReal.toReal_ofReal (by nlinarith [hε.1, hε.2])]

lemma exInvolution_setting {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    InvolutionSetting (fun n => exInvolutionTwoAtom (ε n)) (Measure.dirac 1) where
  prob n := isProbabilityMeasure_twoAtoms (by linarith [(hε n).2]) (hε n).1.le (by ring) _ _
  prob_lim := inferInstance
  pos n := twoAtoms_null _ _ _ _ (by simp) (by simp [(hε n).1])
  pos_lim := by simp
  weak := by
    intro f
    have e : ∀ n, ∫ x, f x ∂(exInvolutionTwoAtom (ε n)) = (1 - ε n) * f 1 + ε n * f (ε n) :=
      fun n => integral_twoAtoms f (by linarith [(hε n).2]) (hε n).1.le _ _
    simp_rw [e, integral_dirac]
    have h1 : Tendsto (fun n => (1 - ε n) * f 1) atTop (𝓝 ((1 - 0) * f 1)) :=
      (tendsto_const_nhds.sub hεlim).mul_const _
    have h2 : Tendsto (fun n => ε n * f (ε n)) atTop (𝓝 (0 * f 0)) :=
      hεlim.mul ((f.continuous.tendsto 0).comp hεlim)
    simpa using h1.add h2
  ui := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with M hM
    refine (le_antisymm (iSup_le fun n => ?_) zero_le).symm
    rw [← lintegral_indicator (measurableSet_lt measurable_const ENNReal.measurable_ofReal),
      exInvolution_lintegral]
    have h1 : (1 : ℝ) ∉ {x : ℝ | ENNReal.ofReal M < ENNReal.ofReal x} := by
      simp only [mem_ofPred_eq, not_lt]
      exact ENNReal.ofReal_le_ofReal hM
    have h2 : ε n ∉ {x : ℝ | ENNReal.ofReal M < ENNReal.ofReal x} := by
      simp only [mem_ofPred_eq, not_lt]
      exact ENNReal.ofReal_le_ofReal ((hε n).2.le.trans hM)
    rw [indicator_of_notMem h1, indicator_of_notMem h2]
    simp
  mean_pos := by simp

/-- **§6.1, the two-atom laws.** -/
theorem involution_two_atom' {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    InvolutionSetting (fun n => exInvolutionTwoAtom (ε n)) (Measure.dirac 1) ∧
    involution (Measure.dirac 1) = Measure.dirac 1 ∧
    (∀ σ, 1 ≤ σ → σ < 2 →
      Tendsto (fun n => wasserstein σ (involution (exInvolutionTwoAtom (ε n))) (Measure.dirac 1))
        atTop (𝓝 0)) ∧
    ¬ Tendsto (fun n => wasserstein 2 (involution (exInvolutionTwoAtom (ε n))) (Measure.dirac 1))
        atTop (𝓝 0) := by
  have hset := exInvolution_setting hε hεlim
  refine ⟨hset, involution_dirac_one, fun σ hσ1 hσ2 => ?_, fun hW => ?_⟩
  · -- condition (ii) of Corollary 6.1 at `s = σ`
    have hT := (hset.stability hσ1).2
    have hlim : ∫⁻ x, ENNReal.ofReal (x ^ (1 - σ)) ∂(Measure.dirac (1 : ℝ)) = 1 := by
      simp
    have hval : ∀ n, ∫⁻ x, ENNReal.ofReal (x ^ (1 - σ)) ∂(exInvolutionTwoAtom (ε n)) =
        ENNReal.ofReal (1 - ε n + ε n ^ (2 - σ)) := fun n => by
      have he := (hε n).1
      rw [exInvolution_lintegral, Real.one_rpow, ENNReal.ofReal_one, mul_one,
        ← ENNReal.ofReal_mul he.le, ← ENNReal.ofReal_add (by linarith [(hε n).2])
          (mul_nonneg he.le (Real.rpow_nonneg he.le _))]
      congr 2
      rw [show (2 : ℝ) - σ = 1 + (1 - σ) by ring, Real.rpow_add he, Real.rpow_one]
    have h2 : (∀ n, ∫⁻ x, ENNReal.ofReal (x ^ (1 - σ)) ∂(exInvolutionTwoAtom (ε n)) < ∞) ∧
        ∫⁻ x, ENNReal.ofReal (x ^ (1 - σ)) ∂(Measure.dirac (1 : ℝ)) < ∞ ∧
        Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (x ^ (1 - σ)) ∂(exInvolutionTwoAtom (ε n)))
          atTop (𝓝 (∫⁻ x, ENNReal.ofReal (x ^ (1 - σ)) ∂(Measure.dirac (1 : ℝ)))) := by
      refine ⟨fun n => by rw [hval]; exact ENNReal.ofReal_lt_top, by rw [hlim]; simp, ?_⟩
      simp_rw [hval, hlim]
      have hpow : Tendsto (fun n => ε n ^ (2 - σ)) atTop (𝓝 ((0 : ℝ) ^ (2 - σ))) :=
        ((Real.continuous_rpow_const (by linarith)).tendsto 0).comp hεlim
      rw [Real.zero_rpow (by linarith)] at hpow
      have hR : Tendsto (fun n => 1 - ε n + ε n ^ (2 - σ)) atTop (𝓝 (1 - 0 + 0)) :=
        (tendsto_const_nhds.sub hεlim).add hpow
      simpa using ENNReal.tendsto_ofReal hR
    have h1 := (hT.out 1 2).2 h2
    rw [involution_dirac_one] at h1
    exact h1.2.2
  · -- `W_2 → 0` would force the second moments to converge to `1`; they tend to `2`
    have hmom := tendsto_moment_of_tendsto_wasserstein 2 (by norm_num)
      (ν := Measure.dirac 1) (by simp [moment]) hW
    have hδ : moment 2 (Measure.dirac (1 : ℝ)) = 1 := by simp [moment]
    have hval : ∀ n, moment 2 (involution (exInvolutionTwoAtom (ε n))) =
        ENNReal.ofReal ((2 - ε n) / (1 - ε n + ε n * ε n)) := fun n => by
      have he := hε n
      have hprob : IsProbabilityMeasure (exInvolutionTwoAtom (ε n)) := hset.prob n
      have hmean := exInvolution_mean he
      have hpos : 0 < 1 - ε n + ε n * ε n := by nlinarith [he.1, he.2]
      rw [moment, (involution_moment' _ (hset.pos n) (by rw [hmean]; exact hpos) (s := 2)).2,
        exInvolution_lintegral, hmean]
      simp_rw [rpow_one_sub_two]
      rw [inv_one, ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_mul he.1.le,
        mul_inv_cancel₀ he.1.ne', ← ENNReal.ofReal_add (by linarith [he.2]) zero_le_one,
        ← ENNReal.ofReal_div_of_pos hpos]
      congr 2
      ring
    simp_rw [hval, hδ] at hmom
    have hreal : Tendsto (fun n => (2 - ε n) / (1 - ε n + ε n * ε n)) atTop
        (𝓝 ((2 - 0) / (1 - 0 + 0 * 0))) :=
      (tendsto_const_nhds.sub hεlim).div
        ((tendsto_const_nhds.sub hεlim).add (hεlim.mul hεlim)) (by norm_num)
    have h2 := ENNReal.tendsto_ofReal hreal
    have := tendsto_nhds_unique hmom h2
    norm_num at this

end NumeraireStability
