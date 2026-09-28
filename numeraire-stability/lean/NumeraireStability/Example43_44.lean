/-
# Examples 4.3 and 4.4
-/
import NumeraireStability.Example41

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-! ## Example 4.3 -/

section Ex43

variable {ε : ℝ} {α : ℕ → ℝ}

lemma exBoundaryMass_eq (ε a : ℝ) : exBoundaryMass ε a = twoAtoms (1 - ε) ε (1, 0) (a, 1) := rfl

lemma exBoundaryMass_mean (hε : 0 < ε ∧ ε < 1) {a : ℝ} (ha : 0 ≤ a) :
    numeraireMean (exBoundaryMass ε a) = 1 - ε + ε * a := by
  rw [exBoundaryMass_eq, numeraireMean_twoAtoms (by linarith [hε.2]) hε.1.le zero_le_one ha]
  ring

lemma exBoundaryMass_mean_pos (hε : 0 < ε ∧ ε < 1) {a : ℝ} (ha : 0 ≤ a) :
    0 < numeraireMean (exBoundaryMass ε a) := by
  rw [exBoundaryMass_mean hε ha]
  nlinarith [hε.1, hε.2]

lemma standing_exBoundaryMass (hε : 0 < ε ∧ ε < 1) (hα : ∀ n, 0 < α n)
    (hαlim : Tendsto α atTop (𝓝 0)) :
    StandingSetting (fun n => exBoundaryMass ε (α n)) (exBoundaryMass ε 0) where
  prob n := isProbabilityMeasure_twoAtoms (by linarith [hε.2]) hε.1.le (by ring) _ _
  prob_lim := isProbabilityMeasure_twoAtoms (by linarith [hε.2]) hε.1.le (by ring) _ _
  pos n := twoAtoms_null _ _ _ _ (fun h => absurd (show (1 : ℝ) ≤ 0 from h) (by norm_num))
    (fun h => absurd (show α n ≤ 0 from h) (not_le.2 (hα n)))
  lim_supp := twoAtoms_null _ _ _ _ (fun h => absurd (show (1 : ℝ) < 0 from h) (by norm_num))
    (fun h => absurd (show (0 : ℝ) < 0 from h) (lt_irrefl 0))
  weak := by
    intro f
    have e : (fun n => ∫ p, f p ∂(exBoundaryMass ε (α n))) = fun n =>
        (1 - ε) * f (1, 0) + ε * f (α n, 1) :=
      funext fun n => integral_twoAtoms f (by linarith [hε.2]) hε.1.le _ _
    rw [e, exBoundaryMass_eq, integral_twoAtoms f (by linarith [hε.2]) hε.1.le]
    have hf : Tendsto (fun n => f (α n, 1)) atTop (𝓝 (f (0, 1))) :=
      (f.continuous.tendsto _).comp (hαlim.prodMk_nhds tendsto_const_nhds)
    exact tendsto_const_nhds.add (hf.const_mul ε)
  ui := by
    obtain ⟨C, hC⟩ := hαlim.bddAbove_range
    show Tendsto (fun M : ℝ => ⨆ n, ∫⁻ p in {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal p.1},
      ENNReal.ofReal p.1 ∂(exBoundaryMass ε (α n))) atTop (𝓝 0)
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop (max C 1)).mono fun M hM => ?_)
    refine (le_antisymm (iSup_le fun n => le_of_eq (setLIntegral_measure_zero _ _ ?_))
      zero_le).symm
    exact twoAtoms_null _ _ _ _
      (fun h => absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal
        (show (1 : ℝ) ≤ M from (le_max_right _ _).trans hM))))
      (fun h => absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal
        (show α n ≤ M from (hC ⟨n, rfl⟩).trans ((le_max_left _ _).trans hM)))))
  mean_pos := exBoundaryMass_mean_pos hε le_rfl

lemma reweight_exBoundaryMass_zero (hε : 0 < ε ∧ ε < 1) :
    reweight (exBoundaryMass ε 0) = Measure.dirac 0 := by
  have hm : numeraireMean (exBoundaryMass ε 0) = 1 - ε := by
    rw [exBoundaryMass_mean hε le_rfl]
    ring
  have h1 : (1 - ε) * (1 / (1 - ε)) = 1 := by
    field_simp [show (1 - ε) ≠ 0 by linarith [hε.2]]
  rw [exBoundaryMass_eq, reweight_twoAtoms (by linarith [hε.2]) hε.1.le]
  simp only [twoAtoms]
  rw [show numeraireMean (twoAtoms (1 - ε) ε ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) = 1 - ε
    from hm, h1]
  simp

lemma reweight_exBoundaryMass (hε : 0 < ε ∧ ε < 1) {a : ℝ} (ha : 0 < a) :
    reweight (exBoundaryMass ε a) =
      twoAtoms ((1 - ε) / numeraireMean (exBoundaryMass ε a))
        (ε * a / numeraireMean (exBoundaryMass ε a)) 0 (1 / a) := by
  rw [exBoundaryMass_eq, reweight_twoAtoms (by linarith [hε.2]) hε.1.le]
  simp only [twoAtoms, zero_div, mul_one_div, mul_div_assoc]

lemma exBoundaryMass_first_moment (hε : 0 < ε ∧ ε < 1) {a : ℝ} (ha : 0 < a) :
    ∫⁻ z, ENNReal.ofReal |z| ∂(reweight (exBoundaryMass ε a)) =
      ENNReal.ofReal (ε / numeraireMean (exBoundaryMass ε a)) := by
  have hm := exBoundaryMass_mean_pos hε ha.le
  rw [reweight_exBoundaryMass hε ha, lintegral_twoAtoms, abs_zero, ENNReal.ofReal_zero, mul_zero,
    zero_add, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hε.1.le ha.le) hm.le)]
  congr 1
  rw [abs_of_pos (one_div_pos.2 ha)]
  field_simp

/-- **Example 4.3.** -/
theorem example_4_3' (hε : 0 < ε ∧ ε < 1) (hα : ∀ n, 0 < α n)
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
  have hst := standing_exBoundaryMass hε hα hαlim
  have hmn : ∀ n, 0 < numeraireMean (exBoundaryMass ε (α n)) := fun n =>
    exBoundaryMass_mean_pos hε (hα n).le
  have hmlim : Tendsto (fun n => numeraireMean (exBoundaryMass ε (α n))) atTop (𝓝 (1 - ε)) := by
    have e : (fun n => numeraireMean (exBoundaryMass ε (α n))) = fun n => 1 - ε + ε * α n :=
      funext fun n => exBoundaryMass_mean hε (hα n).le
    rw [e]
    have h := (tendsto_const_nhds (x := 1 - ε)).add (hαlim.const_mul ε)
    rwa [mul_zero, add_zero] at h
  have h1ε : (1 - ε) ≠ 0 := by linarith [hε.2]
  have hmom : Tendsto (fun n => ∫⁻ z, ENNReal.ofReal |z| ∂(reweight (exBoundaryMass ε (α n))))
      atTop (𝓝 (ENNReal.ofReal (ε / (1 - ε)))) := by
    have e : (fun n => ∫⁻ z, ENNReal.ofReal |z| ∂(reweight (exBoundaryMass ε (α n)))) =
        fun n => ENNReal.ofReal (ε / numeraireMean (exBoundaryMass ε (α n))) :=
      funext fun n => exBoundaryMass_first_moment hε (hα n)
    rw [e]
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.div hmlim h1ε)
  have hW : ¬ Tendsto (fun n => wasserstein 1 (reweight (exBoundaryMass ε (α n)))
      (Measure.dirac 0)) atTop (𝓝 0) := by
    intro hW0
    have e : (fun n => wasserstein 1 (reweight (exBoundaryMass ε (α n))) (Measure.dirac 0)) =
        fun n => ∫⁻ z, ENNReal.ofReal |z| ∂(reweight (exBoundaryMass ε (α n))) := by
      funext n
      have := hst.isProbabilityMeasure_reweight_n n
      rw [wasserstein_dirac_zero 1 le_rfl, div_one, ENNReal.rpow_one, moment]
      simp only [Real.rpow_one]
    rw [e] at hW0
    have hpos : ENNReal.ofReal (ε / (1 - ε)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (div_pos hε.1 (by linarith [hε.2]))).ne'
    exact hpos (tendsto_nhds_unique hmom hW0)
  refine ⟨hst, ?_, ?_, ?_, reweight_exBoundaryMass_zero hε, ?_, hmom, hW, ?_⟩
  · rw [exBoundaryMass_eq, twoAtoms_apply,
      Set.indicator_of_notMem (show ((1 : ℝ), (0 : ℝ)) ∉ {p : ℝ × ℝ | p.1 = 0} from by
        simp),
      Set.indicator_of_mem (show ((0 : ℝ), (1 : ℝ)) ∈ {p : ℝ × ℝ | p.1 = 0} from rfl)]
    simpa using hε.1
  · rw [exBoundaryMass_mean hε le_rfl]
    ring
  · show Tendsto (fun M : ℝ => ⨆ n, ∫⁻ p in {p : ℝ × ℝ | ENNReal.ofReal M <
      ENNReal.ofReal |p.2|}, ENNReal.ofReal |p.2| ∂(exBoundaryMass ε (α n))) atTop (𝓝 0)
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun M hM => ?_)
    refine (le_antisymm (iSup_le fun n => le_of_eq (setLIntegral_measure_zero _ _ ?_))
      zero_le).symm
    exact twoAtoms_null _ _ _ _
      (fun h => absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal (by simp; linarith))))
      (fun h => absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal (by simp; linarith))))
  · intro f
    have hc2nn : ∀ n, 0 ≤ ε * α n / numeraireMean (exBoundaryMass ε (α n)) := fun n =>
      div_nonneg (mul_nonneg hε.1.le (hα n).le) (hmn n).le
    have e : (fun n => ∫ z, f z ∂(reweight (exBoundaryMass ε (α n)))) = fun n =>
        (1 - ε) / numeraireMean (exBoundaryMass ε (α n)) * f 0 +
          ε * α n / numeraireMean (exBoundaryMass ε (α n)) * f (1 / α n) := funext fun n => by
      rw [reweight_exBoundaryMass hε (hα n)]
      exact integral_twoAtoms f (div_nonneg (by linarith [hε.2]) (hmn n).le) (hc2nn n) _ _
    rw [e, integral_dirac]
    have hc1 : Tendsto (fun n => (1 - ε) / numeraireMean (exBoundaryMass ε (α n))) atTop
        (𝓝 1) := by
      have h := (tendsto_const_nhds (x := 1 - ε)).div hmlim h1ε
      rwa [div_self h1ε] at h
    have hc2 : Tendsto (fun n => ε * α n / numeraireMean (exBoundaryMass ε (α n))) atTop
        (𝓝 0) := by
      have h := (hαlim.const_mul ε).div hmlim h1ε
      rwa [mul_zero, zero_div] at h
    have t1 : Tendsto (fun n => (1 - ε) / numeraireMean (exBoundaryMass ε (α n)) * f 0) atTop
        (𝓝 (f 0)) := by
      have h := hc1.mul_const (f 0)
      rwa [one_mul] at h
    have t2 : Tendsto (fun n => ε * α n / numeraireMean (exBoundaryMass ε (α n)) *
        f (1 / α n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by have h := hc2.mul_const ‖f‖; rwa [zero_mul] at h)
      rw [norm_mul, Real.norm_of_nonneg (hc2nn n)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (1 / α n)) (hc2nn n)
    have h := t1.add t2
    rwa [add_zero] at h
  · intro h3
    obtain ⟨-, -, hW1⟩ := ((hst.exact_two_way (s := 1) le_rfl).out 3 1).1 h3
    rw [reweight_exBoundaryMass_zero hε] at hW1
    exact hW hW1

end Ex43

/-! ## Example 4.4 -/

section Ex44

variable {ε : ℕ → ℝ}

lemma exNoUnifIntegrable_eq (e : ℝ) :
    exNoUnifIntegrable e = twoAtoms (1 - e) e (1, 0) (1 / e, 1 / e) := rfl

lemma exNoUnifIntegrable_mean {e : ℝ} (he : 0 < e ∧ e < 1) :
    numeraireMean (exNoUnifIntegrable e) = 2 - e := by
  have he0 : e ≠ 0 := he.1.ne'
  rw [exNoUnifIntegrable_eq, numeraireMean_twoAtoms (by linarith [he.2]) he.1.le zero_le_one
    (one_div_pos.2 he.1).le]
  field_simp
  ring

lemma two_inv_eq : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos]
  simp

/-- **Example 4.4.** -/
theorem example_4_4' (hε : ∀ n, 0 < ε n ∧ ε n < 1) (hεlim : Tendsto ε atTop (𝓝 0)) :
    WeakConv (fun n => exNoUnifIntegrable (ε n)) (Measure.dirac (1, 0)) ∧
    ¬ UnifIntegrableFamily (fun n => exNoUnifIntegrable (ε n)) (fun p => ENNReal.ofReal p.1) ∧
    Tendsto (fun n => numeraireMean (exNoUnifIntegrable (ε n))) atTop (𝓝 2) ∧
    reweight (Measure.dirac ((1 : ℝ), (0 : ℝ))) = Measure.dirac 0 ∧
    WeakConv (fun n => reweight (exNoUnifIntegrable (ε n)))
      ((2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1) ∧
    ¬ WeakConv (fun n => reweight (exNoUnifIntegrable (ε n))) (Measure.dirac 0) := by
  have hmean : ∀ n, numeraireMean (exNoUnifIntegrable (ε n)) = 2 - ε n := fun n =>
    exNoUnifIntegrable_mean (hε n)
  have hmlim : Tendsto (fun n => numeraireMean (exNoUnifIntegrable (ε n))) atTop (𝓝 2) := by
    rw [funext hmean]
    have h := (tendsto_const_nhds (x := (2 : ℝ))).sub hεlim
    rwa [sub_zero] at h
  have hmpos : ∀ n, 0 < 2 - ε n := fun n => by linarith [(hε n).2]
  -- the reweighted laws
  have hΓ : ∀ n, reweight (exNoUnifIntegrable (ε n)) =
      twoAtoms ((1 - ε n) / (2 - ε n)) (1 / (2 - ε n)) 0 1 := fun n => by
    rw [exNoUnifIntegrable_eq, reweight_twoAtoms (by linarith [(hε n).2]) (hε n).1.le,
      ← exNoUnifIntegrable_eq, hmean n]
    have hε0 : ε n ≠ 0 := (hε n).1.ne'
    congr 1
    · field_simp
    · field_simp
    · simp
    · field_simp
  -- the integral of a bounded continuous function along `Γ_n`
  have hint : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ z, f z ∂(reweight (exNoUnifIntegrable (ε n))))
      atTop (𝓝 (1 / 2 * f 0 + 1 / 2 * f 1)) := by
    intro f
    have e : (fun n => ∫ z, f z ∂(reweight (exNoUnifIntegrable (ε n)))) = fun n =>
        (1 - ε n) / (2 - ε n) * f 0 + 1 / (2 - ε n) * f 1 := funext fun n => by
      rw [hΓ n]
      exact integral_twoAtoms f (div_nonneg (by linarith [(hε n).2]) (hmpos n).le)
        (one_div_pos.2 (hmpos n)).le _ _
    rw [e]
    have h2 : Tendsto (fun n => 2 - ε n) atTop (𝓝 2) := by
      have h := (tendsto_const_nhds (x := (2 : ℝ))).sub hεlim
      rwa [sub_zero] at h
    have hc1 : Tendsto (fun n => (1 - ε n) / (2 - ε n)) atTop (𝓝 (1 / 2)) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hεlim).div h2 two_ne_zero
      rwa [sub_zero] at h
    have hc2 : Tendsto (fun n => 1 / (2 - ε n)) atTop (𝓝 (1 / 2)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div h2 two_ne_zero
    exact (hc1.mul_const (f 0)).add (hc2.mul_const (f 1))
  refine ⟨?_, ?_, hmlim, reweight_dirac_one_zero, ?_, ?_⟩
  · intro f
    have e : (fun n => ∫ p, f p ∂(exNoUnifIntegrable (ε n))) = fun n =>
        (1 - ε n) * f (1, 0) + ε n * f (1 / ε n, 1 / ε n) :=
      funext fun n => integral_twoAtoms f (by linarith [(hε n).2]) (hε n).1.le _ _
    rw [e, integral_dirac]
    have h1 : Tendsto (fun n => (1 - ε n) * f (1, 0)) atTop (𝓝 (f (1, 0))) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hεlim).mul_const (f (1, 0))
      rwa [sub_zero, one_mul] at h
    have h2 : Tendsto (fun n => ε n * f (1 / ε n, 1 / ε n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by have h := hεlim.mul_const ‖f‖; rwa [zero_mul] at h)
      rw [norm_mul, Real.norm_of_nonneg (hε n).1.le]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hε n).1.le
    have h := h1.add h2
    rwa [add_zero] at h
  · intro hU
    have hU' : Tendsto (fun M : ℝ => ⨆ n, ∫⁻ p in {p : ℝ × ℝ | ENNReal.ofReal M <
        ENNReal.ofReal p.1}, ENNReal.ofReal p.1 ∂(exNoUnifIntegrable (ε n))) atTop (𝓝 0) := hU
    obtain ⟨M, hM, hM0⟩ := ((hU'.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from
      zero_lt_one))).and (eventually_gt_atTop 0)).exists
    -- some `ε n < 1/M`, so the escaping atom `1/ε n > M` carries mass `ε n · (1/ε n) = 1`
    obtain ⟨n, hn⟩ := ((hεlim.eventually (gt_mem_nhds (one_div_pos.2 hM0))).exists)
    have hbig : M < 1 / ε n := by
      rw [lt_one_div hM0 (hε n).1]
      exact hn
    have hS : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal p.1} :=
      measurableSet_lt measurable_const measurable_fst.ennreal_ofReal
    have hmem : ((1 / ε n), (1 / ε n)) ∈ {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal p.1} :=
      (ENNReal.ofReal_lt_ofReal_iff (one_div_pos.2 (hε n).1)).2 hbig
    have hge : (1 : ℝ≥0∞) ≤ ∫⁻ p in {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal p.1},
        ENNReal.ofReal p.1 ∂(exNoUnifIntegrable (ε n)) := by
      rw [← lintegral_indicator hS, exNoUnifIntegrable_eq, lintegral_twoAtoms,
        Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul (hε n).1.le,
        mul_one_div_cancel (hε n).1.ne', ENNReal.ofReal_one]
      exact le_add_self
    exact absurd (hge.trans (le_iSup (fun n => ∫⁻ p in {p : ℝ × ℝ | ENNReal.ofReal M <
      ENNReal.ofReal p.1}, ENNReal.ofReal p.1 ∂(exNoUnifIntegrable (ε n))) n)) (not_le.2 hM)
  · intro f
    rw [two_inv_eq]
    change Tendsto _ atTop (𝓝 (∫ z, f z ∂(twoAtoms (1 / 2) (1 / 2) 0 1)))
    rw [integral_twoAtoms f (by norm_num) (by norm_num)]
    exact hint f
  · intro hw
    -- a bounded continuous function with `f 0 = 0` and `f 1 = 1`
    let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
      ⟨fun z => min |z| 1, by fun_prop⟩ 1 (by
        intro x y
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have h1 : 0 ≤ min |x| 1 := le_min (abs_nonneg _) zero_le_one
        have h2 : min |x| 1 ≤ 1 := min_le_right _ _
        have h3 : 0 ≤ min |y| 1 := le_min (abs_nonneg _) zero_le_one
        have h4 : min |y| 1 ≤ 1 := min_le_right _ _
        rw [abs_le]
        constructor <;> linarith)
    have hf0 : f 0 = 0 := by simp [f]
    have hf1 : f 1 = 1 := by simp [f]
    have h1 := hint f
    have h2 := hw f
    rw [integral_dirac, hf0] at h2
    rw [hf0, hf1] at h1
    have := tendsto_nhds_unique h1 h2
    norm_num at this

end Ex44

end NumeraireStability
