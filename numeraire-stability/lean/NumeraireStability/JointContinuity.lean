/-
# Theorem 5.1: joint continuity, compact image, affine slices

(i)  Along any sequence in `K × 𝔸` converging to a point of `K × 𝔸`, the
     laws of `(A_a, B_a)` satisfy (S1)–(S2) and the ratio-tail condition, so
     Theorem 3.3 gives `W_s`-convergence; continuity at a point follows because
     the topology is first countable.
(ii) `K × 𝔸` is sequentially compact, and (i) applies along a convergent
     subsequence.
(iii) Pure algebra of `withDensity` and `map`.
-/
import NumeraireStability.Pushforward

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-! ### The reweighting as a ratio of two affine maps -/

lemma reweight_eq_smul_numerator (P : Measure (ℝ × ℝ)) (hm : 0 < numeraireMean P) :
    reweight P = (ENNReal.ofReal (numeraireMean P))⁻¹ • reweightNumerator P := by
  unfold reweight reweightNumerator
  have e : (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 / numeraireMean P)) =
      (ENNReal.ofReal (numeraireMean P))⁻¹ • fun p : ℝ × ℝ => ENNReal.ofReal p.1 := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_div_of_pos hm, ENNReal.div_eq_inv_mul]
  rw [e, withDensity_smul _ measurable_fst.ennreal_ofReal, Measure.map_smul]
  exact measurable_ratio.aemeasurable

lemma numerator_eq_smul_reweight (P : Measure (ℝ × ℝ)) (hm : 0 < numeraireMean P) :
    reweightNumerator P = ENNReal.ofReal (numeraireMean P) • reweight P := by
  rw [reweight_eq_smul_numerator P hm, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hm).ne' ENNReal.ofReal_ne_top, one_smul]

lemma reweightNumerator_add_smul (c₁ c₂ : ℝ≥0∞) (P₁ P₂ : Measure (ℝ × ℝ)) :
    reweightNumerator (c₁ • P₁ + c₂ • P₂) =
      c₁ • reweightNumerator P₁ + c₂ • reweightNumerator P₂ := by
  unfold reweightNumerator
  rw [withDensity_add_measure, withDensity_smul_measure, withDensity_smul_measure,
    Measure.map_add _ _ measurable_ratio, Measure.map_smul, Measure.map_smul]
  all_goals exact measurable_ratio.aemeasurable

lemma numeraireMean_mix (P₁ P₂ : Measure (ℝ × ℝ)) (h₁ : 0 < numeraireMean P₁)
    (h₂ : 0 < numeraireMean P₂) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    numeraireMean (ENNReal.ofReal t • P₁ + ENNReal.ofReal (1 - t) • P₂) =
      t * numeraireMean P₁ + (1 - t) * numeraireMean P₂ := by
  have i₁ := integrable_fst_of_mean_pos h₁
  have i₂ := integrable_fst_of_mean_pos h₂
  unfold numeraireMean
  rw [integral_add_measure (i₁.smul_measure ENNReal.ofReal_ne_top)
      (i₂.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ht0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

lemma mix_weight_pos {m₁ m₂ t : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < t * m₁ + (1 - t) * m₂ := by
  rcases ht0.lt_or_eq with ht | ht
  · have := mul_pos ht h₁
    have := mul_nonneg (sub_nonneg.2 ht1) h₂.le
    linarith
  · subst ht
    simpa using h₂

lemma ofReal_coeff {W t m : ℝ} (hW : 0 < W) (ht : 0 ≤ t) :
    (ENNReal.ofReal W)⁻¹ * ENNReal.ofReal t * ENNReal.ofReal m =
      ENNReal.ofReal (t * m / W) := by
  rw [mul_assoc, ← ENNReal.ofReal_inv_of_pos hW, ← ENNReal.ofReal_mul ht,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hW.le), div_eq_inv_mul]

/-- The mixture formula for laws of `(A, B)` with positive numéraire means. -/
theorem reweight_mix (P₁ P₂ : Measure (ℝ × ℝ)) (h₁ : 0 < numeraireMean P₁)
    (h₂ : 0 < numeraireMean P₂) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    reweight (ENNReal.ofReal t • P₁ + ENNReal.ofReal (1 - t) • P₂) =
      ENNReal.ofReal (t * numeraireMean P₁ /
          (t * numeraireMean P₁ + (1 - t) * numeraireMean P₂)) • reweight P₁ +
        ENNReal.ofReal ((1 - t) * numeraireMean P₂ /
          (t * numeraireMean P₁ + (1 - t) * numeraireMean P₂)) • reweight P₂ := by
  have hW := mix_weight_pos h₁ h₂ ht0 ht1
  have hmix := numeraireMean_mix P₁ P₂ h₁ h₂ ht0 ht1
  rw [reweight_eq_smul_numerator _ (hmix ▸ hW), hmix, reweightNumerator_add_smul,
    numerator_eq_smul_reweight P₁ h₁, numerator_eq_smul_reweight P₂ h₂, smul_add, smul_smul,
    smul_smul, smul_smul, smul_smul, ofReal_coeff hW ht0,
    ofReal_coeff hW (by linarith : (0 : ℝ) ≤ 1 - t)]

section JointContinuity

variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {𝔸 : Type*} [MetricSpace 𝔸] [CompactSpace 𝔸]
  {F : 𝔸 → Ω → ℝ × ℝ} {K : Set (ProbabilityMeasure Ω)} {s : ℝ}

lemma contractLaw_add_smul (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2) (c₁ c₂ : ℝ≥0∞)
    (Q₁ Q₂ : Measure Ω) (a : 𝔸) :
    contractLaw F (c₁ • Q₁ + c₂ • Q₂) a = c₁ • contractLaw F Q₁ a + c₂ • contractLaw F Q₂ a := by
  unfold contractLaw
  rw [Measure.map_add _ _ (measurable_section hF a), Measure.map_smul, Measure.map_smul]
  all_goals exact (measurable_section hF a).aemeasurable

/-- Theorem 5.1 along sequences: finite `s`-moments and `W_s`-convergence. -/
theorem JointSetting.seq_convergence (h : JointSetting F K s) (hs : 1 ≤ s)
    {y : ℕ → ProbabilityMeasure Ω × 𝔸} {x : ProbabilityMeasure Ω × 𝔸}
    (hy : ∀ n, (y n).1 ∈ K) (hx : x.1 ∈ K) (hlim : Tendsto y atTop (𝓝 x)) :
    HasFiniteMoment s (reweightAt F (x.1 : Measure Ω) x.2) ∧
      (∀ n, HasFiniteMoment s (reweightAt F ((y n).1 : Measure Ω) (y n).2)) ∧
      Tendsto (fun n => wasserstein s (reweightAt F ((y n).1 : Measure Ω) (y n).2)
        (reweightAt F (x.1 : Measure Ω) x.2)) atTop (𝓝 0) := by
  have hS := standing_of_seq h.cont h.pos h.ui h.mean_pos hy hx hlim
  exact ((hS.exact_two_way hs).out 3 1).1 (ratioTail_seq_of_class h.tail hy)

/-- **Theorem 5.1(i).** -/
theorem JointSetting.joint_continuity' (h : JointSetting F K s) (hs : 1 ≤ s) :
    (∀ Q ∈ K, ∀ a, HasFiniteMoment s (reweightAt F (Q : Measure Ω) a)) ∧
    ∀ x ∈ K ×ˢ (Set.univ : Set 𝔸),
      Tendsto (fun y : ProbabilityMeasure Ω × 𝔸 =>
          wasserstein s (reweightAt F (y.1 : Measure Ω) y.2)
            (reweightAt F (x.1 : Measure Ω) x.2))
        (𝓝[K ×ˢ Set.univ] x) (𝓝 0) := by
  refine ⟨fun Q hQ a => ?_, fun x hx => ?_⟩
  · exact (h.seq_convergence hs (y := fun _ => (Q, a)) (x := (Q, a)) (fun _ => hQ) hQ
      tendsto_const_nhds).1
  · have := nhdsWithin_isCountablyGenerated (K ×ˢ (Set.univ : Set 𝔸)) x
    rw [tendsto_iff_seq_tendsto]
    intro u hu
    obtain ⟨v, hvS, hv, huv⟩ := exists_seq_mem_of_tendsto_nhdsWithin hx hu
    refine (h.seq_convergence hs (fun n => (hvS n).1) hx.1 hv).2.2.congr' ?_
    filter_upwards [huv] with n hn
    simp [hn]

/-- **Theorem 5.1(ii).** -/
theorem JointSetting.image_compact' (h : JointSetting F K s) (hs : 1 ≤ s)
    (y : ℕ → ProbabilityMeasure Ω × 𝔸) (hy : ∀ n, (y n).1 ∈ K) :
    ∃ x ∈ K ×ˢ (Set.univ : Set 𝔸), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => wasserstein s (reweightAt F ((y (φ k)).1 : Measure Ω) (y (φ k)).2)
          (reweightAt F (x.1 : Measure Ω) x.2)) atTop (𝓝 0) := by
  obtain ⟨x, hx, φ, hφ, hlim⟩ := (h.compact.prod isCompact_univ).tendsto_subseq
    (x := y) (fun n => ⟨hy n, Set.mem_univ _⟩)
  exact ⟨x, hx, φ, hφ, (h.seq_convergence hs (y := y ∘ φ) (fun k => hy (φ k)) hx.1 hlim).2.2⟩

/-- **Theorem 5.1(iii)**, ratio of two affine maps. -/
theorem JointSetting.reweightAt_projective' (h : JointSetting F K s) (a : 𝔸) :
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
          (1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a)) := by
  refine ⟨fun Q hQ => reweight_eq_smul_numerator _ (mean_pos_of_class h.mean_pos hQ a),
    fun c₁ c₂ Q₁ Q₂ => ?_, fun Q₁ h₁ Q₂ h₂ t ht0 ht1 => ?_⟩
  · rw [contractLaw_add_smul h.cont, reweightNumerator_add_smul]
  · rw [contractLaw_add_smul h.cont]
    exact numeraireMean_mix _ _ (mean_pos_of_class h.mean_pos h₁ a)
      (mean_pos_of_class h.mean_pos h₂ a) ht0 ht1

/-- **Theorem 5.1(iii)**, mixture formula. -/
theorem JointSetting.mixture_formula' (h : JointSetting F K s) {Q₁ Q₂ : ProbabilityMeasure Ω}
    (h₁ : Q₁ ∈ K) (h₂ : Q₂ ∈ K) (a : 𝔸) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    reweightAt F (ENNReal.ofReal t • (Q₁ : Measure Ω) + ENNReal.ofReal (1 - t) • (Q₂ : Measure Ω)) a =
      ENNReal.ofReal (t * numeraireMean (contractLaw F (Q₁ : Measure Ω) a) /
          (t * numeraireMean (contractLaw F (Q₁ : Measure Ω) a) +
            (1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a))) •
          reweightAt F (Q₁ : Measure Ω) a +
        ENNReal.ofReal ((1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a) /
          (t * numeraireMean (contractLaw F (Q₁ : Measure Ω) a) +
            (1 - t) * numeraireMean (contractLaw F (Q₂ : Measure Ω) a))) •
          reweightAt F (Q₂ : Measure Ω) a := by
  unfold reweightAt
  rw [contractLaw_add_smul h.cont]
  exact reweight_mix _ _ (mean_pos_of_class h.mean_pos h₁ a) (mean_pos_of_class h.mean_pos h₂ a)
    ht0 ht1

/-- **Theorem 5.1(iii)**, calibration slices. -/
theorem JointSetting.affine_on_slice' (h : JointSetting F K s) {Q₁ Q₂ : ProbabilityMeasure Ω}
    (h₁ : Q₁ ∈ K) (h₂ : Q₂ ∈ K) (a : 𝔸) {c : ℝ}
    (hc₁ : numeraireMean (contractLaw F (Q₁ : Measure Ω) a) = c)
    (hc₂ : numeraireMean (contractLaw F (Q₂ : Measure Ω) a) = c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    reweightAt F (ENNReal.ofReal t • (Q₁ : Measure Ω) + ENNReal.ofReal (1 - t) • (Q₂ : Measure Ω)) a =
      ENNReal.ofReal t • reweightAt F (Q₁ : Measure Ω) a +
        ENNReal.ofReal (1 - t) • reweightAt F (Q₂ : Measure Ω) a := by
  have hc : 0 < c := hc₁ ▸ mean_pos_of_class h.mean_pos h₁ a
  have hsum : t * c + (1 - t) * c = c := by ring
  rw [h.mixture_formula' h₁ h₂ a ht0 ht1, hc₁, hc₂, hsum, mul_div_cancel_right₀ _ hc.ne',
    mul_div_cancel_right₀ _ hc.ne']

end JointContinuity

/-! ### Non-vacuity -/

section Example

/-- The contract of the non-vacuity example: `(A_a(ω), B_a(ω)) = (1 + a, sin ω)`. -/
abbrev exContract : Set.Icc (0 : ℝ) 1 → ℝ → ℝ × ℝ :=
  fun a ω => (1 + (a : ℝ), Real.sin ω)

lemma exContract_continuous :
    Continuous fun x : Set.Icc (0 : ℝ) 1 × ℝ => exContract x.1 x.2 := by
  unfold exContract
  fun_prop

lemma exContract_pos (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) : 0 < (exContract a ω).1 := by
  have := a.2.1
  linarith

lemma exContract_fst_le (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) : (exContract a ω).1 ≤ 2 := by
  have := a.2.2
  linarith

lemma exContract_snd_le (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) : |(exContract a ω).2| ≤ 1 :=
  Real.abs_sin_le_one ω

/-- A set of `(a, b)`-values that the example contract never enters is null. -/
lemma exContract_null (Q : Measure ℝ) (a : Set.Icc (0 : ℝ) 1) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hout : ∀ ω, exContract a ω ∉ S) :
    contractLaw exContract Q a S = 0 := by
  rw [contractLaw_apply exContract_continuous Q a hS]
  have : exContract a ⁻¹' S = ∅ := by
    ext ω
    simpa using hout ω
  rw [this, measure_empty]

lemma exContract_mean (Q : ProbabilityMeasure ℝ) (a : Set.Icc (0 : ℝ) 1) :
    numeraireMean (contractLaw exContract (Q : Measure ℝ) a) = 1 + (a : ℝ) := by
  unfold numeraireMean contractLaw
  rw [integral_map (measurable_section exContract_continuous a).aemeasurable
    measurable_fst.aestronglyMeasurable]
  simp

theorem jointSetting_example' {s : ℝ} :
    JointSetting (fun (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) => (1 + (a : ℝ), Real.sin ω))
      (diracProba '' Set.Icc (0 : ℝ) 1) s where
  compact := isCompact_Icc.image continuous_diracProba
  cont := exContract_continuous
  pos := exContract_pos
  tail := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    refine (le_antisymm (iSup_le fun z => ?_) zero_le).symm
    refine (setLIntegral_measure_zero _ _ ?_).le
    refine exContract_null _ z.2 (measurableSet_lt (measurable_const.mul measurable_fst)
      (continuous_abs.measurable.comp measurable_snd)) fun ω hω => ?_
    have h1 := exContract_snd_le z.2 ω
    have h2 : 1 ≤ (exContract z.2 ω).1 := by
      have := z.2.2.1
      linarith
    have : R * (exContract z.2 ω).1 < |(exContract z.2 ω).2| := hω
    nlinarith
  ui := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with M hM
    refine (le_antisymm (iSup_le fun z => ?_) zero_le).symm
    refine (setLIntegral_measure_zero _ _ ?_).le
    refine exContract_null _ z.2 (measurableSet_lt measurable_const
      measurable_fst.ennreal_ofReal) fun ω hω => ?_
    have h1 := exContract_fst_le z.2 ω
    have : ENNReal.ofReal M < ENNReal.ofReal (exContract z.2 ω).1 := hω
    rw [ENNReal.ofReal_lt_ofReal_iff'] at this
    linarith [this.1]
  mean_pos := ⟨1, one_pos, fun z => by
    rw [exContract_mean]
    linarith [z.2.2.1]⟩

end Example

end NumeraireStability
