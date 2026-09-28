/-
# Section 6.2: annuity-measure swap-rate marginals

* Uniform integrability of the annuities and floating legs, positive
  normalization and compactness give the uniform ratio-tail condition at
  `s = 1`: the legs are split at a level `M`, and `sup Q(A_a ≤ δ) → 0` by a
  compactness argument (portmanteau on the closed sets `{a ≤ δ}`).
* `|∫ f dμ - ∫ f dν| ≤ W_1(μ, ν)` for 1-Lipschitz `f` turns joint
  `W_1`-continuity into uniform convergence of normalized call-price curves,
  and hence of physically settled prices on bounded strike sets.
-/
import NumeraireStability.JointContinuity
import NumeraireStability.Example41

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

/-! ### Bounded annuities are uniformly integrable -/

theorem unifIntegrableOn_of_bounded' {ι : Type*} (L : ι → Measure (ℝ × ℝ)) (C : ℝ)
    (hC : ∀ i, ∀ᵐ p ∂(L i), p.1 ≤ C) :
    UnifIntegrableOn L fun p => ENNReal.ofReal p.1 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (max C 0)] with M hM
  refine (le_antisymm (iSup_le fun i => ?_) zero_le).symm
  refine (setLIntegral_measure_zero _ _ ?_).le
  have hnull : L i {p : ℝ × ℝ | C < p.1} = 0 :=
    measure_eq_zero_iff_ae_notMem.2 ((hC i).mono fun p hp => not_lt.2 hp)
  refine measure_mono_null (fun p (hp : ENNReal.ofReal M < ENNReal.ofReal p.1) => ?_) hnull
  have := (ENNReal.ofReal_lt_ofReal_iff'.1 hp).1
  show C < p.1
  linarith [le_max_left C 0]

/-! ### `W_1` controls Lipschitz integrals -/

lemma integrable_of_hasFiniteMoment_one {μ : Measure ℝ} (hμ : HasFiniteMoment 1 μ) :
    Integrable (fun x : ℝ => x) μ := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa [HasFiniteMoment, Real.norm_eq_abs] using hμ

lemma integrable_of_lipschitz {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : HasFiniteMoment 1 μ)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) : Integrable f μ := by
  refine ((integrable_of_hasFiniteMoment_one hμ).abs.add (integrable_const |f 0|)).mono'
    hf.continuous.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h := hf.dist_le_mul x 0
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_zero] at h
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (f x) (f 0)
  linarith

/-- `|∫ f dμ - ∫ f dν| ≤ W_1(μ, ν)` for 1-Lipschitz `f`. -/
theorem abs_integral_sub_le_wasserstein_one (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : HasFiniteMoment 1 μ) (hν : HasFiniteMoment 1 ν)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ wasserstein 1 μ ν := by
  rw [wasserstein, div_one, ENNReal.rpow_one]
  refine le_iInf₂ fun π hπ => ?_
  have hfμ := integrable_of_lipschitz hμ hf
  have hfν := integrable_of_lipschitz hν hf
  have hxμ := integrable_of_hasFiniteMoment_one hμ
  have hxν := integrable_of_hasFiniteMoment_one hν
  rw [← hπ.1] at hfμ hxμ
  rw [← hπ.2] at hfν hxν
  have h1 : Integrable (fun p : ℝ × ℝ => f p.1) π :=
    (integrable_map_measure hf.continuous.aestronglyMeasurable
      measurable_fst.aemeasurable).1 hfμ
  have h2 : Integrable (fun p : ℝ × ℝ => f p.2) π :=
    (integrable_map_measure hf.continuous.aestronglyMeasurable
      measurable_snd.aemeasurable).1 hfν
  have g1 : Integrable (fun p : ℝ × ℝ => p.1) π :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).1 hxμ
  have g2 : Integrable (fun p : ℝ × ℝ => p.2) π :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).1 hxν
  have e1 : ∫ x, f x ∂μ = ∫ p, f p.1 ∂π := by
    rw [← hπ.1, integral_map measurable_fst.aemeasurable hf.continuous.aestronglyMeasurable]
  have e2 : ∫ x, f x ∂ν = ∫ p, f p.2 ∂π := by
    rw [← hπ.2, integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable]
  have hd : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) π := (g1.sub g2).abs
  rw [e1, e2, ← integral_sub h1 h2]
  calc ENNReal.ofReal |∫ p, (f p.1 - f p.2) ∂π|
      ≤ ENNReal.ofReal (∫ p, |p.1 - p.2| ∂π) := by
        refine ENNReal.ofReal_le_ofReal ((abs_integral_le_integral_abs).trans ?_)
        refine integral_mono (h1.sub h2).abs hd fun p => ?_
        have := hf.dist_le_mul p.1 p.2
        simpa [Real.dist_eq] using this
    _ = ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| ^ (1 : ℝ)) ∂π := by
        rw [ofReal_integral_eq_lintegral_ofReal hd (ae_of_all _ fun p => abs_nonneg _)]
        simp

lemma lipschitz_call (k : ℝ) : LipschitzWith 1 fun z : ℝ => max (z - k) 0 := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
  rw [sub_sub_sub_cancel_right]

theorem abs_normCall_sub_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasFiniteMoment 1 μ) (hν : HasFiniteMoment 1 ν) (k : ℝ) :
    ENNReal.ofReal |normCall μ k - normCall ν k| ≤ wasserstein 1 μ ν :=
  abs_integral_sub_le_wasserstein_one μ ν hμ hν (lipschitz_call k)

lemma normCall_nonneg (μ : Measure ℝ) (k : ℝ) : 0 ≤ normCall μ k :=
  integral_nonneg fun _ => le_max_right _ _

lemma normCall_anti (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : HasFiniteMoment 1 μ)
    {k k' : ℝ} (hk : k' ≤ k) : normCall μ k ≤ normCall μ k' :=
  integral_mono (integrable_of_lipschitz hμ (lipschitz_call k))
    (integrable_of_lipschitz hμ (lipschitz_call k')) fun z =>
      max_le_max (by linarith) le_rfl

/-! ### Physically settled prices -/

lemma payerPrice_eq {Ω 𝔸 : Type*} [MeasurableSpace Ω] {F : 𝔸 → Ω → ℝ × ℝ} (Q : Measure Ω)
    (a : 𝔸) (hF : Measurable (F a)) (hpos : contractLaw F Q a {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean (contractLaw F Q a)) (k : ℝ) :
    payerPrice F Q a k = numeraireMean (contractLaw F Q a) * normCall (reweightAt F Q a) k := by
  set P := contractLaw F Q a
  have hg : Measurable fun p : ℝ × ℝ => max (p.2 - k * p.1) 0 := by fun_prop
  have hP : payerPrice F Q a k = (∫⁻ p, ENNReal.ofReal (max (p.2 - k * p.1) 0) ∂P).toReal := by
    rw [payerPrice, ← integral_map hF.aemeasurable hg.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (f := fun p : ℝ × ℝ => max (p.2 - k * p.1) 0)
        (ae_of_all _ fun _ => le_max_right _ _) hg.aestronglyMeasurable]
    rfl
  have hC : normCall (reweightAt F Q a) k =
      ((∫⁻ p, ENNReal.ofReal (max (p.2 - k * p.1) 0) ∂P) / ENNReal.ofReal (numeraireMean P)).toReal := by
    rw [normCall, integral_eq_lintegral_of_nonneg_ae (f := fun z : ℝ => max (z - k) 0)
      (ae_of_all _ fun _ => le_max_right _ _) (by fun_prop), reweightAt,
      lintegral_reweight P hm _ (by fun_prop)]
    congr 2
    refine lintegral_congr_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
    have h : p.1 * max (p.2 / p.1 - k) 0 = max (p.2 - k * p.1) 0 := by
      rw [mul_max_of_nonneg _ _ hp.le, mul_zero]
      congr 1
      field_simp
    dsimp only
    rw [← ENNReal.ofReal_mul hp.le, h]
  rw [hP, hC, ENNReal.toReal_div, ENNReal.toReal_ofReal hm.le, mul_div_cancel₀ _ hm.ne']

section Annuity

variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {𝔸 : Type*} [MetricSpace 𝔸] [CompactSpace 𝔸]
  {F : 𝔸 → Ω → ℝ × ℝ} {K : Set (ProbabilityMeasure Ω)}

/-! ### `sup Q(A_a ≤ δ) → 0` by compactness -/

theorem uniform_small_measure (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2)
    (hpos : ∀ a ω, 0 < (F a ω).1) (hK : IsCompact K) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : K × 𝔸, contractLaw F (z.1 : Measure Ω) z.2 {p | p.1 ≤ δ} ≤ η := by
  by_contra hcon
  push Not at hcon
  choose z hz using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  set y : ℕ → ProbabilityMeasure Ω × 𝔸 := fun k => (((z k).1 : ProbabilityMeasure Ω), (z k).2)
  obtain ⟨x, hx, φ, hφ, hlim⟩ := (hK.prod isCompact_univ).tendsto_subseq (x := y)
    (fun k => ⟨(z k).1.2, mem_univ _⟩)
  have hconv : Tendsto (fun k => lawMap F (y (φ k))) atTop (𝓝 (lawMap F x)) :=
    ((continuous_lawMap hF).tendsto x).comp hlim
  set C : ℕ → Set (ℝ × ℝ) := fun j => {p | p.1 ≤ 1 / ((j : ℝ) + 1)}
  have hCmeas : ∀ j, MeasurableSet (C j) := fun j => measurableSet_le measurable_fst measurable_const
  have hj : ∀ j, η ≤ contractLaw F (x.1 : Measure Ω) x.2 (C j) := by
    intro j
    have hps := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
      (isClosed_le continuous_fst continuous_const : IsClosed (C j))
    simp only [lawMap_toMeasure] at hps
    refine le_trans ?_ hps
    refine le_limsup_of_frequently_le (Eventually.frequently ?_)
    filter_upwards [eventually_ge_atTop j] with k hk
    have hkφ : j ≤ φ k := hk.trans (hφ.id_le k)
    have hsub : {p : ℝ × ℝ | p.1 ≤ 1 / ((φ k : ℝ) + 1)} ⊆ C j := fun p hp => by
      have : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkφ 1)
      exact (show p.1 ≤ 1 / ((φ k : ℝ) + 1) from hp).trans this
    exact (hz (φ k)).le.trans (measure_mono hsub)
  have hanti : Antitone C := fun i j hij p hp => by
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    exact (show p.1 ≤ 1 / ((j : ℝ) + 1) from hp).trans this
  have hinter : (⋂ j, C j) = {p : ℝ × ℝ | p.1 ≤ 0} := by
    ext p
    simp only [mem_iInter, mem_ofPred_eq, C]
    constructor
    · intro h
      by_contra hp
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (not_le.1 hp)
      linarith [h j]
    · intro hp j
      exact hp.trans (by positivity)
  have := isProbabilityMeasure_contractLaw F x.1 x.2
  have htend := tendsto_measure_iInter_atTop (μ := contractLaw F (x.1 : Measure Ω) x.2)
    (fun j => (hCmeas j).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, contractLaw_nonpos_null hF hpos] at htend
  have : η ≤ 0 := ge_of_tendsto htend (Eventually.of_forall hj)
  exact absurd hη (not_lt.2 this)

/-! ### The ratio-tail condition at `s = 1` -/

lemma tail_split_le (P : Measure (ℝ × ℝ)) {R M δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hRM : M / δ ≤ R) (hM : 0 ≤ M) :
    ∫⁻ p in {p | R * p.1 < |p.2|}, ENNReal.ofReal |p.2| ∂P ≤
      ∫⁻ p in {p | ENNReal.ofReal M < ENNReal.ofReal |p.2|}, ENNReal.ofReal |p.2| ∂P +
        ENNReal.ofReal M * P {p | p.1 ≤ δ} := by
  have hS1 : MeasurableSet {p : ℝ × ℝ | R * p.1 < |p.2|} :=
    measurableSet_lt (measurable_const.mul measurable_fst)
      (continuous_abs.measurable.comp measurable_snd)
  have hS2 : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal |p.2|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp measurable_snd).ennreal_ofReal
  have hS3 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ δ} := measurableSet_le measurable_fst measurable_const
  have hf : Measurable fun p : ℝ × ℝ => ENNReal.ofReal |p.2| :=
    (continuous_abs.measurable.comp measurable_snd).ennreal_ofReal
  rw [← lintegral_indicator hS1, ← lintegral_indicator hS2, ← lintegral_indicator_const hS3,
    ← lintegral_add_left (hf.indicator hS2)]
  refine lintegral_mono fun p => ?_
  by_cases hb : M < |p.2|
  · have hmem : p ∈ {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal |p.2|} :=
      (ENNReal.ofReal_lt_ofReal_iff (hM.trans_lt hb)).2 hb
    rw [indicator_of_mem hmem]
    exact (indicator_le_self _ _ p).trans le_self_add
  · by_cases h1 : p ∈ {p : ℝ × ℝ | R * p.1 < |p.2|}
    · have hle : p.1 ≤ δ := by
        have h1' : R * p.1 < |p.2| := h1
        have hMR : M ≤ R * δ := by rwa [div_le_iff₀ hδ] at hRM
        nlinarith [not_lt.1 hb]
      rw [indicator_of_mem h1, indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 ≤ δ} from hle)]
      exact (ENNReal.ofReal_le_ofReal (not_lt.1 hb)).trans le_add_self
    · rw [indicator_of_notMem h1]
      exact zero_le

theorem AnnuitySetting.ratioTail' (h : AnnuitySetting F K) :
    Tendsto (ratioTailOn 1 fun x : K × 𝔸 => contractLaw F (x.1 : Measure Ω) x.2)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨M, hM, hM1⟩ := ((h.ui_leg.eventually (ge_mem_nhds hε2)).and
    (eventually_ge_atTop (1 : ℝ))).exists
  have hMpos : 0 < M := by linarith
  have hη : 0 < ε / 2 / ENNReal.ofReal M := ENNReal.div_pos hε2.ne' ENNReal.ofReal_ne_top
  obtain ⟨δ, hδ, hδb⟩ := uniform_small_measure h.cont h.pos h.compact hη
  filter_upwards [eventually_ge_atTop (M / δ), eventually_gt_atTop (0 : ℝ)] with R hR hR0
  refine iSup_le fun z => ?_
  rw [boundaryFamily_one]
  calc ∫⁻ p in {p | R * p.1 < |p.2|}, ENNReal.ofReal |p.2|
          ∂(contractLaw F (z.1 : Measure Ω) z.2)
      ≤ ∫⁻ p in {p | ENNReal.ofReal M < ENNReal.ofReal |p.2|}, ENNReal.ofReal |p.2|
            ∂(contractLaw F (z.1 : Measure Ω) z.2) +
          ENNReal.ofReal M * contractLaw F (z.1 : Measure Ω) z.2 {p | p.1 ≤ δ} :=
        tail_split_le _ hR0 hδ hR hMpos.le
    _ ≤ ε / 2 + ENNReal.ofReal M * (ε / 2 / ENNReal.ofReal M) :=
        add_le_add ((le_iSup (fun z : K × 𝔸 =>
          ∫⁻ p in {p | ENNReal.ofReal M < ENNReal.ofReal |p.2|}, ENNReal.ofReal |p.2|
            ∂(contractLaw F (z.1 : Measure Ω) z.2)) z).trans hM) (mul_le_mul' le_rfl (hδb z))
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl ENNReal.mul_div_le
    _ = ε := ENNReal.add_halves ε

lemma AnnuitySetting.toJoint (h : AnnuitySetting F K) : JointSetting F K 1 :=
  ⟨h.compact, h.cont, h.pos, h.ratioTail', h.ui, h.mean_pos⟩

theorem AnnuitySetting.w1_continuity' (h : AnnuitySetting F K) :
    ∀ x ∈ K ×ˢ (Set.univ : Set 𝔸),
      Tendsto (fun y : ProbabilityMeasure Ω × 𝔸 =>
          wasserstein 1 (reweightAt F (y.1 : Measure Ω) y.2)
            (reweightAt F (x.1 : Measure Ω) x.2))
        (𝓝[K ×ˢ Set.univ] x) (𝓝 0) :=
  (h.toJoint.joint_continuity' le_rfl).2

lemma AnnuitySetting.isProbabilityMeasure_reweightAt (h : AnnuitySetting F K)
    {Q : ProbabilityMeasure Ω} (hQ : Q ∈ K) (a : 𝔸) :
    IsProbabilityMeasure (reweightAt F (Q : Measure Ω) a) :=
  isProbabilityMeasure_reweight _ (contractLaw_neg_null h.cont h.pos _ _)
    (mean_pos_of_class h.mean_pos hQ a)

theorem AnnuitySetting.calls_uniform' (h : AnnuitySetting F K) (x : ProbabilityMeasure Ω × 𝔸)
    (hx : x ∈ K ×ˢ (Set.univ : Set 𝔸)) :
    TendstoUniformly (fun (y : ProbabilityMeasure Ω × 𝔸) (k : ℝ) =>
        normCall (reweightAt F (y.1 : Measure Ω) y.2) k)
      (fun k => normCall (reweightAt F (x.1 : Measure Ω) x.2) k) (𝓝[K ×ˢ Set.univ] x) := by
  have hfin := (h.toJoint.joint_continuity' le_rfl).1
  have hW := h.w1_continuity' x hx
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hW.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)), self_mem_nhdsWithin]
    with y hy hyK k
  have := h.isProbabilityMeasure_reweightAt hx.1 x.2
  have := h.isProbabilityMeasure_reweightAt hyK.1 y.2
  have hb := abs_normCall_sub_le _ _ (hfin _ hyK.1 y.2) (hfin _ hx.1 x.2) k
  rw [Real.dist_eq, abs_sub_comm]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hb.trans_lt hy)

theorem AnnuitySetting.tendsto_mean (h : AnnuitySetting F K) (x : ProbabilityMeasure Ω × 𝔸)
    (hx : x ∈ K ×ˢ (Set.univ : Set 𝔸)) :
    Tendsto (fun y : ProbabilityMeasure Ω × 𝔸 => numeraireMean (contractLaw F (y.1 : Measure Ω) y.2))
      (𝓝[K ×ˢ Set.univ] x) (𝓝 (numeraireMean (contractLaw F (x.1 : Measure Ω) x.2))) := by
  have := nhdsWithin_isCountablyGenerated (K ×ˢ (Set.univ : Set 𝔸)) x
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  obtain ⟨v, hvS, hv, huv⟩ := exists_seq_mem_of_tendsto_nhdsWithin hx hu
  have hS := standing_of_seq h.cont h.pos h.ui h.mean_pos (fun n => (hvS n).1) hx.1 hv
  refine hS.tendsto_mean.congr' ?_
  filter_upwards [huv] with n hn
  simp [hn]

theorem AnnuitySetting.prices_uniform' (h : AnnuitySetting F K) (x : ProbabilityMeasure Ω × 𝔸)
    (hx : x ∈ K ×ˢ (Set.univ : Set 𝔸)) (k₀ : ℝ) :
    TendstoUniformlyOn (fun (y : ProbabilityMeasure Ω × 𝔸) (k : ℝ) =>
        payerPrice F (y.1 : Measure Ω) y.2 k)
      (fun k => payerPrice F (x.1 : Measure Ω) x.2 k) (𝓝[K ×ˢ Set.univ] x)
      (Set.Icc (-k₀) k₀) := by
  have hfin := (h.toJoint.joint_continuity' le_rfl).1
  set Γx := reweightAt F (x.1 : Measure Ω) x.2
  set mx := numeraireMean (contractLaw F (x.1 : Measure Ω) x.2)
  have hmx : 0 < mx := mean_pos_of_class h.mean_pos hx.1 x.2
  have := h.isProbabilityMeasure_reweightAt hx.1 x.2
  set B := normCall Γx (-k₀)
  have hB : ∀ k ∈ Set.Icc (-k₀) k₀, |normCall Γx k| ≤ B := fun k hk => by
    rw [abs_of_nonneg (normCall_nonneg _ _)]
    exact normCall_anti Γx (hfin _ hx.1 x.2) hk.1
  have hB0 : 0 ≤ B := normCall_nonneg _ _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hden : 0 < B + 2 + mx := by linarith
  set η := min 1 (ε / (2 * (B + 2 + mx)))
  have hη : 0 < η := lt_min one_pos (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η * (B + 2 + mx) ≤ ε / 2 := by
    have := min_le_right 1 (ε / (2 * (B + 2 + mx)))
    calc η * (B + 2 + mx) ≤ ε / (2 * (B + 2 + mx)) * (B + 2 + mx) :=
          mul_le_mul_of_nonneg_right this hden.le
      _ = ε / 2 := by field_simp
  have hmean := Metric.tendsto_nhds.1 (h.tendsto_mean x hx) η hη
  have hcalls := (Metric.tendstoUniformly_iff.1 (h.calls_uniform' x hx)) η hη
  filter_upwards [self_mem_nhdsWithin, hmean, hcalls] with y hyK hym hyc k hk
  have hmy : 0 < numeraireMean (contractLaw F (y.1 : Measure Ω) y.2) :=
    mean_pos_of_class h.mean_pos hyK.1 y.2
  rw [payerPrice_eq _ _ (measurable_section h.cont _) (contractLaw_nonpos_null h.cont h.pos _ _)
      hmx k,
    payerPrice_eq _ _ (measurable_section h.cont _) (contractLaw_nonpos_null h.cont h.pos _ _)
      hmy k]
  set my := numeraireMean (contractLaw F (y.1 : Measure Ω) y.2)
  set Cx := normCall Γx k
  set Cy := normCall (reweightAt F (y.1 : Measure Ω) y.2) k
  have h1 : |my - mx| < η := by rw [← Real.dist_eq]; exact hym
  have h2 : |Cx - Cy| < η := by rw [← Real.dist_eq]; exact hyc k
  have hCx : |Cx| ≤ B := hB k hk
  have hCy : |Cy| ≤ B + η := by
    have := abs_sub_abs_le_abs_sub Cy Cx
    rw [abs_sub_comm Cy Cx] at this
    linarith
  rw [Real.dist_eq]
  have key : mx * Cx - my * Cy = (mx - my) * Cy + mx * (Cx - Cy) := by ring
  rw [key]
  calc |(mx - my) * Cy + mx * (Cx - Cy)|
      ≤ |mx - my| * |Cy| + |mx| * |Cx - Cy| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ η * (B + η) + mx * η := by
        rw [abs_sub_comm mx my, abs_of_pos hmx]
        exact add_le_add (mul_le_mul h1.le hCy (abs_nonneg _) hη.le)
          (mul_le_mul_of_nonneg_left h2.le hmx.le)
    _ ≤ η * (B + 2 + mx) := by nlinarith
    _ ≤ ε / 2 := hηε
    _ < ε := half_lt_self hε

/-! ### The raw second moment -/

lemma rpow_two_abs (z : ℝ) : ENNReal.ofReal (|z| ^ (2 : ℝ)) = ENNReal.ofReal (z ^ 2) := by
  rw [Real.rpow_two, sq_abs]

lemma boundaryFamily_two : boundaryFamily 2 = fun p => ENNReal.ofReal (p.2 ^ 2 / p.1) := by
  funext p
  rw [boundaryFamily, Real.rpow_two, sq_abs, show (1 : ℝ) - 2 = -1 by norm_num,
    Real.rpow_neg_one, div_eq_mul_inv]

lemma lintegral_sq_eq_moment (μ : Measure ℝ) :
    ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂μ = moment 2 μ := by
  unfold moment
  simp_rw [rpow_two_abs]

theorem AnnuitySetting.second_moment' (h : AnnuitySetting F K) {Q : ProbabilityMeasure Ω}
    (hQ : Q ∈ K) (a : 𝔸) :
    ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F (Q : Measure Ω) a) =
      (∫⁻ ω, ENNReal.ofReal ((F a ω).2 ^ 2 / (F a ω).1) ∂(Q : Measure Ω)) /
        ENNReal.ofReal (numeraireMean (contractLaw F (Q : Measure Ω) a)) := by
  have hm := mean_pos_of_class h.mean_pos hQ a
  have hmom := moment_reweight (contractLaw F (Q : Measure Ω) a)
    (contractLaw_nonpos_null h.cont h.pos _ _) hm 2
  rw [boundaryFamily_two, contractLaw, lintegral_map (by fun_prop)
    (measurable_section h.cont a)] at hmom
  rw [lintegral_sq_eq_moment]
  exact hmom

theorem AnnuitySetting.second_moment_stability' (h : AnnuitySetting F K)
    (y : ℕ → ProbabilityMeasure Ω × 𝔸) (x : ProbabilityMeasure Ω × 𝔸)
    (hy : ∀ n, (y n).1 ∈ K) (hx : x.1 ∈ K) (hlim : Tendsto y atTop (𝓝 x)) :
    ((∀ n, ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F ((y n).1 : Measure Ω) (y n).2) < ∞) ∧
        ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F (x.1 : Measure Ω) x.2) < ∞ ∧
        Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F ((y n).1 : Measure Ω) (y n).2))
          atTop (𝓝 (∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweightAt F (x.1 : Measure Ω) x.2)))) ↔
      UnifIntegrableFamily (fun n => contractLaw F ((y n).1 : Measure Ω) (y n).2)
        fun p => ENNReal.ofReal (p.2 ^ 2 / p.1) := by
  have hS := standing_of_seq h.cont h.pos h.ui h.mean_pos hy hx hlim
  have hC := hS.boundary_free_iff (contractLaw_zero_null h.cont h.pos _ _) (s := 2) (by norm_num)
  rw [boundaryFamily_two] at hC
  rw [← hC]
  simp_rw [lintegral_sq_eq_moment]
  have := hS.isProbabilityMeasure_reweight_lim'
  constructor
  · rintro ⟨hfin, hlimfin, htend⟩
    exact ⟨hlimfin, hfin, tendsto_wasserstein_of_weakConv 2 (by norm_num)
      hS.isProbabilityMeasure_reweight_n hS.weakConv_reweight hlimfin htend⟩
  · rintro ⟨hlimfin, hfin, hW⟩
    exact ⟨hfin, hlimfin, tendsto_moment_of_tendsto_wasserstein 2 (by norm_num) hlimfin hW⟩

end Annuity

/-- §6.2, item 2, in the abstract model of Example 4.1 with `s = 2`. -/
theorem example_4_1_calls_second_moment' {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly (fun (n : ℕ) (k : ℝ) => normCall (reweight (exTwoAtom 2 (ε n))) k)
      (fun k => normCall (Measure.dirac 0) k) atTop ∧
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(reweight (exTwoAtom 2 (ε n)))) atTop (𝓝 1) ∧
    ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂(Measure.dirac (0 : ℝ)) = 0 := by
  obtain ⟨-, -, -, -, -, heq, -, hWlt, -, -, -⟩ := example_4_1' (s := 2) (by norm_num) hε hεlim
  refine ⟨?_, ?_, by simp⟩
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [(hWlt 1 le_rfl (by norm_num)).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))] with n hn k
    have := isProbabilityMeasure_reweight_exTwoAtom (s := 2) (by norm_num) (hε n)
    have hfin : HasFiniteMoment 1 (reweight (exTwoAtom 2 (ε n))) := by
      unfold HasFiniteMoment
      rw [exTwoAtom_moment' (s := 2) (by norm_num) (hε n) le_rfl]
      exact ENNReal.ofReal_lt_top
    have hfin0 : HasFiniteMoment 1 (Measure.dirac (0 : ℝ)) := by
      simp [HasFiniteMoment]
    have hb := abs_normCall_sub_le _ _ hfin hfin0 k
    rw [Real.dist_eq, abs_sub_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 (hb.trans_lt hn)
  · simpa only [rpow_two_abs] using heq

/-- §6.2, item 3 (cash settlement). -/
theorem cash_settled' (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (G : ℝ → ℝ)
    (hG : Measurable G) (hGpos : ∀ x, 0 < G x) (hGint : Integrable G ρ) (K : ℝ) :
    (∀ x, G x * max ((x * G x) / G x - K) 0 = G x * max (x - K) 0) ∧
    reweight (ρ.map fun x => (G x, x * G x)) =
      ρ.withDensity (fun x => ENNReal.ofReal (G x / ∫ y, G y ∂ρ)) ∧
    ∫⁻ z, ENNReal.ofReal (max (z - K) 0) ∂(reweight (ρ.map fun x => (G x, x * G x))) =
      (∫⁻ x, ENNReal.ofReal (G x * max (x - K) 0) ∂ρ) / ENNReal.ofReal (∫ y, G y ∂ρ) := by
  set φ : ℝ → ℝ × ℝ := fun x => (G x, x * G x)
  have hφ : Measurable φ := hG.prodMk (measurable_id.mul hG)
  have hratio : ∀ x, (φ x).2 / (φ x).1 = x := fun x => by
    simp only [φ]
    rw [mul_div_assoc, div_self (hGpos x).ne', mul_one]
  have hm : numeraireMean (ρ.map φ) = ∫ y, G y ∂ρ := by
    unfold numeraireMean
    rw [integral_map hφ.aemeasurable measurable_fst.aestronglyMeasurable]
  have hmpos : 0 < ∫ y, G y ∂ρ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hGpos x).le) hGint]
    have : Function.support G = Set.univ :=
      Set.eq_univ_of_forall fun x => (hGpos x).ne'
    rw [this, measure_univ]
    exact one_pos
  refine ⟨fun x => by rw [mul_div_assoc, div_self (hGpos x).ne', mul_one], ?_, ?_⟩
  · unfold reweight
    rw [hm]
    ext S hS
    rw [Measure.map_apply measurable_ratio hS, withDensity_apply _ (measurable_ratio hS),
      setLIntegral_map (measurable_ratio hS) (measurable_density _) hφ, withDensity_apply _ hS]
    have hpre : φ ⁻¹' ((fun p : ℝ × ℝ => p.2 / p.1) ⁻¹' S) = S := by
      ext x
      simp only [mem_preimage, hratio x]
    rw [hpre]
  · rw [lintegral_reweight _ (hm ▸ hmpos) _ (by fun_prop), hm,
      lintegral_map (by fun_prop) hφ]
    congr 1
    refine lintegral_congr fun x => ?_
    simp only [hratio x]
    rw [← ENNReal.ofReal_mul (hGpos x).le]

/-- Non-vacuity of the hypotheses of §6.2, item 1. -/
theorem annuitySetting_example' :
    AnnuitySetting (fun (a : Set.Icc (0 : ℝ) 1) (ω : ℝ) => (1 + (a : ℝ), Real.sin ω))
      (diracProba '' Set.Icc (0 : ℝ) 1) where
  compact := isCompact_Icc.image continuous_diracProba
  cont := exContract_continuous
  pos := exContract_pos
  ui := (jointSetting_example' (s := 1)).ui
  ui_leg := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with M hM
    refine (le_antisymm (iSup_le fun z => ?_) zero_le).symm
    refine (setLIntegral_measure_zero _ _ ?_).le
    refine exContract_null _ z.2 (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp measurable_snd).ennreal_ofReal) fun ω hω => ?_
    have h1 := exContract_snd_le z.2 ω
    have : ENNReal.ofReal M < ENNReal.ofReal |(exContract z.2 ω).2| := hω
    rw [ENNReal.ofReal_lt_ofReal_iff'] at this
    linarith [this.1]
  mean_pos := (jointSetting_example' (s := 1)).mean_pos


end NumeraireStability
