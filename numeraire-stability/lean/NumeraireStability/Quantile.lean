/-
# The quantile coupling on `ℝ`

For probability measures `μ_n → ν` weakly with `s`-th moments converging to a
finite limit, `W_s(μ_n, ν) → 0`.  The coupling is the quantile (comonotone)
coupling `(q_{μ_n}, q_ν)_# Leb|_(0,1)`; its cost tends to `0` by a
generalized dominated convergence argument, because `q_{μ_n} → q_ν` almost
everywhere on `(0, 1)`.
-/
import NumeraireStability.Wasserstein
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.MeanInequalitiesPow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace NumeraireStability

/-- Lebesgue measure on `(0, 1)`. -/
abbrev unitLeb : Measure ℝ := volume.restrict (Ioo 0 1)

/-- The quantile function `q_μ(u) = inf {x | u ≤ F_μ(x)}`. -/
def quantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x | u ≤ cdf μ x}

section Quantile

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma quantile_set_nonempty {u : ℝ} (hu : u < 1) : {x | u ≤ cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (μ := μ)).eventually (lt_mem_nhds hu)).exists
  exact ⟨x, hx.le⟩

lemma quantile_set_bddBelow {u : ℝ} (hu : 0 < u) : BddBelow {x | u ≤ cdf μ x} := by
  obtain ⟨y, hy⟩ := eventually_atBot.1 ((tendsto_cdf_atBot (μ := μ)).eventually
    (gt_mem_nhds hu))
  refine ⟨y, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hy x (not_le.1 hlt).le) (not_lt.2 hx)

/-- The Galois property of the quantile function. -/
lemma quantile_le_iff {u : ℝ} (hu : u ∈ Ioo 0 1) (x : ℝ) :
    quantile μ u ≤ x ↔ u ≤ cdf μ x := by
  have hne := quantile_set_nonempty μ hu.2
  have hbdd := quantile_set_bddBelow μ hu.1
  constructor
  · intro hq
    refine le_trans ?_ ((cdf μ).mono hq)
    have hright : ∀ y ∈ Ioi (quantile μ u), u ≤ cdf μ y := fun y hy => by
      obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
      exact le_trans hz ((cdf μ).mono hzy.le)
    have htend : Tendsto (cdf μ) (𝓝[>] (quantile μ u)) (𝓝 (cdf μ (quantile μ u))) :=
      ((cdf μ).right_continuous _).mono Ioi_subset_Ici_self
    exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall hright)
  · intro h
    exact csInf_le hbdd h

lemma quantile_monotoneOn : MonotoneOn (quantile μ) (Ioo 0 1) := fun u hu v hv huv =>
  (quantile_le_iff μ hu _).2 (huv.trans ((quantile_le_iff μ hv _).1 le_rfl))

lemma aemeasurable_quantile : AEMeasurable (quantile μ) unitLeb :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (quantile_monotoneOn μ)

lemma volume_Ioo_inter_Iic {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic c) = ENNReal.ofReal c := by
  rcases h1.lt_or_eq with hlt | rfl
  · have e : Ioo (0 : ℝ) 1 ∩ Iic c = Ioc 0 c := by
      ext u
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, h3.trans_lt hlt⟩, h3⟩
    rw [e, Real.volume_Ioc, sub_zero]
  · have e : Ioo (0 : ℝ) 1 ∩ Iic 1 = Ioo 0 1 := inter_eq_left.2 fun u hu => le_of_lt hu.2
    rw [e, Real.volume_Ioo, sub_zero]

/-- The quantile function pushes Lebesgue measure on `(0, 1)` to `μ`. -/
theorem map_quantile : unitLeb.map (quantile μ) = μ := by
  refine (Measure.ext_of_Iic μ _ fun x => ?_).symm
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_quantile μ) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf μ x]
  have hset : quantile μ ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (cdf μ x) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (quantile_le_iff μ h2 x).1 h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(quantile_le_iff μ h2 x).2 h1, h2⟩
  rw [hset, volume_Ioo_inter_Iic (cdf_nonneg μ x) (cdf_le_one μ x)]

lemma lintegral_quantile (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u, f (quantile μ u) ∂unitLeb = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_map' (by rw [map_quantile]; exact hf.aemeasurable) (aemeasurable_quantile μ),
    map_quantile]

end Quantile

/-- The quantile coupling `(q_μ, q_ν)_# Leb|_(0,1)`. -/
def quantileCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  unitLeb.map fun u => (quantile μ u, quantile ν u)

lemma aemeasurable_quantile_pair (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : AEMeasurable (fun u => (quantile μ u, quantile ν u)) unitLeb :=
  (aemeasurable_quantile μ).prodMk (aemeasurable_quantile ν)

lemma isCoupling_quantileCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsCoupling (quantileCoupling μ ν) μ ν := by
  constructor
  · rw [quantileCoupling, AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
      (aemeasurable_quantile_pair μ ν)]
    exact map_quantile μ
  · rw [quantileCoupling, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      (aemeasurable_quantile_pair μ ν)]
    exact map_quantile ν

lemma cost_quantileCoupling (s : ℝ) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    cost s (quantileCoupling μ ν) =
      ∫⁻ u, ENNReal.ofReal (|quantile μ u - quantile ν u| ^ s) ∂unitLeb := by
  rw [cost, quantileCoupling, lintegral_map' (by fun_prop) (aemeasurable_quantile_pair μ ν)]

/-! ### Weak convergence moves quantiles -/

lemma countable_atoms (ν : Measure ℝ) [IsFiniteMeasure ν] : Set.Countable {x | 0 < ν {x}} :=
  Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top ν
    (As := fun x : ℝ => ({x} : Set ℝ)) (fun x => measurableSet_singleton x)
    (fun _ _ hxy => Set.disjoint_singleton.2 hxy) (measure_ne_top ν _)

lemma exists_nonatom_between (ν : Measure ℝ) [IsFiniteMeasure ν] {a b : ℝ} (h : a < b) :
    ∃ c, a < c ∧ c < b ∧ ν {c} = 0 := by
  obtain ⟨c, hc, hac, hcb⟩ := ((countable_atoms ν).dense_compl ℝ).exists_between h
  refine ⟨c, hac, hcb, ?_⟩
  simpa using hc

lemma tendsto_cdf_of_weakConv {μ : ℕ → Measure ℝ} {ν : Measure ℝ}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure ν] (hw : WeakConv μ ν)
    {x : ℝ} (hx : ν {x} = 0) :
    Tendsto (fun n => cdf (μ n) x) atTop (𝓝 (cdf ν x)) := by
  let P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μ n, hμ n⟩
  let P0 : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
  have hP : Tendsto P atTop (𝓝 P0) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => hw f
  have hfr : (P0 : Measure ℝ) (frontier (Iic x)) = 0 := by
    rw [frontier_Iic]
    exact hx
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hP hfr
  have e : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → cdf ρ x = (ρ (Iic x)).toReal :=
    fun ρ _ => by rw [← ofReal_cdf ρ x, ENNReal.toReal_ofReal (cdf_nonneg ρ x)]
  have e' : (fun n => cdf (μ n) x) = fun n => ((μ n) (Iic x)).toReal :=
    funext fun n => e (μ n) (hμ n)
  rw [e', e ν inferInstance]
  exact (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp key

/-- At every `u ∈ (0,1)` where `q_ν` is right-continuous, `q_{μ_n}(u) → q_ν(u)`. -/
lemma tendsto_quantile_of_weakConv {μ : ℕ → Measure ℝ} {ν : Measure ℝ}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure ν] (hw : WeakConv μ ν)
    {u : ℝ} (hu : u ∈ Ioo 0 1) (hcont : ContinuousWithinAt (quantile ν) (Ioo 0 1 ∩ Ioi u) u) :
    Tendsto (fun n => quantile (μ n) u) atTop (𝓝 (quantile ν u)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨x, hax, hxq, hx0⟩ := exists_nonatom_between ν ha
    have hFx : cdf ν x < u := lt_of_not_ge fun h =>
      absurd ((quantile_le_iff ν hu x).2 h) (not_le.2 hxq)
    filter_upwards [(tendsto_cdf_of_weakConv hμ hw hx0).eventually (gt_mem_nhds hFx)] with n hn
    have := hμ n
    have hlt : x < quantile (μ n) u := lt_of_not_ge fun h =>
      absurd ((quantile_le_iff (μ n) hu x).1 h) (not_le.2 hn)
    exact hax.trans hlt
  · have hset : Ioo (0 : ℝ) 1 ∩ Ioi u = Ioo u 1 := by
      ext v
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hu.1.trans h1, h2⟩, h1⟩
    rw [hset] at hcont
    have hne : (𝓝[Ioo u 1] u).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT hu.2]
      infer_instance
    obtain ⟨u', hqu', hu'⟩ := ((hcont.eventually (gt_mem_nhds hb)).and
      self_mem_nhdsWithin).exists
    obtain ⟨y, hqy, hyb, hy0⟩ := exists_nonatom_between ν hqu'
    have hu'01 : u' ∈ Ioo 0 1 := ⟨hu.1.trans hu'.1, hu'.2⟩
    have hFy : u < cdf ν y := lt_of_lt_of_le hu'.1 ((quantile_le_iff ν hu'01 y).1 hqy.le)
    filter_upwards [(tendsto_cdf_of_weakConv hμ hw hy0).eventually (lt_mem_nhds hFy)] with n hn
    have := hμ n
    exact lt_of_le_of_lt ((quantile_le_iff (μ n) hu y).2 hn.le) hyb

/-- Quantiles converge almost everywhere on `(0, 1)`. -/
lemma ae_tendsto_quantile {μ : ℕ → Measure ℝ} {ν : Measure ℝ}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure ν] (hw : WeakConv μ ν) :
    ∀ᵐ u ∂unitLeb, Tendsto (fun n => quantile (μ n) u) atTop (𝓝 (quantile ν u)) := by
  have hcount := (quantile_monotoneOn ν).countable_not_continuousWithinAt_Ioi
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hcount.ae_notMem volume] with u hu hu01
  exact tendsto_quantile_of_weakConv hμ hw hu01 (by_contra fun h => hu ⟨hu01, h⟩)

/-! ### Generalized dominated convergence -/

/-- If `a_n ≤ b_n`, `b_n → B` and `a_n → 0` almost everywhere, and
`∫ b_n → ∫ B < ∞`, then `∫ a_n → 0`. -/
lemma tendsto_lintegral_zero_of_le {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    {a b : ℕ → α → ℝ≥0∞} {B : α → ℝ≥0∞}
    (ha : ∀ n, AEMeasurable (a n) ρ) (hb : ∀ n, AEMeasurable (b n) ρ)
    (hab : ∀ n, ∀ᵐ x ∂ρ, a n x ≤ b n x)
    (hbB : ∀ᵐ x ∂ρ, Tendsto (fun n => b n x) atTop (𝓝 (B x)))
    (ha0 : ∀ᵐ x ∂ρ, Tendsto (fun n => a n x) atTop (𝓝 0))
    (hint : Tendsto (fun n => ∫⁻ x, b n x ∂ρ) atTop (𝓝 (∫⁻ x, B x ∂ρ)))
    (hBfin : ∫⁻ x, B x ∂ρ < ∞) :
    Tendsto (fun n => ∫⁻ x, a n x ∂ρ) atTop (𝓝 0) := by
  set c : ℕ → α → ℝ≥0∞ := fun n x => b n x - a n x
  have hc : ∀ n, AEMeasurable (c n) ρ := fun n => (hb n).sub (ha n)
  have hsum : ∀ n, ∫⁻ x, c n x ∂ρ + ∫⁻ x, a n x ∂ρ = ∫⁻ x, b n x ∂ρ := fun n => by
    rw [← lintegral_add_right' _ (ha n)]
    exact lintegral_congr_ae ((hab n).mono fun x hx => tsub_add_cancel_of_le hx)
  have hcB : ∀ᵐ x ∂ρ, Tendsto (fun n => c n x) atTop (𝓝 (B x)) := by
    filter_upwards [hbB, ha0] with x h1 h2
    simpa using ENNReal.Tendsto.sub h1 h2 (Or.inr ENNReal.zero_ne_top)
  have hfatou : ∫⁻ x, B x ∂ρ ≤ liminf (fun n => ∫⁻ x, c n x ∂ρ) atTop := by
    calc ∫⁻ x, B x ∂ρ = ∫⁻ x, liminf (fun n => c n x) atTop ∂ρ :=
          lintegral_congr_ae (hcB.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ x, c n x ∂ρ) atTop := lintegral_liminf_le' hc
  have hcle : ∀ n, ∫⁻ x, c n x ∂ρ ≤ ∫⁻ x, b n x ∂ρ := fun n => by
    rw [← hsum n]
    exact le_self_add
  have hctend : Tendsto (fun n => ∫⁻ x, c n x ∂ρ) atTop (𝓝 (∫⁻ x, B x ∂ρ)) :=
    tendsto_of_le_liminf_of_limsup_le hfatou
      ((limsup_le_limsup (Eventually.of_forall hcle)).trans (le_of_eq hint.limsup_eq))
  have hev : ∀ᶠ n in atTop, ∫⁻ x, a n x ∂ρ = ∫⁻ x, b n x ∂ρ - ∫⁻ x, c n x ∂ρ := by
    filter_upwards [hint.eventually (Iio_mem_nhds hBfin)] with n hn
    refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (ne_of_lt hn) (hcle n)) ?_
    rw [add_comm]
    exact hsum n
  have hlim := ENNReal.Tendsto.sub hint hctend (Or.inl hBfin.ne)
  rw [tsub_self] at hlim
  exact hlim.congr' (hev.mono fun n hn => hn.symm)

/-! ### Weak convergence plus moment convergence gives `W_s` convergence -/

lemma ofReal_abs_sub_rpow_le (s : ℝ) (hs : 1 ≤ s) (x y : ℝ) :
    ENNReal.ofReal (|x - y| ^ s) ≤
      2 ^ (s - 1) * (ENNReal.ofReal (|x| ^ s) + ENNReal.ofReal (|y| ^ s)) := by
  have hs0 : 0 ≤ s := by linarith
  have h1 : ENNReal.ofReal (|x - y| ^ s) ≤ (ENNReal.ofReal |x| + ENNReal.ofReal |y|) ^ s := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hs0]
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) ?_ hs0)
    exact abs_sub_le_iff.2 ⟨by linarith [le_abs_self x, neg_abs_le y],
      by linarith [neg_abs_le x, le_abs_self y]⟩
  refine h1.trans ?_
  have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow (ENNReal.ofReal |x|) (ENNReal.ofReal |y|) hs
  rwa [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs0,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs0] at h2

lemma measurable_ofReal_abs_rpow (s : ℝ) : Measurable fun x : ℝ => ENNReal.ofReal (|x| ^ s) := by
  fun_prop

lemma two_rpow_ne_top (s : ℝ) (hs : 1 ≤ s) : (2 : ℝ≥0∞) ^ (s - 1) ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top

lemma aemeasurable_quantile_rpow (s : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    AEMeasurable (fun u => ENNReal.ofReal (|quantile μ u| ^ s)) unitLeb :=
  ((continuous_abs.measurable.comp_aemeasurable (aemeasurable_quantile μ)).pow_const s).ennreal_ofReal

lemma aemeasurable_quantile_diff (s : ℝ) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    AEMeasurable (fun u => ENNReal.ofReal (|quantile μ u - quantile ν u| ^ s)) unitLeb :=
  ((continuous_abs.measurable.comp_aemeasurable
    ((aemeasurable_quantile μ).sub (aemeasurable_quantile ν))).pow_const s).ennreal_ofReal

lemma lintegral_bound_quantile (s : ℝ) (hs : 1 ≤ s) (ρ ν : Measure ℝ) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] :
    ∫⁻ u, 2 ^ (s - 1) * (ENNReal.ofReal (|quantile ρ u| ^ s) +
        ENNReal.ofReal (|quantile ν u| ^ s)) ∂unitLeb =
      2 ^ (s - 1) * (moment s ρ + moment s ν) := by
  rw [lintegral_const_mul' _ _ (two_rpow_ne_top s hs),
    lintegral_add_left' (aemeasurable_quantile_rpow s ρ),
    lintegral_quantile ρ (fun x => ENNReal.ofReal (|x| ^ s)) (measurable_ofReal_abs_rpow s),
    lintegral_quantile ν (fun x => ENNReal.ofReal (|x| ^ s)) (measurable_ofReal_abs_rpow s)]
  rfl

/-- The cost of the quantile couplings tends to `0`. -/
lemma tendsto_lintegral_quantile_diff (s : ℝ) (hs : 1 ≤ s) {μ : ℕ → Measure ℝ}
    {ν : Measure ℝ} (hμ : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure ν]
    (hw : WeakConv μ ν) (hνfin : moment s ν < ∞)
    (hmom : Tendsto (fun n => moment s (μ n)) atTop (𝓝 (moment s ν))) :
    Tendsto (fun n => ∫⁻ u, ENNReal.ofReal (|quantile (μ n) u - quantile ν u| ^ s) ∂unitLeb)
      atTop (𝓝 0) := by
  have hs0 : 0 < s := by linarith
  have hlim := ae_tendsto_quantile hμ hw
  refine tendsto_lintegral_zero_of_le (ρ := unitLeb)
    (a := fun n u => ENNReal.ofReal (|quantile (μ n) u - quantile ν u| ^ s))
    (b := fun n u => 2 ^ (s - 1) * (ENNReal.ofReal (|quantile (μ n) u| ^ s) +
      ENNReal.ofReal (|quantile ν u| ^ s)))
    (B := fun u => 2 ^ (s - 1) * (ENNReal.ofReal (|quantile ν u| ^ s) +
      ENNReal.ofReal (|quantile ν u| ^ s)))
    (fun n => ?_) (fun n => ?_) (fun n => ae_of_all _ fun u => ofReal_abs_sub_rpow_le s hs _ _)
    ?_ ?_ ?_ ?_
  · have := hμ n
    exact aemeasurable_quantile_diff s (μ n) ν
  · have := hμ n
    exact ((aemeasurable_quantile_rpow s (μ n)).add (aemeasurable_quantile_rpow s ν)).const_mul _
  · filter_upwards [hlim] with u hu
    exact ENNReal.Tendsto.const_mul
      ((ENNReal.tendsto_ofReal (hu.abs.rpow_const (Or.inr hs0.le))).add tendsto_const_nhds)
      (Or.inr (two_rpow_ne_top s hs))
  · filter_upwards [hlim] with u hu
    have h := ENNReal.tendsto_ofReal (((hu.sub_const (quantile ν u)).abs).rpow_const
      (Or.inr hs0.le))
    rwa [sub_self, abs_zero, Real.zero_rpow hs0.ne', ENNReal.ofReal_zero] at h
  · have e : (fun n => ∫⁻ u, (2 : ℝ≥0∞) ^ (s - 1) * (ENNReal.ofReal (|quantile (μ n) u| ^ s) +
        ENNReal.ofReal (|quantile ν u| ^ s)) ∂unitLeb) =
        fun n => 2 ^ (s - 1) * (moment s (μ n) + moment s ν) :=
      funext fun n => @lintegral_bound_quantile s hs (μ n) ν (hμ n) _
    rw [e, lintegral_bound_quantile s hs ν ν]
    exact ENNReal.Tendsto.const_mul (hmom.add tendsto_const_nhds) (Or.inr (two_rpow_ne_top s hs))
  · rw [lintegral_bound_quantile s hs ν ν]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.add_lt_top.2 ⟨hνfin, hνfin⟩)

/-- **Weak convergence plus convergence of `s`-th moments gives `W_s`
convergence** on `ℝ` (the direction of Villani, Theorem 6.9, used in
Theorem 3.3). -/
theorem tendsto_wasserstein_of_weakConv (s : ℝ) (hs : 1 ≤ s) {μ : ℕ → Measure ℝ}
    {ν : Measure ℝ} (hμ : ∀ n, IsProbabilityMeasure (μ n)) [IsProbabilityMeasure ν]
    (hw : WeakConv μ ν) (hνfin : moment s ν < ∞)
    (hmom : Tendsto (fun n => moment s (μ n)) atTop (𝓝 (moment s ν))) :
    Tendsto (fun n => wasserstein s (μ n) ν) atTop (𝓝 0) := by
  have hs0 : 0 < s := by linarith
  have hcost := tendsto_lintegral_quantile_diff s hs hμ hw hνfin hmom
  have hup : Tendsto (fun n => (∫⁻ u, ENNReal.ofReal (|quantile (μ n) u - quantile ν u| ^ s)
      ∂unitLeb) ^ (1 / s)) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / s)).tendsto 0).comp hcost
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => zero_le)
    (fun n => ?_)
  have := hμ n
  rw [← cost_quantileCoupling]
  exact wasserstein_le_cost s hs0 (isCoupling_quantileCoupling (μ n) ν)

end NumeraireStability
