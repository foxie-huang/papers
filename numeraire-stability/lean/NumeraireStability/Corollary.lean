/-
# Corollary 3.4
-/
import NumeraireStability.Boundary

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

lemma boundaryFamily_one : boundaryFamily 1 = fun p => ENNReal.ofReal |p.2| := by
  funext p
  simp [boundaryFamily]

section Standing

variable {Q : ℕ → Measure (ℝ × ℝ)} {Qlim : Measure (ℝ × ℝ)}

/-- `∫ |b| dQ = I_1 + ∫_{a = 0} |b| dQ`. -/
lemma StandingSetting.lintegral_abs_snd_split (h : StandingSetting Q Qlim) :
    ∫⁻ p, ENNReal.ofReal |p.2| ∂Qlim =
      boundaryIntegral 1 Qlim + ∫⁻ p in {p | p.1 = 0}, ENNReal.ofReal |p.2| ∂Qlim := by
  rw [boundaryIntegral, boundaryFamily_one,
    ← lintegral_add_compl (fun p => ENNReal.ofReal |p.2|)
      (measurableSet_lt measurable_const measurable_fst)]
  congr 1
  refine setLIntegral_congr ?_
  filter_upwards [ae_nonneg_of_null h.lim_supp] with p hp
  simp only [mem_compl_iff, Set.mem_ofPred_eq, not_lt, eq_iff_iff]
  exact ⟨fun h1 => le_antisymm h1 hp, fun h1 => h1.le⟩

/-- **Corollary 3.4(a).** -/
theorem StandingSetting.sharp_cancellation' (h : StandingSetting Q Qlim)
    (hB : UnifIntegrableFamily Q fun p => ENNReal.ofReal |p.2|) :
    HasFiniteMoment 1 (reweight Qlim) ∧ (∀ n, HasFiniteMoment 1 (reweight (Q n))) ∧
      (Tendsto (fun n => wasserstein 1 (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0) ↔
        ∫⁻ p in {p | p.1 = 0}, ENNReal.ofReal |p.2| ∂Qlim = 0) := by
  have hBu : UITails Q fun p => ENNReal.ofReal |p.2| := hB
  have hφc : Continuous fun p : ℝ × ℝ => |p.2| := continuous_abs.comp continuous_snd
  obtain ⟨hEfin, hEtend⟩ := tendsto_lintegral_of_uiTails h.prob h.prob_lim h.weak
    (fun p => |p.2|) hφc (fun p => abs_nonneg _) hBu
  obtain ⟨C, hC, hCb⟩ := exists_bound_of_uiTails h.prob (fun p => |p.2|) hφc hBu
  have hEn : ∀ n, ∫⁻ p, ENNReal.ofReal |p.2| ∂(Q n) < ∞ := fun n => (hCb n).trans_lt hC
  have hsplit := h.lintegral_abs_snd_split
  have hIfin : boundaryIntegral 1 Qlim < ∞ :=
    lt_of_le_of_lt (le_of_le_of_eq le_self_add hsplit.symm) hEfin
  have hfinL : HasFiniteMoment 1 (reweight Qlim) := by
    show moment 1 (reweight Qlim) < ∞
    rw [moment_reweight_lim Qlim h.mean_pos 1]
    exact ENNReal.div_lt_top hIfin.ne (ENNReal.ofReal_pos.2 h.mean_pos).ne'
  have hfinn : ∀ n, HasFiniteMoment 1 (reweight (Q n)) := fun n => by
    show moment 1 (reweight (Q n)) < ∞
    rw [moment_reweight (Q n) (h.pos n) (h.mean_pos_n n) 1, boundaryFamily_one]
    exact ENNReal.div_lt_top (hEn n).ne (ENNReal.ofReal_pos.2 (h.mean_pos_n n)).ne'
  have h12 := (h.exact_two_way (s := 1) le_rfl).out 1 2
  refine ⟨hfinL, hfinn, ⟨fun hW => ?_, fun hZ => ?_⟩⟩
  · obtain ⟨-, -, htend⟩ := h12.1 ⟨hfinL, hfinn, hW⟩
    rw [boundaryFamily_one] at htend
    have heq := tendsto_nhds_unique hEtend htend
    rw [hsplit] at heq
    exact ((ENNReal.add_right_inj hIfin.ne).1 (heq.trans (add_zero _).symm))
  · refine (h12.2 ⟨fun n => ?_, hIfin, ?_⟩).2.2
    · rw [boundaryFamily_one]
      exact hEn n
    · rw [boundaryFamily_one]
      rw [hsplit, hZ, add_zero] at hEtend
      exact hEtend

/-- **Corollary 3.4(a)**, "in particular". -/
theorem StandingSetting.sharp_cancellation_of_no_boundary' (h : StandingSetting Q Qlim)
    (hB : UnifIntegrableFamily Q fun p => ENNReal.ofReal |p.2|)
    (h0 : Qlim {p | p.1 = 0} = 0) :
    Tendsto (fun n => wasserstein 1 (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0) :=
  ((h.sharp_cancellation' hB).2.2).2 (setLIntegral_measure_zero _ _ h0)

end Standing

/-! ### Corollary 3.4(b): ratio tails versus ordinary uniform integrability -/

lemma rpow_family_le {a b R s : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (hs : 0 ≤ s) (hb : |b| ≤ R * a) :
    |b| ^ s * a ^ (1 - s) ≤ R ^ s * a := by
  have h1 : |b| ^ s ≤ (R * a) ^ s := Real.rpow_le_rpow (abs_nonneg _) hb hs
  rw [Real.mul_rpow hR ha.le] at h1
  calc |b| ^ s * a ^ (1 - s) ≤ R ^ s * a ^ s * a ^ (1 - s) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ha.le _)
    _ = R ^ s * a := by
        rw [mul_assoc, ← Real.rpow_add ha, show s + (1 - s) = 1 by ring, Real.rpow_one]

lemma le_rpow_family {a b R s : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (hs : 0 ≤ s) (hb : R * a ≤ |b|) :
    R ^ s * a ≤ |b| ^ s * a ^ (1 - s) := by
  have h1 : (R * a) ^ s ≤ |b| ^ s := Real.rpow_le_rpow (mul_nonneg hR ha.le) hb hs
  rw [Real.mul_rpow hR ha.le] at h1
  calc R ^ s * a = R ^ s * a ^ s * a ^ (1 - s) := by
        rw [mul_assoc, ← Real.rpow_add ha, show s + (1 - s) = 1 by ring, Real.rpow_one]
    _ ≤ |b| ^ s * a ^ (1 - s) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ha.le _)

lemma measurable_boundaryFamily (s : ℝ) : Measurable (boundaryFamily s) := by
  unfold boundaryFamily
  fun_prop

/-- `E[W ; W > M] ≤ E[W ; |B| > R A] + R^s E[A ; A > M/R^s]`. -/
lemma tailW_le (P : Measure (ℝ × ℝ)) (hpos : P {p | p.1 ≤ 0} = 0) {s R M : ℝ} (hs : 0 ≤ s)
    (hR : 0 < R) (hM : 0 ≤ M) :
    ∫⁻ p in {p | ENNReal.ofReal M < boundaryFamily s p}, boundaryFamily s p ∂P ≤
      ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂P +
        ENNReal.ofReal (R ^ s) * ∫⁻ p in {p | ENNReal.ofReal (M / R ^ s) < ENNReal.ofReal p.1},
          ENNReal.ofReal p.1 ∂P := by
  have hW := measurable_boundaryFamily s
  have hS1 : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal M < boundaryFamily s p} :=
    measurableSet_lt measurable_const hW
  have hS2 : MeasurableSet {p : ℝ × ℝ | R * p.1 < |p.2|} :=
    measurableSet_lt (measurable_const.mul measurable_fst)
      (continuous_abs.measurable.comp measurable_snd)
  have hS3 : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal (M / R ^ s) < ENNReal.ofReal p.1} :=
    measurableSet_lt measurable_const measurable_fst.ennreal_ofReal
  rw [← lintegral_indicator hS1, ← lintegral_indicator hS2, ← lintegral_indicator hS3,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left (hW.indicator hS2)]
  refine lintegral_mono_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
  have hRs : 0 < R ^ s := Real.rpow_pos_of_pos hR s
  by_cases h2 : R * p.1 < |p.2|
  · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | R * p.1 < |p.2|} from h2)]
    exact (Set.indicator_le_self _ _ p).trans le_self_add
  · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | R * p.1 < |p.2|} from h2), zero_add]
    by_cases h1 : ENNReal.ofReal M < boundaryFamily s p
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | ENNReal.ofReal M < boundaryFamily s p}
        from h1)]
      have hle := rpow_family_le hp hR.le hs (not_lt.1 h2)
      have hMw : M < |p.2| ^ s * p.1 ^ (1 - s) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM).1 h1
      have h3 : ENNReal.ofReal (M / R ^ s) < ENNReal.ofReal p.1 := by
        rw [ENNReal.ofReal_lt_ofReal_iff hp, div_lt_iff₀ hRs]
        linarith
      rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | ENNReal.ofReal (M / R ^ s) <
        ENNReal.ofReal p.1} from h3), boundaryFamily, ← ENNReal.ofReal_mul hRs.le]
      exact ENNReal.ofReal_le_ofReal hle
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | ENNReal.ofReal M < boundaryFamily s p}
        from h1)]
      exact zero_le

/-- `E[W ; |B| > R A] ≤ E[W ; W > M] + M P(A ≤ M/R^s)`. -/
lemma ratio_le_tailW (P : Measure (ℝ × ℝ)) (hpos : P {p | p.1 ≤ 0} = 0) {s R M : ℝ}
    (hs : 0 ≤ s) (hR : 0 < R) (hM : 0 ≤ M) :
    ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂P ≤
      ∫⁻ p in {p | ENNReal.ofReal M < boundaryFamily s p}, boundaryFamily s p ∂P +
        ENNReal.ofReal M * P {p | p.1 ≤ M / R ^ s} := by
  have hW := measurable_boundaryFamily s
  have hS1 : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal M < boundaryFamily s p} :=
    measurableSet_lt measurable_const hW
  have hS2 : MeasurableSet {p : ℝ × ℝ | R * p.1 < |p.2|} :=
    measurableSet_lt (measurable_const.mul measurable_fst)
      (continuous_abs.measurable.comp measurable_snd)
  have hS4 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ M / R ^ s} :=
    measurableSet_le measurable_fst measurable_const
  rw [← lintegral_indicator hS1, ← lintegral_indicator hS2, ← lintegral_indicator_one hS4,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left (hW.indicator hS1)]
  refine lintegral_mono_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
  have hRs : 0 < R ^ s := Real.rpow_pos_of_pos hR s
  by_cases h1 : ENNReal.ofReal M < boundaryFamily s p
  · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | ENNReal.ofReal M < boundaryFamily s p}
      from h1)]
    exact (Set.indicator_le_self _ _ p).trans le_self_add
  · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | ENNReal.ofReal M < boundaryFamily s p}
      from h1), zero_add]
    by_cases h2 : R * p.1 < |p.2|
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | R * p.1 < |p.2|} from h2)]
      have hge := le_rpow_family hp hR.le hs h2.le
      have hwM : |p.2| ^ s * p.1 ^ (1 - s) ≤ M := by
        by_contra hc
        exact h1 ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM).2 (not_le.1 hc))
      have h4 : p.1 ≤ M / R ^ s := by
        rw [le_div_iff₀ hRs]
        linarith
      rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 ≤ M / R ^ s} from h4), Pi.one_apply,
        mul_one, boundaryFamily]
      exact ENNReal.ofReal_le_ofReal hwM
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | R * p.1 < |p.2|} from h2)]
      exact zero_le

section Standing'

variable {Q : ℕ → Measure (ℝ × ℝ)} {Qlim : Measure (ℝ × ℝ)}

/-- Remark 3.5: the ratio-tail condition always implies ordinary uniform
integrability of `W_n`. -/
lemma StandingSetting.uiTails_of_ratioTail (h : StandingSetting Q Qlim) {s : ℝ} (hs : 0 ≤ s)
    (h3 : Tendsto (ratioTail s Q) atTop (𝓝 0)) : UITails Q (boundaryFamily s) := by
  rw [UITails, ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨R, hR, hR1⟩ := ((h3.eventually (gt_mem_nhds hε2)).and (eventually_ge_atTop 1)).exists
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRs : 0 < R ^ s := Real.rpow_pos_of_pos hRpos s
  have hA : Tendsto (fun M : ℝ => ⨆ n, ∫⁻ p in {p | ENNReal.ofReal (M / R ^ s) <
      ENNReal.ofReal p.1}, ENNReal.ofReal p.1 ∂(Q n)) atTop (𝓝 0) :=
    h.ui.comp (tendsto_id.atTop_div_const hRs)
  have hA' := ENNReal.Tendsto.const_mul hA (Or.inr (ENNReal.ofReal_ne_top (r := R ^ s)))
  rw [mul_zero] at hA'
  filter_upwards [hA'.eventually (gt_mem_nhds hε2), eventually_ge_atTop 0] with M hM hM0
  refine iSup_le fun n => ?_
  calc ∫⁻ p in {p | ENNReal.ofReal M < boundaryFamily s p}, boundaryFamily s p ∂(Q n)
      ≤ ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂(Q n) +
          ENNReal.ofReal (R ^ s) * ∫⁻ p in {p | ENNReal.ofReal (M / R ^ s) <
            ENNReal.ofReal p.1}, ENNReal.ofReal p.1 ∂(Q n) :=
        tailW_le (Q n) (h.pos n) hs hRpos hM0
    _ ≤ ratioTail s Q R + ENNReal.ofReal (R ^ s) * ⨆ n, ∫⁻ p in {p | ENNReal.ofReal (M / R ^ s) <
          ENNReal.ofReal p.1}, ENNReal.ofReal p.1 ∂(Q n) :=
        add_le_add (le_iSup (fun n => ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂(Q n)) n)
          (mul_le_mul' le_rfl (le_iSup (fun n => ∫⁻ p in {p | ENNReal.ofReal (M / R ^ s) <
            ENNReal.ofReal p.1}, ENNReal.ofReal p.1 ∂(Q n)) n))
    _ ≤ ε / 2 + ε / 2 := add_le_add hR.le hM.le
    _ = ε := ENNReal.add_halves ε

/-- If the limit does not charge `{a = 0}`, the numéraires are uniformly away
from `0` in probability. -/
lemma StandingSetting.exists_uniform_small (h : StandingSetting Q Qlim)
    (h0 : Qlim {p | p.1 = 0} = 0) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, ∀ n, Q n {p | p.1 ≤ δ} ≤ η := by
  -- continuity from above at `0`, for any finite measure carried by `{a ≥ 0}`-ish sets
  have hcont : ∀ (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ],
      Tendsto (fun δ : ℝ => ρ {p | p.1 ≤ δ}) (𝓝[>] 0) (𝓝 (ρ {p | p.1 ≤ 0})) := by
    intro ρ _
    have key := tendsto_measure_biInter_gt (μ := ρ) (s := fun r : ℝ => {p : ℝ × ℝ | p.1 ≤ r})
      (a := 0) (fun r _ => (measurableSet_le measurable_fst measurable_const).nullMeasurableSet)
      (fun i j _ hij p hp => le_trans hp hij) ⟨1, zero_lt_one, measure_ne_top ρ _⟩
    have hI : (⋂ r > (0 : ℝ), {p : ℝ × ℝ | p.1 ≤ r}) = {p | p.1 ≤ 0} := by
      ext p
      simp only [mem_iInter, Set.mem_ofPred_eq]
      exact ⟨fun hp => le_of_forall_pos_le_add fun ε hε => by simpa using hp ε hε,
        fun hp r hr => hp.trans hr.le⟩
    rw [hI] at key
    exact key
  have hQ0 : Qlim {p | p.1 ≤ 0} = 0 := by
    refine measure_mono_null (t := {p | p.1 = 0} ∪ {p | p.1 < 0}) (fun p hp => ?_)
      (measure_union_null h0 h.lim_supp)
    rcases (show p.1 ≤ 0 from hp).eq_or_lt with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hlim := h.prob_lim
  -- a level `t0` at which the limit mass below `t0` is below `η`
  have hev := (hcont Qlim).eventually (gt_mem_nhds (show Qlim {p | p.1 ≤ 0} < η by
    rw [hQ0]; exact hη))
  obtain ⟨t0, ht0, ht0pos⟩ := (hev.and self_mem_nhdsWithin).exists
  set δ1 := t0 / 2 with hδ1
  have hδ1pos : 0 < δ1 := half_pos ht0pos
  -- the bounded continuous function `min 1 (max 0 (2 - a/δ1))`
  let f : ℝ × ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun p => min 1 (max 0 (2 - p.1 / δ1)), by fun_prop⟩ 1 (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : 0 ≤ min 1 (max 0 (2 - x.1 / δ1)) := le_min zero_le_one (le_max_left _ _)
      have h2 : min 1 (max 0 (2 - x.1 / δ1)) ≤ 1 := min_le_left _ _
      have h3 : 0 ≤ min 1 (max 0 (2 - y.1 / δ1)) := le_min zero_le_one (le_max_left _ _)
      have h4 : min 1 (max 0 (2 - y.1 / δ1)) ≤ 1 := min_le_left _ _
      rw [abs_le]
      constructor <;> linarith)
  have hf0 : ∀ p, 0 ≤ f p := fun p => le_min zero_le_one (le_max_left _ _)
  have hlow : ∀ (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ],
      ρ {p | p.1 ≤ δ1} ≤ ENNReal.ofReal (∫ p, f p ∂ρ) := by
    intro ρ _
    rw [ofReal_integral_eq_lintegral_ofReal (f.integrable ρ) (ae_of_all _ hf0),
      ← lintegral_indicator_one (measurableSet_le measurable_fst measurable_const)]
    refine lintegral_mono fun p => ?_
    by_cases hp : p.1 ≤ δ1
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 ≤ δ1} from hp), Pi.one_apply]
      have : f p = 1 := by
        show min 1 (max 0 (2 - p.1 / δ1)) = 1
        have : p.1 / δ1 ≤ 1 := (div_le_one hδ1pos).2 hp
        rw [min_eq_left]
        exact le_max_of_le_right (by linarith)
      rw [this, ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 ≤ δ1} from hp)]
      exact zero_le
  have hup : ENNReal.ofReal (∫ p, f p ∂Qlim) ≤ Qlim {p | p.1 ≤ t0} := by
    rw [ofReal_integral_eq_lintegral_ofReal (f.integrable Qlim) (ae_of_all _ hf0),
      ← lintegral_indicator_one (measurableSet_le measurable_fst measurable_const)]
    refine lintegral_mono fun p => ?_
    by_cases hp : p.1 ≤ t0
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 ≤ t0} from hp), Pi.one_apply,
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 ≤ t0} from hp)]
      have : f p = 0 := by
        show min 1 (max 0 (2 - p.1 / δ1)) = 0
        have : 2 ≤ p.1 / δ1 := by
          rw [le_div_iff₀ hδ1pos]
          linarith [not_le.1 hp]
        rw [max_eq_left (by linarith), min_eq_right zero_le_one]
      rw [this, ENNReal.ofReal_zero]
  -- beyond some index the sequence is below `η` at level `δ1`
  have htend := ENNReal.tendsto_ofReal (h.weak f)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually (gt_mem_nhds (lt_of_le_of_lt hup ht0)))
  -- the finitely many earlier indices
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ n ∈ Finset.range N, Q n {p | p.1 ≤ δ} < η :=
    (Finset.range N).eventually_all.2 fun n _ => by
      have := h.prob n
      have hQn0 : Q n {p | p.1 ≤ 0} = 0 := h.pos n
      exact (hcont (Q n)).eventually (gt_mem_nhds (by rw [hQn0]; exact hη))
  obtain ⟨δ, ⟨hδ, hδpos⟩, hδle⟩ := ((hsmall.and self_mem_nhdsWithin).and
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ1pos))).exists
  refine ⟨δ, hδpos, fun n => ?_⟩
  by_cases hn : n < N
  · exact (hδ n (Finset.mem_range.2 hn)).le
  · have := h.prob n
    calc Q n {p | p.1 ≤ δ} ≤ Q n {p | p.1 ≤ δ1} :=
          measure_mono (fun p (hp : p ∈ {p : ℝ × ℝ | p.1 ≤ δ}) =>
            show p ∈ {p : ℝ × ℝ | p.1 ≤ δ1} from le_trans hp hδle.le)
      _ ≤ ENNReal.ofReal (∫ p, f p ∂(Q n)) := hlow (Q n)
      _ ≤ η := (hN n (not_lt.1 hn)).le

/-- Ordinary uniform integrability of `W_n` gives the ratio-tail condition when
the limit does not charge `{a = 0}`. -/
lemma StandingSetting.ratioTail_of_uiTails (h : StandingSetting Q Qlim)
    (h0 : Qlim {p | p.1 = 0} = 0) {s : ℝ} (hs : 0 < s) (hU : UITails Q (boundaryFamily s)) :
    Tendsto (ratioTail s Q) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨M, hM, hM0⟩ := ((hU.eventually (gt_mem_nhds hε2)).and (eventually_ge_atTop 0)).exists
  have hη : 0 < ε / 2 / ENNReal.ofReal M :=
    ENNReal.div_pos hε2.ne' ENNReal.ofReal_ne_top
  obtain ⟨δ, hδpos, hδ⟩ := h.exists_uniform_small h0 hη
  have hMR : Tendsto (fun R : ℝ => M / R ^ s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hs)
  filter_upwards [hMR.eventually (gt_mem_nhds hδpos), eventually_gt_atTop 0] with R hR hRpos
  refine iSup_le fun n => ?_
  calc ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂(Q n)
      ≤ ∫⁻ p in {p | ENNReal.ofReal M < boundaryFamily s p}, boundaryFamily s p ∂(Q n) +
          ENNReal.ofReal M * Q n {p | p.1 ≤ M / R ^ s} :=
        ratio_le_tailW (Q n) (h.pos n) hs.le hRpos hM0
    _ ≤ ε / 2 + ENNReal.ofReal M * (ε / 2 / ENNReal.ofReal M) := by
        refine add_le_add ((le_iSup (fun n => ∫⁻ p in {p | ENNReal.ofReal M <
          boundaryFamily s p}, boundaryFamily s p ∂(Q n)) n).trans hM.le)
          (mul_le_mul' le_rfl ((measure_mono (fun p (hp : p ∈ {p : ℝ × ℝ | p.1 ≤ M / R ^ s}) =>
            show p ∈ {p : ℝ × ℝ | p.1 ≤ δ} from le_trans hp hR.le)).trans (hδ n)))
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl (ENNReal.mul_div_le)
    _ = ε := ENNReal.add_halves ε

/-- **Corollary 3.4(b).** -/
theorem StandingSetting.boundary_free_iff (h : StandingSetting Q Qlim)
    (h0 : Qlim {p | p.1 = 0} = 0) {s : ℝ} (hs : 1 ≤ s) :
    (HasFiniteMoment s (reweight Qlim) ∧ (∀ n, HasFiniteMoment s (reweight (Q n))) ∧
        Tendsto (fun n => wasserstein s (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0)) ↔
      UnifIntegrableFamily Q (boundaryFamily s) := by
  have hs0 : 0 < s := by linarith
  exact ((h.exact_two_way hs).out 1 3).trans
    ⟨h.uiTails_of_ratioTail hs0.le, h.ratioTail_of_uiTails h0 hs0⟩

end Standing'

end NumeraireStability
