/-
# Theorem 3.3: the exact two-way `W_s` boundary

The reweighted moments and tails are base-law quantities (the cancellation
identity), so weak convergence of `Γ_n` (Lemma 3.1) plus the two directions
"uniformly integrable tails ⟺ convergence of moments" and
"moments + weak ⟺ `W_s`" give the three-way equivalence.
-/
import NumeraireStability.Stability
import NumeraireStability.Quantile

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace NumeraireStability

lemma perspective_rpow {a : ℝ} (ha : 0 < a) (b s : ℝ) :
    a * |b / a| ^ s = |b| ^ s * a ^ (1 - s) := by
  rw [abs_div, abs_of_pos ha, Real.div_rpow (abs_nonneg _) ha.le, Real.rpow_sub ha,
    Real.rpow_one]
  have : 0 < a ^ s := Real.rpow_pos_of_pos ha s
  field_simp

/-- `∫ |z|^s dΓ(P) = E_P[|B|^s A^{1-s}] / E_P[A]` when `A > 0` almost surely. -/
lemma moment_reweight (P : Measure (ℝ × ℝ)) (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (s : ℝ) :
    moment s (reweight P) =
      (∫⁻ p, boundaryFamily s p ∂P) / ENNReal.ofReal (numeraireMean P) := by
  rw [moment, lintegral_reweight P hm _ (by fun_prop)]
  congr 1
  refine lintegral_congr_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
  dsimp only
  rw [boundaryFamily, ← ENNReal.ofReal_mul hp.le, perspective_rpow hp]

/-- The limit object: `∫ |z|^s dΓ = I_s / m`. -/
lemma moment_reweight_lim (Q : Measure (ℝ × ℝ)) (hm : 0 < numeraireMean Q) (s : ℝ) :
    moment s (reweight Q) = boundaryIntegral s Q / ENNReal.ofReal (numeraireMean Q) := by
  rw [moment, lintegral_reweight_pos Q hm _ (by fun_prop), boundaryIntegral]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_lt measurable_const measurable_fst)
    fun p (hp : 0 < p.1) => ?_
  rw [boundaryFamily, ← ENNReal.ofReal_mul hp.le, perspective_rpow hp]

/-- Tails: `∫_{|z| > R} |z|^s dΓ(P) = E_P[W ; |B| > R A] / E_P[A]`. -/
lemma tail_reweight (P : Measure (ℝ × ℝ)) (hpos : P {p | p.1 ≤ 0} = 0)
    (hm : 0 < numeraireMean P) (s R : ℝ) :
    ∫⁻ z in {z | R < |z|}, ENNReal.ofReal (|z| ^ s) ∂(reweight P) =
      (∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂P) /
        ENNReal.ofReal (numeraireMean P) := by
  have hS : MeasurableSet {z : ℝ | R < |z|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hT : MeasurableSet {p : ℝ × ℝ | R * p.1 < |p.2|} :=
    measurableSet_lt (measurable_const.mul measurable_fst)
      (continuous_abs.measurable.comp measurable_snd)
  have hf : Measurable fun z : ℝ => ENNReal.ofReal (|z| ^ s) := by fun_prop
  rw [← lintegral_indicator hS, lintegral_reweight P hm _ (hf.indicator hS),
    ← lintegral_indicator hT]
  congr 1
  refine lintegral_congr_ae ((ae_pos_of_null hpos).mono fun p hp => ?_)
  have hiff : R < |p.2 / p.1| ↔ R * p.1 < |p.2| := by
    rw [abs_div, abs_of_pos hp, lt_div_iff₀ hp]
  dsimp only
  by_cases hmem : R * p.1 < |p.2|
  · rw [Set.indicator_of_mem (show p.2 / p.1 ∈ {z : ℝ | R < |z|} from hiff.2 hmem),
      Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | R * p.1 < |p.2|} from hmem), boundaryFamily,
      ← ENNReal.ofReal_mul hp.le, perspective_rpow hp]
  · rw [Set.indicator_of_notMem (show p.2 / p.1 ∉ {z : ℝ | R < |z|} from fun h => hmem (hiff.1 h)),
      Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | R * p.1 < |p.2|} from hmem), mul_zero]

/-! ### Tails of `|z|^s` along a sequence -/

/-- `sup_n ∫_{|z| > R} |z|^s dμ_n`. -/
def absTail (s : ℝ) (μ : ℕ → Measure ℝ) (R : ℝ) : ℝ≥0∞ :=
  ⨆ n, ∫⁻ z in {z | R < |z|}, ENNReal.ofReal (|z| ^ s) ∂(μ n)

lemma tail_set_eq (s : ℝ) (hs : 0 < s) {M : ℝ} (hM : 0 ≤ M) :
    {z : ℝ | ENNReal.ofReal M < ENNReal.ofReal (|z| ^ s)} = {z | M ^ (1 / s) < |z|} := by
  ext z
  simp only [Set.mem_ofPred_eq]
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM,
    ← Real.rpow_lt_rpow_iff hM (Real.rpow_nonneg (abs_nonneg z) s) (one_div_pos.2 hs),
    one_div, Real.rpow_rpow_inv (abs_nonneg z) hs.ne']

/-- Uniform integrability of `|z|^s` in `UITails` form is the vanishing of
`absTail` as `R → ∞`. -/
lemma uiTails_rpow_iff (s : ℝ) (hs : 0 < s) (μ : ℕ → Measure ℝ) :
    UITails μ (fun z => ENNReal.ofReal (|z| ^ s)) ↔ Tendsto (absTail s μ) atTop (𝓝 0) := by
  have key : ∀ M : ℝ, 0 ≤ M →
      (⨆ n, ∫⁻ z in {z | ENNReal.ofReal M < ENNReal.ofReal (|z| ^ s)},
        ENNReal.ofReal (|z| ^ s) ∂(μ n)) = absTail s μ (M ^ (1 / s)) := fun M hM => by
    rw [tail_set_eq s hs hM]
    rfl
  constructor
  · intro hU
    refine (hU.comp (tendsto_rpow_atTop hs)).congr' ((eventually_ge_atTop 0).mono fun R hR => ?_)
    simp only [Function.comp_apply]
    rw [key _ (Real.rpow_nonneg hR s), ← Real.rpow_mul hR, mul_one_div_cancel hs.ne',
      Real.rpow_one]
  · intro hT
    refine (hT.comp (tendsto_rpow_atTop (one_div_pos.2 hs))).congr'
      ((eventually_ge_atTop 0).mono fun M hM => ?_)
    simp only [Function.comp_apply]
    rw [key M hM]

/-! ### Uniform bounds on the numéraire means -/

lemma exists_pos_lower_bound {x : ℕ → ℝ} {L : ℝ} (hx : ∀ n, 0 < x n) (hL : 0 < L)
    (h : Tendsto x atTop (𝓝 L)) : ∃ c > 0, ∀ n, c ≤ x n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (lt_mem_nhds (half_lt_self hL)))
  rcases (Finset.range N).eq_empty_or_nonempty with h0 | hne
  · refine ⟨L / 2, half_pos hL, fun n => (hN n ?_).le⟩
    have : N = 0 := by simpa using h0
    omega
  · obtain ⟨n0, -, hn0⟩ := (Finset.range N).exists_min_image x hne
    refine ⟨min (L / 2) (x n0), lt_min (half_pos hL) (hx n0), fun n => ?_⟩
    by_cases hn : n < N
    · exact (min_le_right _ _).trans (hn0 n (Finset.mem_range.2 hn))
    · exact (min_le_left _ _).trans (hN n (not_lt.1 hn)).le

section Standing

variable {Q : ℕ → Measure (ℝ × ℝ)} {Qlim : Measure (ℝ × ℝ)}

lemma StandingSetting.exists_mean_bounds (h : StandingSetting Q Qlim) :
    ∃ c C : ℝ, 0 < c ∧ ∀ n, c ≤ numeraireMean (Q n) ∧ numeraireMean (Q n) ≤ C := by
  obtain ⟨c, hc, hcle⟩ := exists_pos_lower_bound h.mean_pos_n h.mean_pos h.tendsto_mean
  obtain ⟨C, hC⟩ := h.tendsto_mean.bddAbove_range
  exact ⟨c, C, hc, fun n => ⟨hcle n, hC ⟨n, rfl⟩⟩⟩

lemma StandingSetting.ratio_eq (h : StandingSetting Q Qlim) (s R : ℝ) (n : ℕ) :
    ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂(Q n) =
      (∫⁻ z in {z | R < |z|}, ENNReal.ofReal (|z| ^ s) ∂(reweight (Q n))) *
        ENNReal.ofReal (numeraireMean (Q n)) := by
  rw [tail_reweight (Q n) (h.pos n) (h.mean_pos_n n) s R,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 (h.mean_pos_n n)).ne' ENNReal.ofReal_ne_top]

/-- **Theorem 3.3.** -/
theorem StandingSetting.exact_two_way (h : StandingSetting Q Qlim) {s : ℝ} (hs : 1 ≤ s) :
    List.TFAE
      [ HasFiniteMoment s (reweight Qlim) ∧ (∀ n, HasFiniteMoment s (reweight (Q n))) ∧
          Tendsto (fun n => wasserstein s (reweight (Q n)) (reweight Qlim)) atTop (𝓝 0),
        (∀ n, ∫⁻ p, boundaryFamily s p ∂(Q n) < ∞) ∧ boundaryIntegral s Qlim < ∞ ∧
          Tendsto (fun n => ∫⁻ p, boundaryFamily s p ∂(Q n)) atTop
            (𝓝 (boundaryIntegral s Qlim)),
        Tendsto (ratioTail s Q) atTop (𝓝 0) ] := by
  have hs0 : 0 < s := by linarith
  have hΓ := h.isProbabilityMeasure_reweight_n
  have hΓlim := h.isProbabilityMeasure_reweight_lim'
  have hw := h.weakConv_reweight
  have hφc : Continuous fun z : ℝ => |z| ^ s :=
    continuous_abs.rpow_const fun _ => Or.inr hs0.le
  have hφ0 : ∀ z : ℝ, 0 ≤ |z| ^ s := fun z => Real.rpow_nonneg (abs_nonneg z) s
  have hm0 : ∀ n, ENNReal.ofReal (numeraireMean (Q n)) ≠ 0 := fun n =>
    (ENNReal.ofReal_pos.2 (h.mean_pos_n n)).ne'
  have hmL0 : ENNReal.ofReal (numeraireMean Qlim) ≠ 0 := (ENNReal.ofReal_pos.2 h.mean_pos).ne'
  have hmomn : ∀ n, moment s (reweight (Q n)) =
      (∫⁻ p, boundaryFamily s p ∂(Q n)) / ENNReal.ofReal (numeraireMean (Q n)) := fun n =>
    moment_reweight (Q n) (h.pos n) (h.mean_pos_n n) s
  have hmomL : moment s (reweight Qlim) =
      boundaryIntegral s Qlim / ENNReal.ofReal (numeraireMean Qlim) :=
    moment_reweight_lim Qlim h.mean_pos s
  have hEn : ∀ n, ∫⁻ p, boundaryFamily s p ∂(Q n) =
      moment s (reweight (Q n)) * ENNReal.ofReal (numeraireMean (Q n)) := fun n => by
    rw [hmomn n, ENNReal.div_mul_cancel (hm0 n) ENNReal.ofReal_ne_top]
  have hIs : boundaryIntegral s Qlim =
      moment s (reweight Qlim) * ENNReal.ofReal (numeraireMean Qlim) := by
    rw [hmomL, ENNReal.div_mul_cancel hmL0 ENNReal.ofReal_ne_top]
  have hmeanE : Tendsto (fun n => ENNReal.ofReal (numeraireMean (Q n))) atTop
      (𝓝 (ENNReal.ofReal (numeraireMean Qlim))) := ENNReal.tendsto_ofReal h.tendsto_mean
  -- (ii) gives convergence of the reweighted moments
  have h2mom : ((∀ n, ∫⁻ p, boundaryFamily s p ∂(Q n) < ∞) ∧ boundaryIntegral s Qlim < ∞ ∧
      Tendsto (fun n => ∫⁻ p, boundaryFamily s p ∂(Q n)) atTop
        (𝓝 (boundaryIntegral s Qlim))) →
      (∀ n, moment s (reweight (Q n)) < ∞) ∧ moment s (reweight Qlim) < ∞ ∧
        Tendsto (fun n => moment s (reweight (Q n))) atTop (𝓝 (moment s (reweight Qlim))) := by
    rintro ⟨hfin, hIfin, htend⟩
    refine ⟨fun n => ?_, ?_, ?_⟩
    · rw [hmomn n]
      exact ENNReal.div_lt_top (hfin n).ne (hm0 n)
    · rw [hmomL]
      exact ENNReal.div_lt_top hIfin.ne hmL0
    · have e : (fun n => moment s (reweight (Q n))) = fun n =>
          (∫⁻ p, boundaryFamily s p ∂(Q n)) / ENNReal.ofReal (numeraireMean (Q n)) :=
        funext hmomn
      rw [e, hmomL]
      exact ENNReal.Tendsto.div htend (Or.inr hmL0) hmeanE (Or.inl ENNReal.ofReal_ne_top)
  -- convergence of the reweighted moments gives (ii)
  have hmom2 : (∀ n, moment s (reweight (Q n)) < ∞) → moment s (reweight Qlim) < ∞ →
      Tendsto (fun n => moment s (reweight (Q n))) atTop (𝓝 (moment s (reweight Qlim))) →
      (∀ n, ∫⁻ p, boundaryFamily s p ∂(Q n) < ∞) ∧ boundaryIntegral s Qlim < ∞ ∧
        Tendsto (fun n => ∫⁻ p, boundaryFamily s p ∂(Q n)) atTop
          (𝓝 (boundaryIntegral s Qlim)) := by
    intro hfin hlim htend
    refine ⟨fun n => ?_, ?_, ?_⟩
    · rw [hEn n]
      exact ENNReal.mul_lt_top (hfin n) ENNReal.ofReal_lt_top
    · rw [hIs]
      exact ENNReal.mul_lt_top hlim ENNReal.ofReal_lt_top
    · have e : (fun n => ∫⁻ p, boundaryFamily s p ∂(Q n)) = fun n =>
          moment s (reweight (Q n)) * ENNReal.ofReal (numeraireMean (Q n)) := funext hEn
      rw [e, hIs]
      exact ENNReal.Tendsto.mul htend (Or.inr ENNReal.ofReal_ne_top) hmeanE (Or.inr hlim.ne)
  tfae_have 1 → 2 := by
    rintro ⟨hfinL, hfin, hW⟩
    exact hmom2 hfin hfinL (tendsto_moment_of_tendsto_wasserstein s hs hfinL hW)
  tfae_have 2 → 1 := by
    intro h2
    obtain ⟨hfin, hfinL, htend⟩ := h2mom h2
    exact ⟨hfinL, hfin, tendsto_wasserstein_of_weakConv s hs hΓ hw hfinL htend⟩
  tfae_have 2 → 3 := by
    intro h2
    obtain ⟨hfin, hfinL, htend⟩ := h2mom h2
    have hU : UITails (fun n => reweight (Q n)) (fun z => ENNReal.ofReal (|z| ^ s)) :=
      uiTails_of_tendsto_lintegral hΓ hΓlim hw (fun z => |z| ^ s) hφc hφ0 hfin hfinL htend
    have hT := (uiTails_rpow_iff s hs0 _).1 hU
    obtain ⟨c, C, hc, hbd⟩ := h.exists_mean_bounds
    have hle : ∀ R, ratioTail s Q R ≤
        absTail s (fun n => reweight (Q n)) R * ENNReal.ofReal C := fun R => by
      refine iSup_le fun n => ?_
      rw [h.ratio_eq s R n]
      exact mul_le_mul' (le_iSup (fun n => ∫⁻ z in {z | R < |z|}, ENNReal.ofReal (|z| ^ s)
        ∂(reweight (Q n))) n) (ENNReal.ofReal_le_ofReal (hbd n).2)
    have hlim : Tendsto (fun R => absTail s (fun n => reweight (Q n)) R * ENNReal.ofReal C)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hT (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hle
  tfae_have 3 → 2 := by
    intro h3
    obtain ⟨c, C, hc, hbd⟩ := h.exists_mean_bounds
    have hle : ∀ R, absTail s (fun n => reweight (Q n)) R ≤
        ratioTail s Q R / ENNReal.ofReal c := fun R => by
      refine iSup_le fun n => ?_
      rw [tail_reweight (Q n) (h.pos n) (h.mean_pos_n n) s R]
      exact ENNReal.div_le_div (le_iSup (fun n => ∫⁻ p in {p | R * p.1 < |p.2|},
        boundaryFamily s p ∂(Q n)) n) (ENNReal.ofReal_le_ofReal (hbd n).1)
    have hlim : Tendsto (fun R => ratioTail s Q R / ENNReal.ofReal c) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.div_const h3 (Or.inr (ENNReal.ofReal_pos.2 hc).ne')
    have hT : Tendsto (absTail s (fun n => reweight (Q n))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle
    have hU := (uiTails_rpow_iff s hs0 _).2 hT
    obtain ⟨hfinL, htend⟩ := tendsto_lintegral_of_uiTails hΓ hΓlim hw (fun z => |z| ^ s) hφc hφ0 hU
    obtain ⟨C', hC', hC'b⟩ := exists_bound_of_uiTails hΓ (fun z => |z| ^ s) hφc hU
    exact hmom2 (fun n => (hC'b n).trans_lt hC') hfinL htend
  tfae_finish

end Standing

end NumeraireStability
