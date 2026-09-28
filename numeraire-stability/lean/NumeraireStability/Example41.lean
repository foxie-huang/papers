/-
# Example 4.1: the boundary is attained with bounded inputs
-/
import NumeraireStability.TwoAtoms
import NumeraireStability.Corollary

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

section Atom

variable {s ε : ℝ}

lemma exTwoAtom_eq : exTwoAtom s ε = twoAtoms (1 - ε) ε (1, 0) (ε ^ (1 / (s - 1)), 1) := rfl

lemma atom_pos (hε : 0 < ε ∧ ε < 1) : 0 < ε ^ (1 / (s - 1)) := Real.rpow_pos_of_pos hε.1 _

lemma atom_le_one (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) : ε ^ (1 / (s - 1)) ≤ 1 :=
  Real.rpow_le_one hε.1.le hε.2.le (one_div_nonneg.2 (by linarith))

lemma exTwoAtom_mean' (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    numeraireMean (exTwoAtom s ε) = 1 - ε + ε * ε ^ (1 / (s - 1)) := by
  rw [exTwoAtom_eq, numeraireMean_twoAtoms (by linarith [hε.2]) hε.1.le zero_le_one
    (atom_pos hε).le]
  ring

lemma exTwoAtom_mean_pos (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    0 < numeraireMean (exTwoAtom s ε) := by
  rw [exTwoAtom_mean' hs hε]
  have := mul_pos hε.1 (atom_pos (s := s) hε)
  linarith [hε.2]

lemma exTwoAtom_mean_le_one (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    numeraireMean (exTwoAtom s ε) ≤ 1 := by
  rw [exTwoAtom_mean' hs hε]
  have := mul_le_mul_of_nonneg_left (atom_le_one hs hε) hε.1.le
  linarith

lemma reweight_exTwoAtom' (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    reweight (exTwoAtom s ε) =
      ENNReal.ofReal ((1 - ε) / numeraireMean (exTwoAtom s ε)) • Measure.dirac 0 +
        ENNReal.ofReal (ε * ε ^ (1 / (s - 1)) / numeraireMean (exTwoAtom s ε)) •
          Measure.dirac (1 / ε ^ (1 / (s - 1))) := by
  rw [exTwoAtom_eq, reweight_twoAtoms (by linarith [hε.2]) hε.1.le]
  simp only [twoAtoms, zero_div, mul_one_div, mul_div_assoc]

lemma isProbabilityMeasure_exTwoAtom (hε : 0 < ε ∧ ε < 1) :
    IsProbabilityMeasure (exTwoAtom s ε) :=
  isProbabilityMeasure_twoAtoms (by linarith [hε.2]) hε.1.le (by ring) _ _

lemma exTwoAtom_pos (hε : 0 < ε ∧ ε < 1) : exTwoAtom s ε {p | p.1 ≤ 0} = 0 :=
  twoAtoms_null _ _ _ _ (fun h => absurd (show (1 : ℝ) ≤ 0 from h) (by norm_num))
    (fun h => absurd (show ε ^ (1 / (s - 1)) ≤ 0 from h) (not_le.2 (atom_pos hε)))

lemma isProbabilityMeasure_reweight_exTwoAtom (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) :
    IsProbabilityMeasure (reweight (exTwoAtom s ε)) := by
  have := isProbabilityMeasure_exTwoAtom (s := s) hε
  exact NumeraireStability.isProbabilityMeasure_reweight _
    (measure_mono_null (fun p (hp : p.1 < 0) => (show p.1 ≤ 0 from hp.le)) (exTwoAtom_pos hε))
    (exTwoAtom_mean_pos hs hε)

/-- `ε a (1/a)^σ = ε^{(s-σ)/(s-1)}` for `a = ε^{1/(s-1)}`. -/
lemma two_atom_moment_real (hs : 1 < s) (hε : 0 < ε) (σ : ℝ) :
    ε * ε ^ (1 / (s - 1)) * |1 / ε ^ (1 / (s - 1))| ^ σ = ε ^ ((s - σ) / (s - 1)) := by
  have hs1 : s - 1 ≠ 0 := by linarith
  have ha : 0 < ε ^ (1 / (s - 1)) := Real.rpow_pos_of_pos hε _
  rw [abs_of_pos (one_div_pos.2 ha), Real.div_rpow zero_le_one ha.le, Real.one_rpow,
    ← Real.rpow_mul hε.le]
  have e1 : ε * ε ^ (1 / (s - 1)) * (1 / ε ^ (1 / (s - 1) * σ)) =
      ε ^ (1 + 1 / (s - 1) - 1 / (s - 1) * σ) := by
    rw [Real.rpow_sub hε, Real.rpow_add hε, Real.rpow_one]
    ring
  rw [e1]
  congr 1
  field_simp
  ring

lemma exTwoAtom_moment' (hs : 1 < s) (hε : 0 < ε ∧ ε < 1) {σ : ℝ} (hσ : 1 ≤ σ) :
    ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s ε)) =
      ENNReal.ofReal (ε ^ ((s - σ) / (s - 1)) / numeraireMean (exTwoAtom s ε)) := by
  have hm := exTwoAtom_mean_pos hs hε
  rw [reweight_exTwoAtom' hs hε]
  change ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(twoAtoms _ _ _ _) = _
  rw [lintegral_twoAtoms, abs_zero, Real.zero_rpow (by linarith), ENNReal.ofReal_zero, mul_zero,
    zero_add, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hε.1.le (atom_pos hε).le) hm.le)]
  congr 1
  rw [div_mul_eq_mul_div, two_atom_moment_real hs hε.1]

end Atom

section Main

variable {s : ℝ} {ε : ℕ → ℝ}

lemma tendsto_eps_atom (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ε n * ε n ^ (1 / (s - 1))) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => mul_nonneg (hε n).1.le (atom_pos (hε n)).le) (fun n => ?_) hεlim
  have := mul_le_mul_of_nonneg_left (atom_le_one hs (hε n)) (hε n).1.le
  linarith

lemma tendsto_exTwoAtom_mean (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => numeraireMean (exTwoAtom s (ε n))) atTop (𝓝 1) := by
  have e : (fun n => numeraireMean (exTwoAtom s (ε n))) =
      fun n => 1 - ε n + ε n * ε n ^ (1 / (s - 1)) :=
    funext fun n => exTwoAtom_mean' hs (hε n)
  rw [e]
  simpa using (tendsto_const_nhds.sub hεlim).add (tendsto_eps_atom hs hε hεlim)

/-- (S1)–(S2) hold for Example 4.1, with limit `δ_{(1,0)}`. -/
lemma standing_exTwoAtom (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    StandingSetting (fun n => exTwoAtom s (ε n)) (Measure.dirac (1, 0)) where
  prob n := isProbabilityMeasure_exTwoAtom (hε n)
  prob_lim := inferInstance
  pos n := exTwoAtom_pos (hε n)
  lim_supp := by simp [Measure.dirac_apply]
  weak := by
    intro f
    have e : (fun n => ∫ p, f p ∂(exTwoAtom s (ε n))) = fun n =>
        (1 - ε n) * f (1, 0) + ε n * f (ε n ^ (1 / (s - 1)), 1) :=
      funext fun n => integral_twoAtoms f (by linarith [(hε n).2]) (hε n).1.le _ _
    rw [e, integral_dirac]
    have h1 : Tendsto (fun n => (1 - ε n) * f (1, 0)) atTop (𝓝 (f (1, 0))) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hεlim).mul_const (f (1, 0))
      rwa [sub_zero, one_mul] at h
    have h2 : Tendsto (fun n => ε n * f (ε n ^ (1 / (s - 1)), 1)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by have h := hεlim.mul_const ‖f‖; rwa [zero_mul] at h)
      rw [norm_mul, Real.norm_of_nonneg (hε n).1.le]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hε n).1.le
    simpa using h1.add h2
  ui := by
    show Tendsto (fun M : ℝ => ⨆ n, ∫⁻ p in {p : ℝ × ℝ | ENNReal.ofReal M < ENNReal.ofReal p.1},
      ENNReal.ofReal p.1 ∂(exTwoAtom s (ε n))) atTop (𝓝 0)
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun M hM => ?_)
    refine (le_antisymm (iSup_le fun n => le_of_eq (setLIntegral_measure_zero _ _ ?_))
      zero_le).symm
    exact twoAtoms_null _ _ _ _
      (fun h => absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ M from hM))))
      (fun h => absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal
        ((atom_le_one hs (hε n)).trans hM))))
  mean_pos := by
    rw [numeraireMean, integral_dirac]
    norm_num

lemma reweight_dirac_one_zero : reweight (Measure.dirac ((1 : ℝ), (0 : ℝ))) = Measure.dirac 0 := by
  rw [reweight_dirac (by norm_num)]
  norm_num

lemma weakConv_reweight_exTwoAtom (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    WeakConv (fun n => reweight (exTwoAtom s (ε n))) (Measure.dirac 0) := by
  intro f
  have hm := tendsto_exTwoAtom_mean hs hε hεlim
  have hmpos : ∀ n, 0 < numeraireMean (exTwoAtom s (ε n)) := fun n =>
    exTwoAtom_mean_pos hs (hε n)
  have hc2nn : ∀ n, 0 ≤ ε n * ε n ^ (1 / (s - 1)) / numeraireMean (exTwoAtom s (ε n)) :=
    fun n => div_nonneg (mul_nonneg (hε n).1.le (atom_pos (hε n)).le) (hmpos n).le
  have e : (fun n => ∫ z, f z ∂(reweight (exTwoAtom s (ε n)))) = fun n =>
      (1 - ε n) / numeraireMean (exTwoAtom s (ε n)) * f 0 +
        ε n * ε n ^ (1 / (s - 1)) / numeraireMean (exTwoAtom s (ε n)) *
          f (1 / ε n ^ (1 / (s - 1))) := funext fun n => by
    rw [reweight_exTwoAtom' hs (hε n)]
    exact integral_twoAtoms f (div_nonneg (by linarith [(hε n).2]) (hmpos n).le) (hc2nn n) _ _
  rw [e, integral_dirac]
  have hc1 : Tendsto (fun n => (1 - ε n) / numeraireMean (exTwoAtom s (ε n))) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hεlim).div hm one_ne_zero
    rw [sub_zero, div_one] at h
    exact h
  have hc2 : Tendsto (fun n => ε n * ε n ^ (1 / (s - 1)) / numeraireMean (exTwoAtom s (ε n)))
      atTop (𝓝 0) := by
    have h := (tendsto_eps_atom hs hε hεlim).div hm one_ne_zero
    rw [zero_div] at h
    exact h
  have t1 : Tendsto (fun n => (1 - ε n) / numeraireMean (exTwoAtom s (ε n)) * f 0) atTop
      (𝓝 (f 0)) := by
    have h := hc1.mul_const (f 0)
    rwa [one_mul] at h
  have t2 : Tendsto (fun n => ε n * ε n ^ (1 / (s - 1)) / numeraireMean (exTwoAtom s (ε n)) *
      f (1 / ε n ^ (1 / (s - 1)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by have h := hc2.mul_const ‖f‖; rwa [zero_mul] at h)
    rw [norm_mul, Real.norm_of_nonneg (hc2nn n)]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (1 / ε n ^ (1 / (s - 1)))) (hc2nn n)
  simpa using t1.add t2

lemma moment_exTwoAtom_eq (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1) {σ : ℝ} (hσ : 1 ≤ σ) :
    (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n)))) =
      fun n => ENNReal.ofReal (ε n ^ ((s - σ) / (s - 1)) / numeraireMean (exTwoAtom s (ε n))) :=
  funext fun n => exTwoAtom_moment' hs (hε n) hσ

lemma tendsto_moment_exTwoAtom_lt (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) {σ : ℝ} (hσ1 : 1 ≤ σ) (hσs : σ < s) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n))))
      atTop (𝓝 0) := by
  rw [moment_exTwoAtom_eq hs hε hσ1]
  have hp : 0 < (s - σ) / (s - 1) := div_pos (by linarith) (by linarith)
  have h1 := (hεlim.rpow_const (Or.inr hp.le)).div (tendsto_exTwoAtom_mean hs hε hεlim)
    one_ne_zero
  rw [Real.zero_rpow hp.ne', zero_div] at h1
  simpa using ENNReal.tendsto_ofReal h1

lemma tendsto_moment_exTwoAtom_eq (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ s) ∂(reweight (exTwoAtom s (ε n))))
      atTop (𝓝 1) := by
  rw [moment_exTwoAtom_eq hs hε hs.le]
  simp only [sub_self, zero_div, Real.rpow_zero]
  simpa using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1 : ℝ))).div
    (tendsto_exTwoAtom_mean hs hε hεlim) one_ne_zero)

lemma tendsto_moment_exTwoAtom_gt (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) {σ : ℝ} (hσs : s < σ) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n))))
      atTop (𝓝 ∞) := by
  rw [moment_exTwoAtom_eq hs hε (by linarith)]
  have hp : (s - σ) / (s - 1) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hεw : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall fun n => (hε n).1⟩
  have hbig := (tendsto_rpow_neg_nhdsGT_zero hp).comp hεw
  have hbig' : Tendsto (fun n => ε n ^ ((s - σ) / (s - 1)) / numeraireMean (exTwoAtom s (ε n)))
      atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) hbig
    exact le_div_self (Real.rpow_nonneg (hε n).1.le _) (exTwoAtom_mean_pos hs (hε n))
      (exTwoAtom_mean_le_one hs (hε n))
  exact ENNReal.tendsto_ofReal_atTop.comp hbig'

/-- **Example 4.1.** -/
theorem example_4_1' (hs : 1 < s) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    StandingSetting (fun n => exTwoAtom s (ε n)) (Measure.dirac (1, 0)) ∧
    Measure.dirac ((1 : ℝ), (0 : ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 ∧
    reweight (Measure.dirac ((1 : ℝ), (0 : ℝ))) = Measure.dirac 0 ∧
    WeakConv (fun n => reweight (exTwoAtom s (ε n))) (Measure.dirac 0) ∧
    (∀ σ, 1 ≤ σ → σ < s →
      Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n))))
        atTop (𝓝 0)) ∧
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ s) ∂(reweight (exTwoAtom s (ε n))))
      atTop (𝓝 1) ∧
    (∀ σ, s < σ →
      Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n))))
        atTop (𝓝 ∞)) ∧
    (∀ σ, 1 ≤ σ → σ < s →
      Tendsto (fun n => wasserstein σ (reweight (exTwoAtom s (ε n))) (Measure.dirac 0))
        atTop (𝓝 0)) ∧
    ¬ Tendsto (fun n => wasserstein s (reweight (exTwoAtom s (ε n))) (Measure.dirac 0))
        atTop (𝓝 0) ∧
    (∀ σ, 1 ≤ σ → σ < s →
      UnifIntegrableFamily (fun n => exTwoAtom s (ε n)) (boundaryFamily σ)) ∧
    ¬ UnifIntegrableFamily (fun n => exTwoAtom s (ε n)) (boundaryFamily s) := by
  have hst := standing_exTwoAtom hs hε hεlim
  have h0 : Measure.dirac ((1 : ℝ), (0 : ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    simp [Measure.dirac_apply]
  have hprob : ∀ n, IsProbabilityMeasure (reweight (exTwoAtom s (ε n))) := fun n =>
    isProbabilityMeasure_reweight_exTwoAtom hs (hε n)
  -- `W_σ(Γ_n, δ_0) = M_σ(Γ_n)^{1/σ}`
  have hWform : ∀ σ, 1 ≤ σ → (fun n => wasserstein σ (reweight (exTwoAtom s (ε n)))
      (Measure.dirac 0)) = fun n => (∫⁻ z, ENNReal.ofReal (|z| ^ σ)
        ∂(reweight (exTwoAtom s (ε n)))) ^ (1 / σ) := fun σ hσ => funext fun n => by
    have := hprob n
    exact wasserstein_dirac_zero σ hσ _
  have hWlt : ∀ σ, 1 ≤ σ → σ < s → Tendsto (fun n => wasserstein σ
      (reweight (exTwoAtom s (ε n))) (Measure.dirac 0)) atTop (𝓝 0) := by
    intro σ hσ1 hσs
    rw [hWform σ hσ1]
    have h := ((ENNReal.continuous_rpow_const (y := 1 / σ)).tendsto 0).comp
      (tendsto_moment_exTwoAtom_lt hs hε hεlim hσ1 hσs)
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.2 (by linarith))] at h
  have hWs : ¬ Tendsto (fun n => wasserstein s (reweight (exTwoAtom s (ε n)))
      (Measure.dirac 0)) atTop (𝓝 0) := by
    intro hW0
    rw [hWform s hs.le] at hW0
    have h := ((ENNReal.continuous_rpow_const (y := 1 / s)).tendsto 1).comp
      (tendsto_moment_exTwoAtom_eq hs hε hεlim)
    rw [ENNReal.one_rpow] at h
    exact one_ne_zero (tendsto_nhds_unique h hW0)
  -- the uniform-integrability claims, through Corollary 3.4(b)
  have hfin : ∀ σ, 1 ≤ σ → (∀ n, HasFiniteMoment σ (reweight (exTwoAtom s (ε n)))) := by
    intro σ hσ n
    show ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(reweight (exTwoAtom s (ε n))) < ∞
    rw [exTwoAtom_moment' hs (hε n) hσ]
    exact ENNReal.ofReal_lt_top
  have hfin0 : ∀ σ, 1 ≤ σ → HasFiniteMoment σ (reweight (Measure.dirac ((1 : ℝ), (0 : ℝ)))) := by
    intro σ hσ
    rw [reweight_dirac_one_zero]
    show ∫⁻ z, ENNReal.ofReal (|z| ^ σ) ∂(Measure.dirac (0 : ℝ)) < ∞
    rw [lintegral_dirac]
    exact ENNReal.ofReal_lt_top
  refine ⟨hst, h0, reweight_dirac_one_zero, weakConv_reweight_exTwoAtom hs hε hεlim,
    fun σ hσ1 hσs => tendsto_moment_exTwoAtom_lt hs hε hεlim hσ1 hσs,
    tendsto_moment_exTwoAtom_eq hs hε hεlim,
    fun σ hσs => tendsto_moment_exTwoAtom_gt hs hε hεlim hσs, hWlt, hWs, ?_, ?_⟩
  · intro σ hσ1 hσs
    refine (hst.boundary_free_iff h0 hσ1).1 ⟨hfin0 σ hσ1, hfin σ hσ1, ?_⟩
    rw [reweight_dirac_one_zero]
    exact hWlt σ hσ1 hσs
  · intro hU
    obtain ⟨-, -, hW⟩ := (hst.boundary_free_iff h0 hs.le).2 hU
    rw [reweight_dirac_one_zero] at hW
    exact hWs hW

end Main

end NumeraireStability
