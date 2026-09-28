/-
# Basic facts about `W_s` on `ℝ`

Minkowski's inequality through a coupling gives
`|M_s(μ)^{1/s} - M_s(ν)^{1/s}| ≤ W_s(μ, ν)`, hence `W_s → 0` forces convergence
of `s`-th moments; and `W_s(μ, δ_0) = M_s(μ)^{1/s}`.
-/
import NumeraireStability.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace NumeraireStability

/-- The transport cost `∫ |x - y|^s dπ` of a coupling `π`. -/
def cost (s : ℝ) (π : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| ^ s) ∂π

/-- The `s`-th absolute moment `∫ |x|^s dμ`. -/
def moment (s : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂μ

lemma hasFiniteMoment_iff_moment (s : ℝ) (μ : Measure ℝ) :
    HasFiniteMoment s μ ↔ moment s μ < ∞ :=
  Iff.rfl

lemma wasserstein_le_cost (s : ℝ) (hs : 0 < s) {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}
    (hπ : IsCoupling π μ ν) : wasserstein s μ ν ≤ cost s π ^ (1 / s) :=
  ENNReal.rpow_le_rpow (iInf₂_le π hπ) (by positivity)

lemma eLpNorm_eq_rpow {α : Type*} [MeasurableSpace α] (s : ℝ) (hs : 1 ≤ s) (ρ : Measure α)
    (f : α → ℝ) (hf : AEStronglyMeasurable f ρ) :
    eLpNorm f (ENNReal.ofReal s) ρ = (∫⁻ a, ENNReal.ofReal (|f a| ^ s) ∂ρ) ^ (1 / s) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal (by linarith)]
  congr 1
  refine lintegral_congr fun a => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith)]

lemma moment_eq_fst {s : ℝ} {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ} (hπ : IsCoupling π μ ν) :
    moment s μ = ∫⁻ p, ENNReal.ofReal (|p.1| ^ s) ∂π := by
  rw [moment, ← hπ.1, lintegral_map (by fun_prop) measurable_fst]

lemma moment_eq_snd {s : ℝ} {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ} (hπ : IsCoupling π μ ν) :
    moment s ν = ∫⁻ p, ENNReal.ofReal (|p.2| ^ s) ∂π := by
  rw [moment, ← hπ.2, lintegral_map (by fun_prop) measurable_snd]

/-- Minkowski through a coupling: `M(μ)^{1/s} ≤ cost(π)^{1/s} + M(ν)^{1/s}`. -/
lemma moment_rpow_le_cost_add (s : ℝ) (hs : 1 ≤ s) {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}
    (hπ : IsCoupling π μ ν) :
    moment s μ ^ (1 / s) ≤ cost s π ^ (1 / s) + moment s ν ^ (1 / s) := by
  rw [moment_eq_fst hπ, moment_eq_snd hπ, cost,
    ← eLpNorm_eq_rpow s hs π (fun p => p.1) (by fun_prop),
    ← eLpNorm_eq_rpow s hs π (fun p => p.1 - p.2) (by fun_prop),
    ← eLpNorm_eq_rpow s hs π (fun p => p.2) (by fun_prop)]
  have h := eLpNorm_add_le (μ := π) (f := fun p : ℝ × ℝ => p.1 - p.2) (g := fun p => p.2)
    (ENNReal.one_le_ofReal.2 hs)
  have e : ((fun p : ℝ × ℝ => p.1 - p.2) + fun p => p.2) = fun p => p.1 := by
    funext p
    simp
  rwa [e] at h

/-- Minkowski through a coupling, other marginal. -/
lemma moment_rpow_le_cost_add' (s : ℝ) (hs : 1 ≤ s) {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}
    (hπ : IsCoupling π μ ν) :
    moment s ν ^ (1 / s) ≤ cost s π ^ (1 / s) + moment s μ ^ (1 / s) := by
  rw [moment_eq_fst hπ, moment_eq_snd hπ, cost,
    ← eLpNorm_eq_rpow s hs π (fun p => p.2) (by fun_prop),
    ← eLpNorm_eq_rpow s hs π (fun p => p.1) (by fun_prop)]
  have hc : (∫⁻ p, ENNReal.ofReal (|p.1 - p.2| ^ s) ∂π) =
      ∫⁻ p, ENNReal.ofReal (|p.2 - p.1| ^ s) ∂π := by
    congr 1
    ext p
    rw [abs_sub_comm]
  rw [hc, ← eLpNorm_eq_rpow s hs π (fun p => p.2 - p.1) (by fun_prop)]
  have h := eLpNorm_add_le (μ := π) (f := fun p : ℝ × ℝ => p.2 - p.1) (g := fun p => p.1)
    (ENNReal.one_le_ofReal.2 hs)
  have e : ((fun p : ℝ × ℝ => p.2 - p.1) + fun p => p.1) = fun p => p.2 := by
    funext p
    simp
  rwa [e] at h

/-- `M(μ)^{1/s} ≤ W_s(μ, ν) + M(ν)^{1/s}`. -/
lemma moment_rpow_le_wasserstein_add (s : ℝ) (hs : 1 ≤ s) (μ ν : Measure ℝ) :
    moment s μ ^ (1 / s) ≤ wasserstein s μ ν + moment s ν ^ (1 / s) := by
  have hs0 : 0 < s := by linarith
  rw [← tsub_le_iff_right, wasserstein, one_div, ENNReal.le_rpow_inv_iff hs0]
  refine le_iInf₂ fun π hπ => ?_
  rw [← ENNReal.le_rpow_inv_iff hs0, tsub_le_iff_right]
  simpa only [one_div, cost] using moment_rpow_le_cost_add s hs hπ

/-- `M(ν)^{1/s} ≤ W_s(μ, ν) + M(μ)^{1/s}`. -/
lemma moment_rpow_le_wasserstein_add' (s : ℝ) (hs : 1 ≤ s) (μ ν : Measure ℝ) :
    moment s ν ^ (1 / s) ≤ wasserstein s μ ν + moment s μ ^ (1 / s) := by
  have hs0 : 0 < s := by linarith
  rw [← tsub_le_iff_right, wasserstein, one_div, ENNReal.le_rpow_inv_iff hs0]
  refine le_iInf₂ fun π hπ => ?_
  rw [← ENNReal.le_rpow_inv_iff hs0, tsub_le_iff_right]
  simpa only [one_div, cost] using moment_rpow_le_cost_add' s hs hπ

/-- `W_s(μ_n, ν) → 0` forces `M_s(μ_n) → M_s(ν)`. -/
theorem tendsto_moment_of_tendsto_wasserstein (s : ℝ) (hs : 1 ≤ s) {μ : ℕ → Measure ℝ}
    {ν : Measure ℝ} (hν : moment s ν < ∞)
    (hW : Tendsto (fun n => wasserstein s (μ n) ν) atTop (𝓝 0)) :
    Tendsto (fun n => moment s (μ n)) atTop (𝓝 (moment s ν)) := by
  have hs0 : 0 < s := by linarith
  set b := moment s ν ^ (1 / s)
  have hb : b ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hν.ne
  have hroot : Tendsto (fun n => moment s (μ n) ^ (1 / s)) atTop (𝓝 b) := by
    have hup : Tendsto (fun n => wasserstein s (μ n) ν + b) atTop (𝓝 b) := by
      simpa using hW.add (tendsto_const_nhds (x := b))
    have hlow : Tendsto (fun n => b - wasserstein s (μ n) ν) atTop (𝓝 b) := by
      simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := b)) hW (Or.inl hb)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_)
      (fun n => moment_rpow_le_wasserstein_add s hs _ _)
    rw [tsub_le_iff_right, add_comm]
    exact moment_rpow_le_wasserstein_add' s hs _ _
  have h := ((ENNReal.continuous_rpow_const (y := s)).tendsto b).comp hroot
  simp only [b, one_div, Function.comp_def, ENNReal.rpow_inv_rpow hs0.ne'] at h
  exact h

/-- `W_s(μ, δ_0) = M_s(μ)^{1/s}` for a probability measure `μ`. -/
theorem wasserstein_dirac_zero (s : ℝ) (hs : 1 ≤ s) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    wasserstein s μ (Measure.dirac 0) = moment s μ ^ (1 / s) := by
  have hs0 : 0 < s := by linarith
  refine le_antisymm ?_ ?_
  · have hπ : IsCoupling (μ.map fun x => (x, (0 : ℝ))) μ (Measure.dirac 0) := by
      constructor
      · rw [Measure.map_map measurable_fst (by fun_prop)]
        exact Measure.map_id
      · rw [Measure.map_map measurable_snd (by fun_prop)]
        simp [Function.comp_def, Measure.map_const]
    refine (wasserstein_le_cost s hs0 hπ).trans (le_of_eq ?_)
    rw [cost, lintegral_map (by fun_prop) (by fun_prop), moment]
    simp
  · have h := moment_rpow_le_wasserstein_add s hs μ (Measure.dirac 0)
    have h0 : moment s (Measure.dirac (0 : ℝ)) = 0 := by
      rw [moment, lintegral_dirac]
      simp [Real.zero_rpow hs0.ne']
    rwa [h0, ENNReal.zero_rpow_of_pos (by positivity), add_zero] at h

end NumeraireStability
