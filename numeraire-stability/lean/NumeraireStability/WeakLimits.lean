/-
# Weak convergence and uniformly integrable tails

For probability measures `μ_n → ν` weakly and a continuous `φ ≥ 0` whose
tails are uniformly integrable along `μ_n`, `∫ φ dμ_n → ∫ φ dν < ∞`
(`tendsto_lintegral_of_uiTails`).
-/
import NumeraireStability.Defs
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Order.Filter.ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

section General

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Uniformly integrable tails of `g` along the measures `μ n`:
`lim_{M → ∞} sup_n ∫_{g > M} g dμ_n = 0`. -/
def UITails (μ : ℕ → Measure X) (g : X → ℝ≥0∞) : Prop :=
  Tendsto (fun M : ℝ => ⨆ n, ∫⁻ x in {x | ENNReal.ofReal M < g x}, g x ∂(μ n))
    atTop (𝓝 0)

lemma unifIntegrableFamily_iff_uiTails (Q : ℕ → Measure (ℝ × ℝ)) (g : ℝ × ℝ → ℝ≥0∞) :
    UnifIntegrableFamily Q g ↔ UITails Q g :=
  Iff.rfl

/-- The truncation `min φ M⁺` of a nonnegative continuous `φ`, as a bounded
continuous function. -/
def truncBCF (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (M : ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (φ x) (max M 0), hφc.min continuous_const⟩ (max M 0) (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : 0 ≤ min (φ x) (max M 0) := le_min (hφ0 x) (le_max_right _ _)
      have h2 : min (φ x) (max M 0) ≤ max M 0 := min_le_right _ _
      have h3 : 0 ≤ min (φ y) (max M 0) := le_min (hφ0 y) (le_max_right _ _)
      have h4 : min (φ y) (max M 0) ≤ max M 0 := min_le_right _ _
      rw [abs_le]
      constructor <;> linarith)

@[simp] lemma truncBCF_apply (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (M : ℝ)
    (x : X) : truncBCF φ hφc hφ0 M x = min (φ x) (max M 0) :=
  rfl

lemma lintegral_trunc_eq (ρ : Measure X) [IsFiniteMeasure ρ] (φ : X → ℝ)
    (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (M : ℝ) :
    ∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂ρ =
      ENNReal.ofReal (∫ x, truncBCF φ hφc hφ0 M x ∂ρ) := by
  rw [ofReal_integral_eq_lintegral_ofReal ((truncBCF φ hφc hφ0 M).integrable ρ)
    (Eventually.of_forall fun x => le_min (hφ0 x) (le_max_right _ _))]
  rfl

/-- Weak convergence moves the truncated integrals. -/
lemma tendsto_lintegral_trunc {μ : ℕ → Measure X} {ν : Measure X}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) (hν : IsProbabilityMeasure ν) (hw : WeakConv μ ν)
    (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (M : ℝ) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂(μ n)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂ν)) := by
  simp_rw [lintegral_trunc_eq _ φ hφc hφ0 M]
  exact ENNReal.tendsto_ofReal (hw _)

/-- Pointwise: `φ ≤ min(φ, M⁺) + φ 1{φ > M}`, integrated. -/
lemma lintegral_le_trunc_add_tail (ρ : Measure X) (φ : X → ℝ) (hφc : Continuous φ)
    (M : ℝ) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ ≤
      ∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂ρ +
        ∫⁻ x in {x | ENNReal.ofReal M < ENNReal.ofReal (φ x)}, ENNReal.ofReal (φ x) ∂ρ := by
  have hmeas : MeasurableSet {x | ENNReal.ofReal M < ENNReal.ofReal (φ x)} :=
    measurableSet_lt measurable_const hφc.measurable.ennreal_ofReal
  rw [← lintegral_indicator hmeas, ← lintegral_add_left
    (hφc.measurable.min measurable_const).ennreal_ofReal]
  refine lintegral_mono fun x => ?_
  by_cases hx : φ x ≤ max M 0
  · rw [min_eq_left hx]
    exact le_self_add
  · rw [not_le] at hx
    have hlt : ENNReal.ofReal M < ENNReal.ofReal (φ x) :=
      (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (le_max_right M 0) hx)).2
        (lt_of_le_of_lt (le_max_left M 0) hx)
    rw [Set.indicator_of_mem (show x ∈ {x | ENNReal.ofReal M < ENNReal.ofReal (φ x)} from hlt)]
    exact le_add_self

/-- **Weak convergence plus uniformly integrable tails.**  For probability
measures `μ n → ν` weakly and continuous `φ ≥ 0` with uniformly integrable
tails, `∫ φ dν < ∞` and `∫ φ dμ n → ∫ φ dν`. -/
theorem tendsto_lintegral_of_uiTails {μ : ℕ → Measure X} {ν : Measure X}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) (hν : IsProbabilityMeasure ν) (hw : WeakConv μ ν)
    (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hui : UITails μ fun x => ENNReal.ofReal (φ x)) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ∞ ∧
      Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n)) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (φ x) ∂ν)) := by
  set T : ℝ → ℝ≥0∞ := fun M =>
    ⨆ n, ∫⁻ x in {x | ENNReal.ofReal M < ENNReal.ofReal (φ x)}, ENNReal.ofReal (φ x) ∂(μ n)
  set F : ℝ → ℕ → ℝ≥0∞ := fun M n => ∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂(μ n)
  set G : ℝ → ℝ≥0∞ := fun M => ∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂ν
  have hF : ∀ M, Tendsto (F M) atTop (𝓝 (G M)) :=
    tendsto_lintegral_trunc hμ hν hw φ hφc hφ0
  -- upper bound along the sequence
  have hup : ∀ M n, ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n) ≤ F M n + T M := fun M n =>
    (lintegral_le_trunc_add_tail (μ n) φ hφc M).trans
      (add_le_add le_rfl (le_iSup (fun n =>
        ∫⁻ x in {x | ENNReal.ofReal M < ENNReal.ofReal (φ x)}, ENNReal.ofReal (φ x) ∂(μ n)) n))
  have hlow : ∀ M n, F M n ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n) := fun M n =>
    lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  -- monotone convergence for the limit measure, along natural truncation levels
  have hsup : ∫⁻ x, ENNReal.ofReal (φ x) ∂ν = ⨆ k : ℕ, G k := by
    simp only [G]
    rw [← lintegral_iSup (fun k => (hφc.measurable.min measurable_const).ennreal_ofReal)]
    · congr 1
      ext x
      refine le_antisymm ?_ (iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      obtain ⟨k, hk⟩ := exists_nat_ge (φ x)
      refine le_trans ?_ (le_iSup _ k)
      rw [min_eq_left (le_trans hk (le_max_left _ _))]
    · intro i j hij x
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (max_le_max_right _ (by exact_mod_cast hij)))
  have hlim_inf : ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n)) atTop := by
    rw [hsup]
    refine iSup_le fun k => ?_
    rw [← (hF k).liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun n => hlow k n)
  have hlim_sup : limsup (fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n)) atTop ≤
      ∫⁻ x, ENNReal.ofReal (φ x) ∂ν := by
    have hM : ∀ M, limsup (fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n)) atTop ≤
        ∫⁻ x, ENNReal.ofReal (φ x) ∂ν + T M := by
      intro M
      calc limsup (fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n)) atTop
          ≤ limsup (fun n => F M n + T M) atTop :=
            limsup_le_limsup (Eventually.of_forall fun n => hup M n)
        _ = G M + T M := ((hF M).add tendsto_const_nhds).limsup_eq
        _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂ν + T M :=
            add_le_add (lintegral_mono fun x =>
              ENNReal.ofReal_le_ofReal (min_le_left _ _)) le_rfl
    have hT : Tendsto (fun M => ∫⁻ x, ENNReal.ofReal (φ x) ∂ν + T M) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (φ x) ∂ν + 0)) :=
      tendsto_const_nhds.add hui
    rw [add_zero] at hT
    exact ge_of_tendsto hT (Eventually.of_forall hM)
  -- finiteness of the limit integral
  have hfin : ∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ∞ := by
    obtain ⟨M0, hM0⟩ := ((hui.eventually (gt_mem_nhds zero_lt_one)).and
      (eventually_ge_atTop 0)).exists
    have hbd : ∀ n, ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n) ≤ ENNReal.ofReal M0 + 1 := by
      intro n
      have := hμ n
      refine (hup M0 n).trans (add_le_add ?_ hM0.1.le)
      calc F M0 n ≤ ∫⁻ _, ENNReal.ofReal M0 ∂(μ n) :=
            lintegral_mono fun x => ENNReal.ofReal_le_ofReal
              ((min_le_right _ _).trans (le_of_eq (max_eq_left hM0.2)))
        _ = ENNReal.ofReal M0 := by simp
    calc ∫⁻ x, ENNReal.ofReal (φ x) ∂ν
        ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n)) atTop := hlim_inf
      _ ≤ ENNReal.ofReal M0 + 1 := liminf_le_of_frequently_le' (Frequently.of_forall hbd)
      _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.one_lt_top⟩
  exact ⟨hfin, tendsto_of_le_liminf_of_limsup_le hlim_inf hlim_sup⟩

lemma ofReal_max_zero (r : ℝ) : ENNReal.ofReal (max r 0) = ENNReal.ofReal r := by
  simp [ENNReal.ofReal_max]

/-- Uniformly integrable tails give a uniform bound on the integrals. -/
lemma exists_bound_of_uiTails {μ : ℕ → Measure X} (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (φ : X → ℝ) (hφc : Continuous φ) (hui : UITails μ fun x => ENNReal.ofReal (φ x)) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ n, ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n) ≤ C := by
  obtain ⟨M0, hM0⟩ := ((hui.eventually (gt_mem_nhds zero_lt_one)).and
    (eventually_ge_atTop 0)).exists
  refine ⟨ENNReal.ofReal M0 + 1, ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    ENNReal.one_lt_top⟩, fun n => ?_⟩
  have := hμ n
  refine (lintegral_le_trunc_add_tail (μ n) φ hφc M0).trans (add_le_add ?_ ?_)
  · calc ∫⁻ x, ENNReal.ofReal (min (φ x) (max M0 0)) ∂(μ n)
        ≤ ∫⁻ _, ENNReal.ofReal M0 ∂(μ n) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal
            ((min_le_right _ _).trans (le_of_eq (max_eq_left hM0.2)))
      _ = ENNReal.ofReal M0 := by simp
  · exact (le_iSup (fun n => ∫⁻ x in {x | ENNReal.ofReal M0 < ENNReal.ofReal (φ x)},
      ENNReal.ofReal (φ x) ∂(μ n)) n).trans hM0.1.le

/-- Uniformly integrable tails pass to smaller functions. -/
lemma uiTails_mono {μ : ℕ → Measure X} {φ ψ : X → ℝ} (hψφ : ∀ x, ψ x ≤ φ x)
    (hui : UITails μ fun x => ENNReal.ofReal (φ x)) :
    UITails μ fun x => ENNReal.ofReal (ψ x) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hui
    (fun _ => zero_le) (fun M => iSup_mono fun n => ?_)
  calc ∫⁻ x in {x | ENNReal.ofReal M < ENNReal.ofReal (ψ x)}, ENNReal.ofReal (ψ x) ∂(μ n)
      ≤ ∫⁻ x in {x | ENNReal.ofReal M < ENNReal.ofReal (ψ x)}, ENNReal.ofReal (φ x) ∂(μ n) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hψφ x)
    _ ≤ ∫⁻ x in {x | ENNReal.ofReal M < ENNReal.ofReal (φ x)}, ENNReal.ofReal (φ x) ∂(μ n) :=
        lintegral_mono_set fun x hx =>
          lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (hψφ x))

lemma integrable_of_lintegral_lt_top {ρ : Measure X} {φ : X → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hfin : ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ < ∞) : Integrable φ ρ :=
  ⟨hφc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hφ0)).2 hfin⟩

/-- **Signed version.**  If `|h| ≤ φ` with `φ ≥ 0` continuous and uniformly
integrable along `μ n → ν`, then `∫ h dμ n → ∫ h dν`. -/
theorem tendsto_integral_of_uiTails {μ : ℕ → Measure X} {ν : Measure X}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) (hν : IsProbabilityMeasure ν) (hw : WeakConv μ ν)
    (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hui : UITails μ fun x => ENNReal.ofReal (φ x))
    (h : X → ℝ) (hhc : Continuous h) (hhφ : ∀ x, |h x| ≤ φ x) :
    Tendsto (fun n => ∫ x, h x ∂(μ n)) atTop (𝓝 (∫ x, h x ∂ν)) := by
  have hpc : Continuous fun x => max (h x) 0 := hhc.max continuous_const
  have hmc : Continuous fun x => max (-h x) 0 := hhc.neg.max continuous_const
  have hpφ : ∀ x, max (h x) 0 ≤ φ x := fun x =>
    max_le ((le_abs_self _).trans (hhφ x)) ((abs_nonneg _).trans (hhφ x))
  have hmφ : ∀ x, max (-h x) 0 ≤ φ x := fun x =>
    max_le ((neg_le_abs _).trans (hhφ x)) ((abs_nonneg _).trans (hhφ x))
  obtain ⟨hpfin, hptend⟩ := tendsto_lintegral_of_uiTails hμ hν hw _ hpc
    (fun x => le_max_right _ _) (uiTails_mono hpφ hui)
  obtain ⟨hmfin, hmtend⟩ := tendsto_lintegral_of_uiTails hμ hν hw _ hmc
    (fun x => le_max_right _ _) (uiTails_mono hmφ hui)
  obtain ⟨hφfin, -⟩ := tendsto_lintegral_of_uiTails hμ hν hw φ hφc hφ0 hui
  obtain ⟨C, hC, hCb⟩ := exists_bound_of_uiTails hμ φ hφc hui
  have hint : ∀ ρ : Measure X, ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ < ∞ → Integrable h ρ :=
    fun ρ hρ => (integrable_of_lintegral_lt_top hφc hφ0 hρ).mono' hhc.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hhφ x)
  have hsplit : ∀ ρ : Measure X, ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ < ∞ →
      ∫ x, h x ∂ρ = (∫⁻ x, ENNReal.ofReal (max (h x) 0) ∂ρ).toReal -
        (∫⁻ x, ENNReal.ofReal (max (-h x) 0) ∂ρ).toReal := by
    intro ρ hρ
    simp_rw [ofReal_max_zero]
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint ρ hρ)
  rw [hsplit ν hφfin]
  have hseq : (fun n => ∫ x, h x ∂(μ n)) = fun n =>
      (∫⁻ x, ENNReal.ofReal (max (h x) 0) ∂(μ n)).toReal -
        (∫⁻ x, ENNReal.ofReal (max (-h x) 0) ∂(μ n)).toReal :=
    funext fun n => hsplit (μ n) ((hCb n).trans_lt hC)
  rw [hseq]
  exact ((ENNReal.tendsto_toReal hpfin.ne).comp hptend).sub
    ((ENNReal.tendsto_toReal hmfin.ne).comp hmtend)

/-- The tail integral `∫_{φ > K} φ dρ`. -/
def tailInt (ρ : Measure X) (φ : X → ℝ) (K : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | ENNReal.ofReal K < ENNReal.ofReal (φ x)}, ENNReal.ofReal (φ x) ∂ρ

lemma tailInt_antitone (ρ : Measure X) (φ : X → ℝ) : Antitone (tailInt ρ φ) :=
  fun _ _ hK => lintegral_mono_set fun x hx =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hK) hx

lemma measurableSet_tail (φ : X → ℝ) (hφc : Continuous φ) (K : ℝ) :
    MeasurableSet {x | ENNReal.ofReal K < ENNReal.ofReal (φ x)} :=
  measurableSet_lt measurable_const hφc.measurable.ennreal_ofReal

/-- A single integrable `φ` has vanishing tails. -/
lemma tendsto_tailInt_zero (ρ : Measure X) (φ : X → ℝ) (hφc : Continuous φ)
    (hfin : ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ < ∞) :
    Tendsto (tailInt ρ φ) atTop (𝓝 0) := by
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := ρ) (l := atTop)
    (F := fun K x => Set.indicator {x | ENNReal.ofReal K < ENNReal.ofReal (φ x)}
      (fun x => ENNReal.ofReal (φ x)) x) (f := fun _ => 0)
    (fun x => ENNReal.ofReal (φ x))
    (Eventually.of_forall fun K => hφc.measurable.ennreal_ofReal.indicator
      (measurableSet_tail φ hφc K))
    (Eventually.of_forall fun K => ae_of_all _ fun x => Set.indicator_le_self _ _ x)
    hfin.ne (ae_of_all _ fun x => tendsto_const_nhds.congr' <|
      (eventually_ge_atTop (φ x)).mono fun K hK => by
        dsimp only
        rw [Set.indicator_of_notMem]
        exact not_lt.2 (ENNReal.ofReal_le_ofReal hK))
  simp only [lintegral_zero] at key
  refine key.congr fun K => ?_
  rw [lintegral_indicator (measurableSet_tail φ hφc K)]
  rfl

/-- The excess `∫ (φ - min(φ, M⁺)) dρ`. -/
def excessInt (ρ : Measure X) (φ : X → ℝ) (M : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (φ x - min (φ x) (max M 0)) ∂ρ

lemma tailInt_two_mul_le (ρ : Measure X) (φ : X → ℝ) (hφc : Continuous φ)
    {M : ℝ} (hM : 0 ≤ M) :
    tailInt ρ φ (2 * M) ≤ excessInt ρ φ M + excessInt ρ φ M := by
  have hmeas : Measurable fun x => ENNReal.ofReal (φ x - min (φ x) (max M 0)) :=
    (hφc.measurable.sub (hφc.measurable.min measurable_const)).ennreal_ofReal
  rw [tailInt, excessInt, ← lintegral_indicator (measurableSet_tail φ hφc _),
    ← lintegral_add_left hmeas]
  refine lintegral_mono fun x => ?_
  by_cases hx : ENNReal.ofReal (2 * M) < ENNReal.ofReal (φ x)
  · rw [Set.indicator_of_mem (show x ∈ {x | ENNReal.ofReal (2 * M) < ENNReal.ofReal (φ x)}
      from hx)]
    have hφ : 2 * M < φ x := (ENNReal.ofReal_lt_ofReal_iff'.1 hx).1
    have hmin : min (φ x) (max M 0) = M := by
      rw [max_eq_left hM]
      exact min_eq_right (by linarith)
    rw [hmin, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [Set.indicator_of_notMem (show x ∉ {x | ENNReal.ofReal (2 * M) < ENNReal.ofReal (φ x)}
      from hx)]
    exact zero_le

lemma excessInt_eq (ρ : Measure X) (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hfin : ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ < ∞) (M : ℝ) :
    excessInt ρ φ M = ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ -
      ∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂ρ := by
  have hle : ∀ x, ENNReal.ofReal (min (φ x) (max M 0)) ≤ ENNReal.ofReal (φ x) :=
    fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  rw [excessInt, ← lintegral_sub (hφc.measurable.min measurable_const).ennreal_ofReal
    ((lintegral_mono hle).trans_lt hfin).ne (ae_of_all _ hle)]
  congr 1
  ext x
  exact ENNReal.ofReal_sub _ (le_min (hφ0 x) (le_max_right _ _))

lemma tendsto_excessInt_zero (ρ : Measure X) (φ : X → ℝ) (hφc : Continuous φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hfin : ∫⁻ x, ENNReal.ofReal (φ x) ∂ρ < ∞) :
    Tendsto (excessInt ρ φ) atTop (𝓝 0) := by
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := ρ) (l := atTop)
    (F := fun M x => ENNReal.ofReal (φ x - min (φ x) (max M 0))) (f := fun _ => 0)
    (fun x => ENNReal.ofReal (φ x))
    (Eventually.of_forall fun M =>
      (hφc.measurable.sub (hφc.measurable.min measurable_const)).ennreal_ofReal)
    (Eventually.of_forall fun M => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (by
      linarith [le_min (hφ0 x) (le_max_right M 0)]))
    hfin.ne (ae_of_all _ fun x => tendsto_const_nhds.congr' <|
      (eventually_ge_atTop (φ x)).mono fun M hM => by
        dsimp only
        rw [min_eq_left (hM.trans (le_max_left _ _)), sub_self, ENNReal.ofReal_zero])
  simp only [lintegral_zero] at key
  exact key

/-- **Converse.**  If `∫ φ dμ n → ∫ φ dν < ∞` along weakly convergent
probability measures, then `φ` has uniformly integrable tails. -/
theorem uiTails_of_tendsto_lintegral {μ : ℕ → Measure X} {ν : Measure X}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) (hν : IsProbabilityMeasure ν) (hw : WeakConv μ ν)
    (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hfin : ∀ n, ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n) < ∞)
    (hνfin : ∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ∞)
    (htend : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (φ x) ∂ν))) :
    UITails μ fun x => ENNReal.ofReal (φ x) := by
  show Tendsto (fun K => ⨆ n, tailInt (μ n) φ K) atTop (𝓝 0)
  -- the excess converges along the sequence
  have hex : ∀ M, Tendsto (fun n => excessInt (μ n) φ M) atTop (𝓝 (excessInt ν φ M)) := by
    intro M
    have e : (fun n => excessInt (μ n) φ M) = fun n => ∫⁻ x, ENNReal.ofReal (φ x) ∂(μ n) -
        ∫⁻ x, ENNReal.ofReal (min (φ x) (max M 0)) ∂(μ n) :=
      funext fun n => excessInt_eq (μ n) φ hφc hφ0 (hfin n) M
    rw [e, excessInt_eq ν φ hφc hφ0 hνfin M]
    exact ENNReal.Tendsto.sub htend (tendsto_lintegral_trunc hμ hν hw φ hφc hφ0 M)
      (Or.inl hνfin.ne)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- a truncation level at which the limit excess is below `ε/2`
  obtain ⟨M1, hM1, hM1pos⟩ := (((tendsto_excessInt_zero ν φ hφc hφ0 hνfin).eventually
    (gt_mem_nhds hε2)).and (eventually_ge_atTop 0)).exists
  -- beyond some index, the excess along the sequence is below `ε/2`
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hex M1).eventually (gt_mem_nhds hM1))
  have hlarge : ∀ n, N ≤ n → tailInt (μ n) φ (2 * M1) ≤ ε := fun n hn =>
    (tailInt_two_mul_le (μ n) φ hφc hM1pos).trans
      ((ENNReal.add_lt_add (hN n hn) (hN n hn)).le.trans (ENNReal.add_halves ε).le)
  -- the finitely many earlier indices
  have hsmall : ∀ᶠ K in atTop, ∀ n ∈ Finset.range N, tailInt (μ n) φ K ≤ ε :=
    (Finset.range N).eventually_all.2 fun n _ =>
      (tendsto_tailInt_zero (μ n) φ hφc (hfin n)).eventually (ge_mem_nhds hε)
  filter_upwards [hsmall, eventually_ge_atTop (2 * M1)] with K hK hK2
  refine iSup_le fun n => ?_
  by_cases hn : n < N
  · exact hK n (Finset.mem_range.2 hn)
  · exact (tailInt_antitone (μ n) φ hK2).trans (hlarge n (not_lt.1 hn))

end General

end NumeraireStability
