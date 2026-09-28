/-
# The continuous-mapping step of Theorem 5.1

If `Q_n → Q` weakly and `a_n → a`, then the laws of `(A_{a_n}, B_{a_n})` under
`Q_n` converge weakly to the law of `(A_a, B_a)` under `Q` (paper, proof of
Theorem 5.1(i)): the product laws `δ_{a_n} ⊗ Q_n` converge to `δ_a ⊗ Q`, and
pushing forward by the jointly continuous map `(a, ω) ↦ (A_a(ω), B_a(ω))` is
continuous.  Along any sequence in `K × 𝔸` converging to a point of `K × 𝔸`,
the class hypotheses then give the standing hypotheses (S1)–(S2) of §3.
-/
import NumeraireStability.Defs56
import NumeraireStability.Corollary
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

noncomputable section

namespace NumeraireStability

section Pushforward

variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {𝔸 : Type*} [MetricSpace 𝔸] [CompactSpace 𝔸]
  {F : 𝔸 → Ω → ℝ × ℝ}

lemma continuous_section (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2) (a : 𝔸) :
    Continuous (F a) :=
  hF.comp (continuous_const.prodMk continuous_id)

lemma measurable_section (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2) (a : 𝔸) :
    Measurable (F a) :=
  (continuous_section hF a).measurable

/-- `(Q, a) ↦` the law of `(A_a, B_a)` under `Q`, as a probability measure. -/
def lawMap (F : 𝔸 → Ω → ℝ × ℝ) (x : ProbabilityMeasure Ω × 𝔸) :
    ProbabilityMeasure (ℝ × ℝ) :=
  x.1.map (F x.2)

lemma lawMap_toMeasure (F : 𝔸 → Ω → ℝ × ℝ) (x : ProbabilityMeasure Ω × 𝔸) :
    (lawMap F x : Measure (ℝ × ℝ)) = contractLaw F (x.1 : Measure Ω) x.2 := by
  simp [lawMap, contractLaw, ProbabilityMeasure.toMeasure_map]

/-- The continuous-mapping step: `(Q, a) ↦ law of (A_a, B_a) under Q` is
continuous for the weak topologies. -/
theorem continuous_lawMap (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2) :
    Continuous (lawMap F) := by
  let _i : MeasurableSpace 𝔸 := borel 𝔸
  have _j : BorelSpace 𝔸 := ⟨rfl⟩
  have hprod : Continuous fun x : ProbabilityMeasure Ω × 𝔸 => (diracProba x.2).prod x.1 :=
    ProbabilityMeasure.continuous_prod.comp
      ((continuous_diracProba.comp continuous_snd).prodMk continuous_fst)
  have hmap := ProbabilityMeasure.continuous_map (Ω := 𝔸 × Ω) (Ω' := ℝ × ℝ) hF
  refine (hmap.comp hprod).congr fun x => ?_
  apply Subtype.ext
  change ((Measure.dirac x.2).prod (x.1 : Measure Ω)).map (fun y : 𝔸 × Ω => F y.1 y.2) =
    (x.1 : Measure Ω).map (F x.2)
  rw [Measure.dirac_prod, Measure.map_map hF.measurable measurable_prodMk_left]
  rfl

/-- Along `(Q_n, a_n) → (Q, a)`, the laws of `(A_{a_n}, B_{a_n})` converge weakly. -/
lemma weakConv_contractLaw (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2)
    {y : ℕ → ProbabilityMeasure Ω × 𝔸} {x : ProbabilityMeasure Ω × 𝔸}
    (hy : Tendsto y atTop (𝓝 x)) :
    WeakConv (fun n => contractLaw F ((y n).1 : Measure Ω) (y n).2)
      (contractLaw F (x.1 : Measure Ω) x.2) := by
  intro f
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (((continuous_lawMap hF).tendsto x).comp hy)) f
  simpa [Function.comp_def, lawMap_toMeasure] using h

lemma isProbabilityMeasure_contractLaw (F : 𝔸 → Ω → ℝ × ℝ)
    (Q : ProbabilityMeasure Ω) (a : 𝔸) :
    IsProbabilityMeasure (contractLaw F (Q : Measure Ω) a) := by
  unfold contractLaw
  infer_instance

lemma contractLaw_apply (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2) (Q : Measure Ω) (a : 𝔸)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    contractLaw F Q a S = Q (F a ⁻¹' S) :=
  Measure.map_apply (measurable_section hF a) hS

lemma contractLaw_nonpos_null (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2)
    (hpos : ∀ a ω, 0 < (F a ω).1) (Q : Measure Ω) (a : 𝔸) :
    contractLaw F Q a {p | p.1 ≤ 0} = 0 := by
  rw [contractLaw_apply hF Q a (measurableSet_le measurable_fst measurable_const)]
  have : F a ⁻¹' {p : ℝ × ℝ | p.1 ≤ 0} = ∅ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hpos a ω
  rw [this, measure_empty]

lemma contractLaw_neg_null (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2)
    (hpos : ∀ a ω, 0 < (F a ω).1) (Q : Measure Ω) (a : 𝔸) :
    contractLaw F Q a {p | p.1 < 0} = 0 :=
  measure_mono_null (fun p (hp : p.1 < 0) => show p.1 ≤ 0 from hp.le)
    (contractLaw_nonpos_null hF hpos Q a)

lemma contractLaw_zero_null (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2)
    (hpos : ∀ a ω, 0 < (F a ω).1) (Q : Measure Ω) (a : 𝔸) :
    contractLaw F Q a {p | p.1 = 0} = 0 :=
  measure_mono_null (fun p (hp : p.1 = 0) => show p.1 ≤ 0 from hp.le)
    (contractLaw_nonpos_null hF hpos Q a)

variable {K : Set (ProbabilityMeasure Ω)}

/-- A quantity bounded, index by index, by a supremum over `K × 𝔸`. -/
lemma iSup_seq_le_iSup_class (G : Measure (ℝ × ℝ) → ℝ≥0∞)
    {y : ℕ → ProbabilityMeasure Ω × 𝔸} (hy : ∀ n, (y n).1 ∈ K) :
    (⨆ n, G (contractLaw F ((y n).1 : Measure Ω) (y n).2)) ≤
      ⨆ z : K × 𝔸, G (contractLaw F ((z.1 : ProbabilityMeasure Ω) : Measure Ω) z.2) :=
  iSup_le fun n => le_iSup_of_le (⟨⟨(y n).1, hy n⟩, (y n).2⟩ : K × 𝔸) le_rfl

/-- Uniform integrability over `K × 𝔸` passes to any sequence in `K × 𝔸`. -/
lemma unifIntegrable_seq_of_class (g : ℝ × ℝ → ℝ≥0∞)
    (hui : UnifIntegrableOn (fun z : K × 𝔸 => contractLaw F (z.1 : Measure Ω) z.2) g)
    {y : ℕ → ProbabilityMeasure Ω × 𝔸} (hy : ∀ n, (y n).1 ∈ K) :
    UnifIntegrableFamily (fun n => contractLaw F ((y n).1 : Measure Ω) (y n).2) g :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hui (fun _ => zero_le)
    fun M => iSup_seq_le_iSup_class
      (fun P => ∫⁻ p in {p | ENNReal.ofReal M < g p}, g p ∂P) hy

/-- The uniform ratio-tail condition over `K × 𝔸` passes to any sequence in `K × 𝔸`. -/
lemma ratioTail_seq_of_class {s : ℝ}
    (htail : Tendsto (ratioTailOn s fun z : K × 𝔸 => contractLaw F (z.1 : Measure Ω) z.2)
      atTop (𝓝 0))
    {y : ℕ → ProbabilityMeasure Ω × 𝔸} (hy : ∀ n, (y n).1 ∈ K) :
    Tendsto (ratioTail s fun n => contractLaw F ((y n).1 : Measure Ω) (y n).2) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail (fun _ => zero_le)
    fun R => iSup_seq_le_iSup_class
      (fun P => ∫⁻ p in {p | R * p.1 < |p.2|}, boundaryFamily s p ∂P) hy

/-- Along a sequence in `K × 𝔸` converging to a point of `K × 𝔸`, the laws of
`(A_a, B_a)` satisfy the standing hypotheses (S1)–(S2) of §3. -/
theorem standing_of_seq (hF : Continuous fun x : 𝔸 × Ω => F x.1 x.2)
    (hpos : ∀ a ω, 0 < (F a ω).1)
    (hui : UnifIntegrableOn (fun z : K × 𝔸 => contractLaw F (z.1 : Measure Ω) z.2)
      fun p => ENNReal.ofReal p.1)
    (hmean : ∃ c : ℝ, 0 < c ∧
      ∀ z : K × 𝔸, c ≤ numeraireMean (contractLaw F (z.1 : Measure Ω) z.2))
    {y : ℕ → ProbabilityMeasure Ω × 𝔸} {x : ProbabilityMeasure Ω × 𝔸}
    (hy : ∀ n, (y n).1 ∈ K) (hx : x.1 ∈ K) (hlim : Tendsto y atTop (𝓝 x)) :
    StandingSetting (fun n => contractLaw F ((y n).1 : Measure Ω) (y n).2)
      (contractLaw F (x.1 : Measure Ω) x.2) where
  prob n := isProbabilityMeasure_contractLaw F (y n).1 (y n).2
  prob_lim := isProbabilityMeasure_contractLaw F x.1 x.2
  pos n := contractLaw_nonpos_null hF hpos _ _
  lim_supp := contractLaw_neg_null hF hpos _ _
  weak := weakConv_contractLaw hF hlim
  ui := unifIntegrable_seq_of_class _ hui hy
  mean_pos := by
    obtain ⟨c, hc, hcle⟩ := hmean
    exact hc.trans_le (hcle ⟨⟨x.1, hx⟩, x.2⟩)

/-- Every point of `K × 𝔸` has positive numéraire mean. -/
lemma mean_pos_of_class
    (hmean : ∃ c : ℝ, 0 < c ∧
      ∀ z : K × 𝔸, c ≤ numeraireMean (contractLaw F (z.1 : Measure Ω) z.2))
    {Q : ProbabilityMeasure Ω} (hQ : Q ∈ K) (a : 𝔸) :
    0 < numeraireMean (contractLaw F (Q : Measure Ω) a) := by
  obtain ⟨c, hc, hcle⟩ := hmean
  exact hc.trans_le (hcle ⟨⟨Q, hQ⟩, a⟩)

/-! ### From neighbourhoods within `K × 𝔸` to sequences -/

instance : FirstCountableTopology (ProbabilityMeasure Ω × 𝔸) := inferInstance

lemma nhdsWithin_isCountablyGenerated (S : Set (ProbabilityMeasure Ω × 𝔸))
    (x : ProbabilityMeasure Ω × 𝔸) : (𝓝[S] x).IsCountablyGenerated := by
  rw [nhdsWithin]
  infer_instance

/-- A sequence tending to `x ∈ S` within `S` agrees eventually with a sequence
lying entirely in `S` and tending to `x`. -/
lemma exists_seq_mem_of_tendsto_nhdsWithin {S : Set (ProbabilityMeasure Ω × 𝔸)}
    {x : ProbabilityMeasure Ω × 𝔸} (hx : x ∈ S) {u : ℕ → ProbabilityMeasure Ω × 𝔸}
    (hu : Tendsto u atTop (𝓝[S] x)) :
    ∃ v : ℕ → ProbabilityMeasure Ω × 𝔸, (∀ n, v n ∈ S) ∧ Tendsto v atTop (𝓝 x) ∧
      ∀ᶠ n in atTop, u n = v n := by
  classical
  obtain ⟨hu1, hu2⟩ := tendsto_nhdsWithin_iff.1 hu
  refine ⟨fun n => if u n ∈ S then u n else x, fun n => ?_, ?_, ?_⟩
  · by_cases h : u n ∈ S
    · simp [h]
    · simp [h, hx]
  · refine hu1.congr' (hu2.mono fun n hn => ?_)
    simp [hn]
  · exact hu2.mono fun n hn => by simp [hn]

end Pushforward

end NumeraireStability
