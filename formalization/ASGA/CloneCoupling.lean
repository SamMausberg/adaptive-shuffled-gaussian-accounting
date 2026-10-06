import ASGA.Basic

/-!
# Measure-theoretic steps of the null-clone reduction

This file proves the steps in the proof of `lem:clone` that do not involve Gaussian integrals.

* Transfer of a hockey-stick inequality through total variation errors on both arguments, with
  cost `(1 + e^ε) β`, which is `(1 + k) β_p` at `ε = log k`.
* The kernel modification: with `η = ∫ (p g₀ - g)_+`, `r = (g - p g₀)_+ / (1 - p + η)` and
  `g̃ = p g₀ + (1 - p) r`, the residual `r` and `g̃` are probability densities, `TV(g, g̃) = η`,
  and the law with density `g̃` is the mixture `p · g₀ + (1 - p) · r` realized by a coin.
* The hybrid argument for adaptive processes: if each step kernel, which may depend on the whole
  history, moves by at most `η_t` in total variation uniformly over histories, the law of the
  history moves by at most `∑ η_t`. Histories use Mathlib's `Kernel.partialTraj`.
* Joint convexity of total variation and of the hockey-stick divergence over mixtures, and
  data processing under Markov kernels and measurable maps.
* The likelihood-ratio form `H_ε(P,Q) = E_Q (L - e^ε)_+` and `H_ε(Q,P) = E_Q (1 - e^ε L)_+`
  for `P ≪ Q` with `L = dP/dQ`.
-/

open MeasureTheory ProbabilityTheory

namespace ASGA

variable {Ω : Type*} [MeasurableSpace Ω]

section Tests

variable {P Q : Measure Ω}

/-- Randomized-test form of a set inequality: if `P(A) - c Q(A) ≤ d` for every measurable `A`,
then `∫ φ dP - c ∫ φ dQ ≤ d` for every `[0,1]`-valued measurable `φ`. -/
private lemma integral_sub_le_of_forall_set [IsFiniteMeasure P] [IsFiniteMeasure Q] {c d : ℝ}
    (hc : 0 ≤ c) (h : ∀ A, MeasurableSet A → (P A).toReal - c * (Q A).toReal ≤ d)
    {φ : Ω → ℝ} (hφ : IsTest φ) :
    ∫ x, φ x ∂P - c * ∫ x, φ x ∂Q ≤ d := by
  have hd : 0 ≤ d := by simpa using h ∅ MeasurableSet.empty
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => (hφ.2 x).1
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => (hφ.2 x).2
  -- pointwise bound on the level sets
  have hlev : ∀ t : ℝ, P {x | t < φ x} ≤
      ENNReal.ofReal c * Q {x | t < φ x} + (Set.Iio (1 : ℝ)).indicator
        (fun _ => ENNReal.ofReal d) t := by
    intro t
    by_cases ht : t < 1
    · have hA : MeasurableSet {x | t < φ x} := measurableSet_lt measurable_const hφ.1
      have h1 := h _ hA
      rw [Set.indicator_of_mem (by exact ht)]
      rw [← ENNReal.ofReal_toReal (measure_ne_top P {x | t < φ x}),
        ← ENNReal.ofReal_toReal (measure_ne_top Q {x | t < φ x}),
        ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) hd]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · have : {x | t < φ x} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (hφ1 x).trans (not_lt.1 ht)
      simp [this]
  have hP := lintegral_eq_lintegral_meas_lt P (Filter.Eventually.of_forall hφ0)
    hφ.1.aemeasurable
  have hQ := lintegral_eq_lintegral_meas_lt Q (Filter.Eventually.of_forall hφ0)
    hφ.1.aemeasurable
  have hvol : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iio 1) = 1 := by
    rw [Measure.restrict_apply measurableSet_Iio, Set.Iio_inter_Ioi, Real.volume_Ioo]
    simp
  have hmain : ∫⁻ x, ENNReal.ofReal (φ x) ∂P ≤
      ENNReal.ofReal c * (∫⁻ x, ENNReal.ofReal (φ x) ∂Q) + ENNReal.ofReal d := by
    rw [hP, hQ]
    calc ∫⁻ t in Set.Ioi 0, P {x | t < φ x}
        ≤ ∫⁻ t in Set.Ioi 0, (ENNReal.ofReal c * Q {x | t < φ x} +
            (Set.Iio (1 : ℝ)).indicator (fun _ => ENNReal.ofReal d) t) :=
          lintegral_mono fun t => hlev t
      _ = ENNReal.ofReal c * (∫⁻ t in Set.Ioi 0, Q {x | t < φ x}) + ENNReal.ofReal d := by
          rw [lintegral_add_right' _ ((measurable_const.indicator measurableSet_Iio).aemeasurable),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_indicator_const measurableSet_Iio, hvol, mul_one]
  have hfinQ : ∫⁻ x, ENNReal.ofReal (φ x) ∂Q ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top Q Set.univ) ?_
    calc ∫⁻ x, ENNReal.ofReal (φ x) ∂Q ≤ ∫⁻ _, 1 ∂Q :=
          lintegral_mono fun x => by simpa using hφ1 x
      _ = Q Set.univ := by simp
  have hIP : ∫ x, φ x ∂P = (∫⁻ x, ENNReal.ofReal (φ x) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφ.1.aestronglyMeasurable
  have hIQ : ∫ x, φ x ∂Q = (∫⁻ x, ENNReal.ofReal (φ x) ∂Q).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφ.1.aestronglyMeasurable
  have := ENNReal.toReal_mono (by finiteness) hmain
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd] at this
  rw [hIP, hIQ]
  linarith

/-- Randomized tests are integrable against finite measures. -/
private lemma IsTest.integrable {φ : Ω → ℝ} (hφ : IsTest φ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable φ μ :=
  Integrable.of_bound hφ.1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hφ.2 x).1, (hφ.2 x).2])

/-- A hockey-stick bound holds for randomized tests. -/
private lemma integral_sub_le_hockeyStick [IsFiniteMeasure P] [IsFiniteMeasure Q] (ε : ℝ)
    {φ : Ω → ℝ} (hφ : IsTest φ) :
    ∫ x, φ x ∂P - Real.exp ε * ∫ x, φ x ∂Q ≤ hockeyStick P Q ε :=
  integral_sub_le_of_forall_set (Real.exp_pos ε).le (fun _ hA => le_hockeyStick ε hA) hφ

/-- A total variation bound holds for randomized tests. -/
private lemma abs_integral_sub_le_tvDist [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {φ : Ω → ℝ} (hφ : IsTest φ) :
    |∫ x, φ x ∂P - ∫ x, φ x ∂Q| ≤ tvDist P Q := by
  rw [abs_sub_le_iff]
  constructor
  · have := integral_sub_le_of_forall_set (P := P) (Q := Q) zero_le_one
      (fun A hA => (le_abs_self _).trans (by simpa using le_tvDist (P := P) (Q := Q) hA)) hφ
    simpa using this
  · have := integral_sub_le_of_forall_set (P := Q) (Q := P) zero_le_one
      (fun A hA => (le_abs_self _).trans (by
        simpa [abs_sub_comm] using le_tvDist (P := P) (Q := Q) hA)) hφ
    simpa using this

/-- Evaluation of a Markov kernel on a fixed measurable set is a randomized test. -/
private lemma isTest_kernel {β : Type*} [MeasurableSpace β] (κ : Kernel Ω β) [IsMarkovKernel κ]
    {A : Set β} (hA : MeasurableSet A) : IsTest fun x => (κ x A).toReal :=
  ⟨(κ.measurable_coe hA).ennreal_toReal, fun x =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp [prob_le_one])⟩⟩

/-- Real-valued form of `Measure.bind_apply` for Markov kernels. -/
private lemma toReal_comp_apply {β : Type*} [MeasurableSpace β] (κ : Kernel Ω β)
    [IsMarkovKernel κ] (μ : Measure Ω) {A : Set β} (hA : MeasurableSet A) :
    ((κ ∘ₘ μ) A).toReal = ∫ x, (κ x A).toReal ∂μ := by
  rw [Measure.bind_apply hA κ.aemeasurable,
    integral_toReal (κ.measurable_coe hA).aemeasurable
      (Filter.Eventually.of_forall fun x => measure_lt_top (κ x) A)]

end Tests

/-! ### Transfer of a hockey-stick inequality through total variation errors -/

section Transfer

variable {P P' Q Q' : Measure Ω}

/-- Transfer with separate budgets: `H_ε(P,Q) ≤ H_ε(P',Q') + β₁ + e^ε β₂` when
`TV(P,P') ≤ β₁` and `TV(Q,Q') ≤ β₂`. -/
theorem hockeyStick_le_hockeyStick_add [IsFiniteMeasure P] [IsFiniteMeasure P']
    [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (ε : ℝ) {β₁ β₂ : ℝ}
    (hP : tvDist P P' ≤ β₁) (hQ : tvDist Q Q' ≤ β₂) :
    hockeyStick P Q ε ≤ hockeyStick P' Q' ε + β₁ + Real.exp ε * β₂ := by
  refine hockeyStick_le fun A hA => ?_
  have h1 := (le_abs_self _).trans ((le_tvDist (P := P) (Q := P') hA).trans hP)
  have h2 := (neg_le_abs _).trans ((le_tvDist (P := Q) (Q := Q') hA).trans hQ)
  have h3 := le_hockeyStick (P := P') (Q := Q') ε hA
  have h4 : Real.exp ε * ((Q' A).toReal - (Q A).toReal) ≤ Real.exp ε * β₂ :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos ε).le
  nlinarith

/-- Transfer of a hockey-stick inequality through two total variation errors, as in the proof
of `lem:clone`: the cost is `(1 + e^ε) β`. -/
theorem hockeyStick_le_hockeyStick_add_tv [IsFiniteMeasure P] [IsFiniteMeasure P']
    [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (ε : ℝ) {β : ℝ}
    (hP : tvDist P P' ≤ β) (hQ : tvDist Q Q' ≤ β) :
    hockeyStick P Q ε ≤ hockeyStick P' Q' ε + (1 + Real.exp ε) * β := by
  have := hockeyStick_le_hockeyStick_add ε hP hQ
  linarith

/-- The transfer at threshold `ε = log k`, with cost `(1 + k) β` (proof of `lem:clone`). -/
theorem hockeyStick_log_le_hockeyStick_add_tv [IsFiniteMeasure P] [IsFiniteMeasure P']
    [IsFiniteMeasure Q] [IsFiniteMeasure Q'] {k β : ℝ} (hk : 0 < k)
    (hP : tvDist P P' ≤ β) (hQ : tvDist Q Q' ≤ β) :
    hockeyStick P Q (Real.log k) ≤ hockeyStick P' Q' (Real.log k) + (1 + k) * β := by
  simpa [Real.exp_log hk] using hockeyStick_le_hockeyStick_add_tv (Real.log k) hP hQ

end Transfer

/-! ### Data processing -/

section DataProcessing

variable {β : Type*} [MeasurableSpace β]

/-- Data processing for the hockey-stick divergence under a Markov kernel. -/
theorem hockeyStick_comp_le (κ : Kernel Ω β) [IsMarkovKernel κ] (P Q : Measure Ω)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (ε : ℝ) :
    hockeyStick (κ ∘ₘ P) (κ ∘ₘ Q) ε ≤ hockeyStick P Q ε := by
  refine hockeyStick_le fun A hA => ?_
  rw [toReal_comp_apply κ P hA, toReal_comp_apply κ Q hA]
  exact integral_sub_le_hockeyStick ε (isTest_kernel κ hA)

/-- Data processing for the hockey-stick divergence under a measurable map. -/
theorem hockeyStick_map_le {f : Ω → β} (hf : Measurable f) (P Q : Measure Ω)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (ε : ℝ) :
    hockeyStick (P.map f) (Q.map f) ε ≤ hockeyStick P Q ε := by
  rw [← Measure.deterministic_comp_eq_map hf, ← Measure.deterministic_comp_eq_map hf]
  exact hockeyStick_comp_le _ P Q ε

/-- Data processing for total variation under a measurable map. -/
theorem tvDist_map_le {f : Ω → β} (hf : Measurable f) (P Q : Measure Ω)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    tvDist (P.map f) (Q.map f) ≤ tvDist P Q := by
  refine tvDist_le fun A hA => ?_
  rw [Measure.map_apply hf hA, Measure.map_apply hf hA]
  exact le_tvDist (hf hA)

/-- Data processing for total variation under a Markov kernel. -/
theorem tvDist_comp_le (κ : Kernel Ω β) [IsMarkovKernel κ] (P Q : Measure Ω)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    tvDist (κ ∘ₘ P) (κ ∘ₘ Q) ≤ tvDist P Q := by
  refine tvDist_le fun A hA => ?_
  rw [toReal_comp_apply κ P hA, toReal_comp_apply κ Q hA]
  exact abs_integral_sub_le_tvDist (isTest_kernel κ hA)

end DataProcessing

/-! ### Mixtures and averaging over a revealed variable -/

section Mixture

variable {ι : Type*}

/-- Evaluation of a finite mixture with nonnegative real weights. -/
private lemma toReal_sum_smul_apply (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (P : ι → Measure Ω) [∀ i, IsFiniteMeasure (P i)] (A : Set Ω) :
    ((∑ i ∈ s, ENNReal.ofReal (w i) • P i) A).toReal = ∑ i ∈ s, w i * (P i A).toReal := by
  rw [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i hi)]
  · intro i _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- Joint convexity of total variation over a finite mixture. -/
theorem tvDist_sum_smul_le (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (P Q : ι → Measure Ω) [∀ i, IsFiniteMeasure (P i)] [∀ i, IsFiniteMeasure (Q i)] :
    tvDist (∑ i ∈ s, ENNReal.ofReal (w i) • P i) (∑ i ∈ s, ENNReal.ofReal (w i) • Q i) ≤
      ∑ i ∈ s, w i * tvDist (P i) (Q i) := by
  refine tvDist_le fun A hA => ?_
  rw [toReal_sum_smul_apply s w hw P A, toReal_sum_smul_apply s w hw Q A,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
  exact mul_le_mul_of_nonneg_left (le_tvDist hA) (hw i hi)

/-- Joint convexity of the hockey-stick divergence over a finite mixture: averaging over a
revealed variable with finitely many values. -/
theorem hockeyStick_sum_smul_le (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (P Q : ι → Measure Ω) [∀ i, IsFiniteMeasure (P i)] [∀ i, IsFiniteMeasure (Q i)] (ε : ℝ) :
    hockeyStick (∑ i ∈ s, ENNReal.ofReal (w i) • P i) (∑ i ∈ s, ENNReal.ofReal (w i) • Q i) ε ≤
      ∑ i ∈ s, w i * hockeyStick (P i) (Q i) ε := by
  refine hockeyStick_le fun A hA => ?_
  rw [toReal_sum_smul_apply s w hw P A, toReal_sum_smul_apply s w hw Q A, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have := mul_le_mul_of_nonneg_left (le_hockeyStick (P := P i) (Q := Q i) ε hA) (hw i hi)
  linarith

variable {β : Type*} [MeasurableSpace β]

/-- Averaging over a revealed variable with law `ν`: if the conditional pairs satisfy
`H_ε(κ y, κ' y) ≤ d y`, then the averaged pair satisfies `H_ε ≤ ∫ d dν`. -/
theorem hockeyStick_comp_le_integral (ν : Measure β) [IsFiniteMeasure ν]
    (κ κ' : Kernel β Ω) [IsMarkovKernel κ] [IsMarkovKernel κ'] (ε : ℝ) {d : β → ℝ}
    (hd : Integrable d ν) (h : ∀ y, hockeyStick (κ y) (κ' y) ε ≤ d y) :
    hockeyStick (κ ∘ₘ ν) (κ' ∘ₘ ν) ε ≤ ∫ y, d y ∂ν := by
  refine hockeyStick_le fun A hA => ?_
  rw [toReal_comp_apply κ ν hA, toReal_comp_apply κ' ν hA, ← integral_const_mul,
    ← integral_sub ((isTest_kernel κ hA).integrable ν)
      (((isTest_kernel κ' hA).integrable ν).const_mul _)]
  refine integral_mono (((isTest_kernel κ hA).integrable ν).sub
    (((isTest_kernel κ' hA).integrable ν).const_mul _)) hd fun y => ?_
  exact (le_hockeyStick ε hA).trans (h y)

/-- Averaging over a revealed variable for total variation. -/
theorem tvDist_comp_le_integral (ν : Measure β) [IsFiniteMeasure ν]
    (κ κ' : Kernel β Ω) [IsMarkovKernel κ] [IsMarkovKernel κ'] {d : β → ℝ}
    (hd : Integrable d ν) (h : ∀ y, tvDist (κ y) (κ' y) ≤ d y) :
    tvDist (κ ∘ₘ ν) (κ' ∘ₘ ν) ≤ ∫ y, d y ∂ν := by
  refine tvDist_le fun A hA => ?_
  have hi := (isTest_kernel κ hA).integrable ν
  have hi' := (isTest_kernel κ' hA).integrable ν
  rw [toReal_comp_apply κ ν hA, toReal_comp_apply κ' ν hA, ← integral_sub hi hi']
  refine (abs_integral_le_integral_abs).trans (integral_mono (hi.sub hi').abs hd fun y => ?_)
  exact (le_tvDist hA).trans (h y)

end Mixture

/-! ### Sequential coupling of adaptive processes -/

section Sequential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- One step of the hybrid argument: changing the initial law and then the kernel costs
at most `TV(μ, μ') + η` when `TV(κ x, κ' x) ≤ η` for every input `x`. -/
theorem tvDist_comp_le_tvDist_add (μ μ' : Measure α) [IsProbabilityMeasure μ]
    [IsFiniteMeasure μ'] (κ κ' : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel κ'] {η : ℝ}
    (h : ∀ x, tvDist (κ x) (κ' x) ≤ η) :
    tvDist (κ ∘ₘ μ) (κ' ∘ₘ μ') ≤ tvDist μ μ' + η := by
  refine tvDist_le fun A hA => ?_
  have hi := (isTest_kernel κ hA).integrable μ
  have hi' := (isTest_kernel κ' hA).integrable μ
  rw [toReal_comp_apply κ μ hA, toReal_comp_apply κ' μ' hA]
  have h1 : |∫ x, (κ x A).toReal ∂μ - ∫ x, (κ' x A).toReal ∂μ| ≤ η := by
    rw [← integral_sub hi hi', ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := η)
      (Filter.Eventually.of_forall fun x => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]
    exact (le_tvDist hA).trans (h x)
  have h2 := abs_integral_sub_le_tvDist (P := μ) (Q := μ') (isTest_kernel κ' hA)
  calc |∫ x, (κ x A).toReal ∂μ - ∫ x, (κ' x A).toReal ∂μ'|
      ≤ |∫ x, (κ x A).toReal ∂μ - ∫ x, (κ' x A).toReal ∂μ| +
          |∫ x, (κ' x A).toReal ∂μ - ∫ x, (κ' x A).toReal ∂μ'| := abs_sub_le _ _ _
    _ ≤ tvDist μ μ' + η := by linarith

/-- The two-step hybrid bound for composition-products:
`TV(μ ⊗ κ, μ' ⊗ κ') ≤ TV(μ, μ') + η` when `TV(κ x, κ' x) ≤ η` for every `x`. -/
theorem tvDist_compProd_le (μ μ' : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (κ κ' : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel κ']
    {η : ℝ} (h : ∀ x, tvDist (κ x) (κ' x) ≤ η) :
    tvDist (μ ⊗ₘ κ) (μ' ⊗ₘ κ') ≤ tvDist μ μ' + η := by
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod]
  refine tvDist_comp_le_tvDist_add μ μ' _ _ fun x => ?_
  rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.dirac_prod]
  exact (tvDist_map_le measurable_prodMk_left _ _).trans (h x)

private lemma tvDist_self (μ : Measure α) : tvDist μ μ = 0 := by
  have : Nonempty {s : Set α // MeasurableSet s} := ⟨⟨∅, MeasurableSet.empty⟩⟩
  simp [tvDist]

end Sequential

/-! ### The hybrid argument along an adaptive trajectory

Histories are encoded with Mathlib's Ionescu-Tulcea kernels: `κ n` is a Markov kernel from the
history `(x₀, …, xₙ)` to the next state `xₙ₊₁`, so the step law may depend on the whole past, and
`Kernel.partialTraj κ a b` gives the law of the history up to time `b` given the history up to
time `a`. -/

section Trajectory

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {κ κ' : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))}
  [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (κ' n)]

/-- One transition of the trajectory kernel inherits the total variation bound of the step
kernel. -/
private lemma tvDist_partialTraj_succ_self_le (b : ℕ) (x : Π i : Finset.Iic b, X i) :
    tvDist (Kernel.partialTraj κ b (b + 1) x) (Kernel.partialTraj κ' b (b + 1) x) ≤
      tvDist (κ b x) (κ' b x) := by
  rw [Kernel.partialTraj_succ_self, Kernel.partialTraj_succ_self,
    Kernel.map_apply _ measurable_IicProdIoc, Kernel.map_apply _ measurable_IicProdIoc,
    Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton b).measurable,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton b).measurable,
    Measure.dirac_prod, Measure.dirac_prod]
  refine (tvDist_map_le measurable_IicProdIoc _ _).trans ?_
  refine (tvDist_map_le measurable_prodMk_left _ _).trans ?_
  exact tvDist_map_le (MeasurableEquiv.piSingleton b).measurable _ _

/-- Hybrid argument for adaptive processes. If at each step `n` with `a ≤ n < b` the two step
kernels satisfy `TV(κ n h, κ' n h) ≤ η n` for every history `h`, then the laws of the histories
up to time `b`, started from `μ` and `μ'` at time `a`, satisfy
`TV ≤ TV(μ, μ') + ∑_{a ≤ n < b} η n`. -/
theorem tvDist_partialTraj_comp_le (a b : ℕ) (μ μ' : Measure (Π i : Finset.Iic a, X i))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (η : ℕ → ℝ)
    (h : ∀ n ∈ Finset.Ico a b, ∀ x, tvDist (κ n x) (κ' n x) ≤ η n) :
    tvDist (Kernel.partialTraj κ a b ∘ₘ μ) (Kernel.partialTraj κ' a b ∘ₘ μ') ≤
      tvDist μ μ' + ∑ n ∈ Finset.Ico a b, η n := by
  rcases le_total b a with hba | hab
  · rw [Kernel.partialTraj_le hba, Kernel.partialTraj_le hba,
      Measure.deterministic_comp_eq_map, Measure.deterministic_comp_eq_map,
      Finset.Ico_eq_empty_of_le hba, Finset.sum_empty, add_zero]
    exact tvDist_map_le (Preorder.measurable_frestrictLe₂ hba) μ μ'
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Kernel.partialTraj_succ_eq_comp hab, Kernel.partialTraj_succ_eq_comp hab,
      ← Measure.comp_assoc, ← Measure.comp_assoc, Finset.sum_Ico_succ_top hab, ← add_assoc]
    have ih' := ih (fun n hn x => h n (Finset.Ico_subset_Ico_right b.le_succ hn) x)
    refine (tvDist_comp_le_tvDist_add _ _ _ _ fun x =>
      (tvDist_partialTraj_succ_self_le b x).trans
        (h b (Finset.mem_Ico.2 ⟨hab, b.lt_succ_self⟩) x)).trans ?_
    linarith

/-- The hybrid argument from a common initial law: `TV ≤ ∑_{a ≤ n < b} η n`. -/
theorem tvDist_partialTraj_comp_le_sum (a b : ℕ) (μ : Measure (Π i : Finset.Iic a, X i))
    [IsProbabilityMeasure μ] (η : ℕ → ℝ)
    (h : ∀ n ∈ Finset.Ico a b, ∀ x, tvDist (κ n x) (κ' n x) ≤ η n) :
    tvDist (Kernel.partialTraj κ a b ∘ₘ μ) (Kernel.partialTraj κ' a b ∘ₘ μ) ≤
      ∑ n ∈ Finset.Ico a b, η n := by
  simpa [tvDist_self] using tvDist_partialTraj_comp_le a b μ μ η h

/-- Modifying the step kernels only at the steps in `S ⊆ [a, b)`, each by at most `γ` in total
variation uniformly over histories, changes the law of the history by at most `|S| γ`. In the
proof of `lem:clone` the `T - 1` rounds of common items are modified, which gives
`TV(P, P̃) ≤ (T - 1) γ_σ(p) = β_p`. -/
theorem tvDist_partialTraj_comp_le_card (a b : ℕ) (μ : Measure (Π i : Finset.Iic a, X i))
    [IsProbabilityMeasure μ] (S : Finset ℕ) (hS : S ⊆ Finset.Ico a b) (γ : ℝ)
    (hsame : ∀ n ∉ S, κ n = κ' n) (hmod : ∀ n ∈ S, ∀ x, tvDist (κ n x) (κ' n x) ≤ γ) :
    tvDist (Kernel.partialTraj κ a b ∘ₘ μ) (Kernel.partialTraj κ' a b ∘ₘ μ) ≤ S.card * γ := by
  have key := tvDist_partialTraj_comp_le_sum (κ := κ) (κ' := κ') a b μ
    (fun n => if n ∈ S then γ else 0) fun n _ x => by
      by_cases hn : n ∈ S
      · simpa [hn] using hmod n hn x
      · simp [hn, hsame n hn, tvDist_self]
  rwa [Finset.sum_ite_mem, Finset.inter_eq_right.2 hS, Finset.sum_const, nsmul_eq_mul] at key

end Trajectory

/-! ### Positive parts and densities -/

section Densities

variable {μ : Measure Ω}

/-- `∫_A h ≤ ∫ h_+` for every set `A`. -/
private lemma setIntegral_le_integral_max {h : Ω → ℝ} (hi : Integrable h μ) {A : Set Ω} :
    ∫ x in A, h x ∂μ ≤ ∫ x, max (h x) 0 ∂μ :=
  (setIntegral_mono hi.integrableOn hi.pos_part.integrableOn fun _ => le_max_left _ _).trans
    (setIntegral_le_integral hi.pos_part (Filter.Eventually.of_forall fun _ => le_max_right _ _))

/-- `∫_{h > 0} h = ∫ h_+`. -/
private lemma setIntegral_pos_eq_integral_max {h : Ω → ℝ} (hm : Measurable h) :
    ∫ x in {x | 0 < h x}, h x ∂μ = ∫ x, max (h x) 0 ∂μ := by
  rw [← integral_indicator (measurableSet_lt measurable_const hm)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : 0 < h x
  · simp [Set.indicator_of_mem (show x ∈ {x | 0 < h x} from hx), max_eq_left hx.le]
  · simp [Set.indicator_of_notMem (show x ∉ {x | 0 < h x} from hx), max_eq_right (not_lt.1 hx)]

/-- If `P(A) - e^ε Q(A) = ∫_A h dν` for every measurable `A`, then `H_ε(P,Q) = ∫ h_+ dν`. -/
private lemma hockeyStick_eq_integral_max_of_setIntegral {P Q ν : Measure Ω} [IsFiniteMeasure P]
    {ε : ℝ} {h : Ω → ℝ} (hm : Measurable h) (hi : Integrable h ν)
    (hset : ∀ A, MeasurableSet A → (P A).toReal - Real.exp ε * (Q A).toReal = ∫ x in A, h x ∂ν) :
    hockeyStick P Q ε = ∫ x, max (h x) 0 ∂ν := by
  refine le_antisymm (hockeyStick_le fun A hA => ?_) ?_
  · rw [hset A hA]
    exact setIntegral_le_integral_max hi
  · have hA : MeasurableSet {x | 0 < h x} := measurableSet_lt measurable_const hm
    rw [← setIntegral_pos_eq_integral_max hm, ← hset _ hA]
    exact le_hockeyStick ε hA

private lemma toReal_withDensity_apply {f : Ω → ℝ} (hi : Integrable f μ) (h0 : ∀ x, 0 ≤ f x)
    {A : Set Ω} (hA : MeasurableSet A) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x)) A).toReal = ∫ x in A, f x ∂μ := by
  rw [withDensity_apply _ hA, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h0) hi.aestronglyMeasurable.restrict]

/-- Total variation between two measures with nonnegative integrable densities of equal mass:
`TV(f₁ μ, f₂ μ) = ∫ (f₂ - f₁)_+ dμ`. -/
theorem tvDist_withDensity_eq {f₁ f₂ : Ω → ℝ} (hm₁ : Measurable f₁) (hm₂ : Measurable f₂)
    (hi₁ : Integrable f₁ μ) (hi₂ : Integrable f₂ μ) (h0₁ : ∀ x, 0 ≤ f₁ x) (h0₂ : ∀ x, 0 ≤ f₂ x)
    (hmass : ∫ x, f₁ x ∂μ = ∫ x, f₂ x ∂μ) :
    tvDist (μ.withDensity fun x => ENNReal.ofReal (f₁ x))
      (μ.withDensity fun x => ENNReal.ofReal (f₂ x)) = ∫ x, max (f₂ x - f₁ x) 0 ∂μ := by
  have : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f₁ x)) :=
    isFiniteMeasure_withDensity_ofReal hi₁.2
  have : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f₂ x)) :=
    isFiniteMeasure_withDensity_ofReal hi₂.2
  have hsym : ∫ x, max (f₁ x - f₂ x) 0 ∂μ = ∫ x, max (f₂ x - f₁ x) 0 ∂μ := by
    have hpt : ∀ x, max (f₁ x - f₂ x) 0 - max (f₂ x - f₁ x) 0 = f₁ x - f₂ x := by
      intro x
      rcases le_total (f₁ x) (f₂ x) with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have := integral_sub (hi₁.sub hi₂).pos_part (hi₂.sub hi₁).pos_part (μ := μ)
    simp only [Pi.sub_apply, hpt] at this
    rw [integral_sub hi₁ hi₂, hmass, sub_self] at this
    linarith
  refine le_antisymm (tvDist_le fun A hA => ?_) ?_
  · rw [toReal_withDensity_apply hi₁ h0₁ hA, toReal_withDensity_apply hi₂ h0₂ hA, abs_sub_le_iff,
      ← integral_sub hi₁.integrableOn hi₂.integrableOn,
      ← integral_sub hi₂.integrableOn hi₁.integrableOn]
    exact ⟨hsym ▸ setIntegral_le_integral_max (hi₁.sub hi₂),
      setIntegral_le_integral_max (hi₂.sub hi₁)⟩
  · have hA : MeasurableSet {x | 0 < f₂ x - f₁ x} :=
      measurableSet_lt measurable_const (hm₂.sub hm₁)
    have := le_tvDist (P := μ.withDensity fun x => ENNReal.ofReal (f₁ x))
      (Q := μ.withDensity fun x => ENNReal.ofReal (f₂ x)) hA
    rw [toReal_withDensity_apply hi₁ h0₁ hA, toReal_withDensity_apply hi₂ h0₂ hA, abs_sub_comm,
      ← integral_sub hi₂.integrableOn hi₁.integrableOn,
      setIntegral_pos_eq_integral_max (h := fun x => f₂ x - f₁ x) (hm₂.sub hm₁)] at this
    exact (le_abs_self _).trans this

end Densities

/-! ### The kernel modification -/

section Modification

variable {μ : Measure Ω}

/-- A probability density with respect to `μ`. -/
structure IsProbDensity (μ : Measure Ω) (g : Ω → ℝ) : Prop where
  measurable : Measurable g
  nonneg : ∀ x, 0 ≤ g x
  integrable : Integrable g μ
  integral_eq_one : ∫ x, g x ∂μ = 1

/-- The defect `η = ∫ (p g₀ - g)_+ dμ` from the proof of `lem:clone`. -/
noncomputable def cloneDefect (μ : Measure Ω) (g₀ g : Ω → ℝ) (p : ℝ) : ℝ :=
  ∫ x, max (p * g₀ x - g x) 0 ∂μ

/-- The residual density `r = (g - p g₀)_+ / (1 - p + η)` from the proof of `lem:clone`. -/
noncomputable def cloneResidual (μ : Measure Ω) (g₀ g : Ω → ℝ) (p : ℝ) (x : Ω) : ℝ :=
  max (g x - p * g₀ x) 0 / (1 - p + cloneDefect μ g₀ g p)

/-- The modified density `g̃ = p g₀ + (1 - p) r` from the proof of `lem:clone`. -/
noncomputable def cloneDensity (μ : Measure Ω) (g₀ g : Ω → ℝ) (p : ℝ) (x : Ω) : ℝ :=
  p * g₀ x + (1 - p) * cloneResidual μ g₀ g p x

variable {g₀ g : Ω → ℝ} {p : ℝ}

theorem cloneDefect_nonneg : 0 ≤ cloneDefect μ g₀ g p :=
  integral_nonneg fun _ => le_max_right _ _

/-- `∫ (g - p g₀)_+ dμ = 1 - p + η`. -/
theorem integral_max_sub_eq (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g) :
    ∫ x, max (g x - p * g₀ x) 0 ∂μ = 1 - p + cloneDefect μ g₀ g p := by
  have hi : Integrable (fun x => g x - p * g₀ x) μ := h.integrable.sub (h₀.integrable.const_mul p)
  have hpt : ∀ x, max (g x - p * g₀ x) 0 - max (p * g₀ x - g x) 0 = g x - p * g₀ x := by
    intro x
    rcases le_total (g x) (p * g₀ x) with hx | hx
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have := integral_sub hi.pos_part (hi.neg.pos_part) (μ := μ)
  simp only [Pi.neg_apply, neg_sub, hpt] at this
  rw [integral_sub h.integrable (h₀.integrable.const_mul p), integral_const_mul,
    h.integral_eq_one, h₀.integral_eq_one, mul_one] at this
  unfold cloneDefect
  linarith

theorem cloneResidual_nonneg (hp : p ≤ 1) (x : Ω) : 0 ≤ cloneResidual μ g₀ g p x :=
  div_nonneg (le_max_right _ _)
    (by linarith [cloneDefect_nonneg (μ := μ) (g₀ := g₀) (g := g) (p := p)])

theorem measurable_cloneResidual (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g) :
    Measurable (cloneResidual μ g₀ g p) :=
  ((h.measurable.sub (h₀.measurable.const_mul p)).max measurable_const).div_const _

theorem integrable_cloneResidual (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g) :
    Integrable (cloneResidual μ g₀ g p) μ :=
  (h.integrable.sub (h₀.integrable.const_mul p)).pos_part.div_const _

/-- The residual density integrates to one when `p < 1`. -/
theorem integral_cloneResidual (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g) (hp : p < 1) :
    ∫ x, cloneResidual μ g₀ g p x ∂μ = 1 := by
  have hD : 0 < 1 - p + cloneDefect μ g₀ g p := by
    linarith [cloneDefect_nonneg (μ := μ) (g₀ := g₀) (g := g) (p := p)]
  unfold cloneResidual
  rw [integral_div, integral_max_sub_eq h₀ h, div_self hD.ne']

/-- The residual is a probability density when `0 ≤ p < 1`. -/
theorem isProbDensity_cloneResidual (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g)
    (hp : p < 1) : IsProbDensity μ (cloneResidual μ g₀ g p) :=
  ⟨measurable_cloneResidual h₀ h, cloneResidual_nonneg hp.le, integrable_cloneResidual h₀ h,
    integral_cloneResidual h₀ h hp⟩

theorem cloneDensity_nonneg (h₀ : IsProbDensity μ g₀) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Ω) :
    0 ≤ cloneDensity μ g₀ g p x :=
  add_nonneg (mul_nonneg hp0 (h₀.nonneg x))
    (mul_nonneg (by linarith) (cloneResidual_nonneg hp1 x))

/-- The modified density integrates to one. -/
theorem integral_cloneDensity (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g) (hp : p ≤ 1) :
    ∫ x, cloneDensity μ g₀ g p x ∂μ = 1 := by
  unfold cloneDensity
  rw [integral_add (h₀.integrable.const_mul p) ((integrable_cloneResidual h₀ h).const_mul _),
    integral_const_mul, integral_const_mul, h₀.integral_eq_one]
  rcases hp.lt_or_eq with hp | rfl
  · rw [integral_cloneResidual h₀ h hp]; ring
  · ring

theorem isProbDensity_cloneDensity (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProbDensity μ (cloneDensity μ g₀ g p) :=
  ⟨(h₀.measurable.const_mul p).add ((measurable_cloneResidual h₀ h).const_mul _),
    cloneDensity_nonneg h₀ hp0 hp1,
    (h₀.integrable.const_mul p).add ((integrable_cloneResidual h₀ h).const_mul _),
    integral_cloneDensity h₀ h hp1⟩

/-- Pointwise, `(g̃ - g)_+ = (p g₀ - g)_+`. -/
private lemma max_cloneDensity_sub (hp : p ≤ 1) (x : Ω) :
    max (cloneDensity μ g₀ g p x - g x) 0 = max (p * g₀ x - g x) 0 := by
  set D := 1 - p + cloneDefect μ g₀ g p
  have hD : 1 - p ≤ D := by linarith [cloneDefect_nonneg (μ := μ) (g₀ := g₀) (g := g) (p := p)]
  set c := (1 - p) / D with hc
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have hc1 : c ≤ 1 := div_le_one_of_le₀ hD (by linarith)
  have hg : cloneDensity μ g₀ g p x = p * g₀ x + c * max (g x - p * g₀ x) 0 := by
    simp only [cloneDensity, cloneResidual, hc]
    ring
  rw [hg]
  rcases le_total (p * g₀ x) (g x) with hx | hx
  · have h1 : p * g₀ x + c * (g x - p * g₀ x) - g x ≤ 0 := by nlinarith
    rw [max_eq_left (by linarith : 0 ≤ g x - p * g₀ x), max_eq_right h1,
      max_eq_right (by linarith : p * g₀ x - g x ≤ 0)]
  · rw [max_eq_right (by linarith : g x - p * g₀ x ≤ 0), mul_zero, add_zero]

/-- `TV(g, g̃) = η` (proof of `lem:clone`). -/
theorem tvDist_withDensity_cloneDensity (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    tvDist (μ.withDensity fun x => ENNReal.ofReal (g x))
      (μ.withDensity fun x => ENNReal.ofReal (cloneDensity μ g₀ g p x)) =
      cloneDefect μ g₀ g p := by
  have h' := isProbDensity_cloneDensity h₀ h hp0 hp1
  rw [tvDist_withDensity_eq h.measurable h'.measurable h.integrable h'.integrable h.nonneg
    h'.nonneg (by rw [h.integral_eq_one, h'.integral_eq_one])]
  simp_rw [max_cloneDensity_sub hp1]
  rfl

/-- Coin realization: the modified law is the mixture that emits `g₀` with probability `p` and
the residual `r` with probability `1 - p` (proof of `lem:clone`). -/
theorem withDensity_cloneDensity (h₀ : IsProbDensity μ g₀) (h : IsProbDensity μ g)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (μ.withDensity fun x => ENNReal.ofReal (cloneDensity μ g₀ g p x)) =
      ENNReal.ofReal p • μ.withDensity (fun x => ENNReal.ofReal (g₀ x)) +
        ENNReal.ofReal (1 - p) •
          μ.withDensity (fun x => ENNReal.ofReal (cloneResidual μ g₀ g p x)) := by
  have hm₀ : Measurable fun x => ENNReal.ofReal (g₀ x) := h₀.measurable.ennreal_ofReal
  have hmr : Measurable fun x => ENNReal.ofReal (cloneResidual μ g₀ g p x) :=
    (measurable_cloneResidual h₀ h).ennreal_ofReal
  have hfun : (fun x => ENNReal.ofReal (cloneDensity μ g₀ g p x)) =
      (ENNReal.ofReal p • fun x => ENNReal.ofReal (g₀ x)) +
        (ENNReal.ofReal (1 - p) • fun x => ENNReal.ofReal (cloneResidual μ g₀ g p x)) := by
    ext x
    simp only [cloneDensity, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_add (mul_nonneg hp0 (h₀.nonneg x))
        (mul_nonneg (by linarith) (cloneResidual_nonneg hp1 x)),
      ENNReal.ofReal_mul hp0, ENNReal.ofReal_mul (by linarith)]
  rw [hfun, withDensity_add_left (hm₀.const_smul _), withDensity_smul _ hm₀,
    withDensity_smul _ hmr]

end Modification

/-! ### Likelihood-ratio form of the hockey-stick divergence -/

section LikelihoodRatio

variable {P Q : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure Q]

/-- `H_ε(P,Q) = E_Q (L - e^ε)_+` with `L = dP/dQ`. -/
theorem hockeyStick_eq_integral_rnDeriv (hPQ : P ≪ Q) (ε : ℝ) :
    hockeyStick P Q ε = ∫ x, max 0 ((P.rnDeriv Q x).toReal - Real.exp ε) ∂Q := by
  have hL : Measurable fun x => (P.rnDeriv Q x).toReal :=
    (Measure.measurable_rnDeriv P Q).ennreal_toReal
  have hLi : Integrable (fun x => (P.rnDeriv Q x).toReal) Q := Measure.integrable_toReal_rnDeriv
  simp_rw [max_comm (0 : ℝ)]
  refine hockeyStick_eq_integral_max_of_setIntegral (hL.sub measurable_const)
    (hLi.sub (integrable_const _)) fun A hA => ?_
  rw [integral_sub hLi.integrableOn (integrable_const _).integrableOn,
    Measure.setIntegral_toReal_rnDeriv hPQ A, setIntegral_const, smul_eq_mul, measureReal_def,
    measureReal_def]
  ring

/-- `H_ε(Q,P) = E_Q (1 - e^ε L)_+` with `L = dP/dQ`. -/
theorem hockeyStick_swap_eq_integral_rnDeriv (hPQ : P ≪ Q) (ε : ℝ) :
    hockeyStick Q P ε = ∫ x, max 0 (1 - Real.exp ε * (P.rnDeriv Q x).toReal) ∂Q := by
  have hL : Measurable fun x => (P.rnDeriv Q x).toReal :=
    (Measure.measurable_rnDeriv P Q).ennreal_toReal
  have hLi : Integrable (fun x => (P.rnDeriv Q x).toReal) Q := Measure.integrable_toReal_rnDeriv
  simp_rw [max_comm (0 : ℝ)]
  refine hockeyStick_eq_integral_max_of_setIntegral (measurable_const.sub (hL.const_mul _))
    ((integrable_const _).sub (hLi.const_mul _)) fun A hA => ?_
  rw [integral_sub (integrable_const _).integrableOn (hLi.const_mul _).integrableOn,
    integral_const_mul, Measure.setIntegral_toReal_rnDeriv hPQ A, setIntegral_const,
    smul_eq_mul, mul_one, measureReal_def, measureReal_def]

/-- The forward divergence at `ε = log k` is `E_Q (L - k)_+`, as in the proof of `lem:clone`. -/
theorem hockeyStick_log_eq_integral_rnDeriv (hPQ : P ≪ Q) {k : ℝ} (hk : 0 < k) :
    hockeyStick P Q (Real.log k) = ∫ x, max 0 ((P.rnDeriv Q x).toReal - k) ∂Q := by
  rw [hockeyStick_eq_integral_rnDeriv hPQ, Real.exp_log hk]

/-- The reverse divergence at `ε = log k` is `E_Q (1 - k L)_+`, as in the proof of `lem:clone`. -/
theorem hockeyStick_swap_log_eq_integral_rnDeriv (hPQ : P ≪ Q) {k : ℝ} (hk : 0 < k) :
    hockeyStick Q P (Real.log k) = ∫ x, max 0 (1 - k * (P.rnDeriv Q x).toReal) ∂Q := by
  rw [hockeyStick_swap_eq_integral_rnDeriv hPQ, Real.exp_log hk]

end LikelihoodRatio

end ASGA
