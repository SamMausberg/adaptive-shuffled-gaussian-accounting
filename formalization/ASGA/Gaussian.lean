import ASGA.Basic

/-!
# Gaussian computations for the null-clone bound and the candidate count

This file proves the Gaussian facts used by Lemma `lem:clone` and Proposition `prop:counts`
of `paper/main.tex`, for a noise scale `σ > 0`. Write `X = exp(Z/σ - 1/(2σ²))` with
`Z ~ N(0,1)` for the likelihood ratio of `lem:clone`.

* `setIntegral_exp_tilt`: the exponential tilt `∫_B exp(a z - a²/2) dN(0,1) = N(a,1)(B)`.
* `hockeyStick_gaussianReal`, `hockeyStick_gaussianReal_symm`: the hockey-stick divergence
  between `N(1,σ²)` and `N(0,σ²)`, in either order, is the profile `g_σ` of `eq:gaussian`.
* `integral_lr_sub_pos`, `integral_one_sub_mul_lr_pos`: `E(X - k)_+ = E(1 - kX)_+ = g_σ(log k)`.
* `integral_clone_eq_cloneCost`, `integral_clone_le_cloneCost`,
  `integral_clone_euclidean_le_cloneCost`: the clone integral `∫ (p g_0 - g_u)_+` equals
  `γ_σ(p)` of `eq:gamma` for a unit scalar displacement and is at most `γ_σ(p)` for every
  `u ∈ ℝ^d` with `‖u‖ ≤ 1`.
* `integral_lr_sub_truncLR`, `truncLR_le`: the tail correction `eq:tau` of `app:certificate`.
* `callF_succ`, `putJ_succ`, `convexOn_callF`, `convexOn_putJ`: the recurrences
  `eq:recurrences` and convexity of `F_m`, `J_m`.
* `counts_bound_forward`, `counts_bound_reverse`: Proposition `prop:counts`, with the two
  conclusions `eq:clonef` and `eq:cloner` of `lem:clone` taken as hypotheses.

Declarations live in `ASGA.Gaussian`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ASGA

namespace Gaussian

/-! ### Half-lines under `N(m, 1)` -/

section HalfLines

private lemma gaussianReal_one_eq_map_add (m : ℝ) :
    gaussianReal m 1 = (gaussianReal 0 1).map (· + m) := by
  simpa using (gaussianReal_map_add_const (μ := 0) (v := 1) m).symm

private lemma gaussianReal_one_eq_map_sub (m : ℝ) :
    gaussianReal m 1 = (gaussianReal 0 1).map (m - ·) := by
  simpa using (gaussianReal_map_const_sub (μ := 0) (v := 1) m).symm

lemma Phi_eq (x : ℝ) : Phi x = (gaussianReal 0 1 (Iic x)).toReal := by
  rw [Phi, cdf_eq_real, measureReal_def]

lemma gaussianReal_one_Iic (m t : ℝ) : (gaussianReal m 1 (Iic t)).toReal = Phi (t - m) := by
  rw [gaussianReal_one_eq_map_add, Measure.map_apply (measurable_add_const m) measurableSet_Iic,
    Phi_eq]
  congr 2
  ext z
  simp [le_sub_iff_add_le]

lemma gaussianReal_one_Iio (m t : ℝ) : (gaussianReal m 1 (Iio t)).toReal = Phi (t - m) := by
  have := nullSingletonClass_gaussianReal (μ := m) (v := 1) one_ne_zero
  rw [measure_congr Iio_ae_eq_Iic, gaussianReal_one_Iic]

lemma gaussianReal_one_Ioi (m t : ℝ) : (gaussianReal m 1 (Ioi t)).toReal = Phi (m - t) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [gaussianReal_one_eq_map_sub, Measure.map_apply (measurable_const_sub m) measurableSet_Ioi,
    Phi_eq]
  have : (fun z => m - z) ⁻¹' Ioi t = Iio (m - t) := by
    ext z
    simp [lt_sub_comm]
  rw [this, measure_congr Iio_ae_eq_Iic]

end HalfLines

/-! ### Exponential tilt -/

section Tilt

lemma gaussianPDFReal_tilt (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x = gaussianPDFReal 0 v x * Real.exp ((m * x - m ^ 2 / 2) / v) := by
  simp only [gaussianPDFReal, sub_zero, mul_assoc, ← Real.exp_add]
  congr 2
  by_cases hv : (v : ℝ) = 0
  · simp [hv]
  · field_simp
    ring

/-- `N(a,1)` has density `z ↦ exp(a z - a²/2)` with respect to `N(0,1)`. -/
lemma gaussianReal_one_eq_withDensity (a : ℝ) :
    gaussianReal a 1 = (gaussianReal 0 1).withDensity
      (fun z => ENNReal.ofReal (Real.exp (a * z - a ^ 2 / 2))) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  ext z
  simp only [Pi.mul_apply, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  rw [gaussianPDFReal_tilt a 1 z]
  simp

lemma integrable_exp_tilt (a : ℝ) :
    Integrable (fun z => Real.exp (a * z - a ^ 2 / 2)) (gaussianReal 0 1) := by
  have := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).mul_const (Real.exp (-(a ^ 2 / 2)))
  refine this.congr (ae_of_all _ fun z => ?_)
  simp only [← Real.exp_add, sub_eq_add_neg]

/-- Exponential tilt of the standard normal law: for measurable `B`,
`∫_B exp(a z - a²/2) dN(0,1)(z) = N(a,1)(B)`. -/
theorem setIntegral_exp_tilt (a : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    ∫ z in B, Real.exp (a * z - a ^ 2 / 2) ∂gaussianReal 0 1 = (gaussianReal a 1 B).toReal := by
  rw [gaussianReal_one_eq_withDensity a, withDensity_apply _ hB,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
      (by fun_prop)]

/-- Half-line form of the tilt: `∫_{z > t} exp(a z - a²/2) dN(0,1) = Φ(a - t)`. -/
theorem setIntegral_exp_tilt_Ioi (a t : ℝ) :
    ∫ z in Ioi t, Real.exp (a * z - a ^ 2 / 2) ∂gaussianReal 0 1 = Phi (a - t) := by
  rw [setIntegral_exp_tilt a measurableSet_Ioi, gaussianReal_one_Ioi]

/-- Half-line form of the tilt: `∫_{z < t} exp(a z - a²/2) dN(0,1) = Φ(t - a)`. -/
theorem setIntegral_exp_tilt_Iio (a t : ℝ) :
    ∫ z in Iio t, Real.exp (a * z - a ^ 2 / 2) ∂gaussianReal 0 1 = Phi (t - a) := by
  rw [setIntegral_exp_tilt a measurableSet_Iio, gaussianReal_one_Iio]

lemma integral_exp_tilt (a : ℝ) :
    ∫ z, Real.exp (a * z - a ^ 2 / 2) ∂gaussianReal 0 1 = 1 := by
  rw [← setIntegral_univ, setIntegral_exp_tilt a MeasurableSet.univ]
  simp

end Tilt

/-! ### Positive parts -/

section PosPart

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}

lemma integral_max_zero_eq_setIntegral {S : Set α} (hS : MeasurableSet S)
    (h1 : ∀ x ∈ S, 0 ≤ f x) (h2 : ∀ x ∉ S, f x ≤ 0) :
    ∫ x, max (f x) 0 ∂ν = ∫ x in S, f x ∂ν := by
  rw [← integral_indicator hS]
  congr 1
  ext x
  by_cases hx : x ∈ S
  · simp [hx, h1 x hx]
  · simp [hx, h2 x hx]

lemma setIntegral_le_integral_max_zero (hf : Integrable f ν) (A : Set α) :
    ∫ x in A, f x ∂ν ≤ ∫ x, max (f x) 0 ∂ν :=
  calc ∫ x in A, f x ∂ν ≤ ∫ x in A, max (f x) 0 ∂ν :=
        setIntegral_mono hf.integrableOn hf.pos_part.integrableOn fun _ => le_max_left _ _
    _ ≤ ∫ x, max (f x) 0 ∂ν :=
        setIntegral_le_integral hf.pos_part (ae_of_all _ fun _ => le_max_right _ _)

end PosPart

/-! ### The likelihood ratio `X = exp(Z/σ - 1/(2σ²))` -/

section LikelihoodRatio

variable {σ k : ℝ}

lemma lr_eq_tilt (hσ : σ ≠ 0) (z : ℝ) :
    Real.exp (z / σ - 1 / (2 * σ ^ 2)) = Real.exp (σ⁻¹ * z - σ⁻¹ ^ 2 / 2) := by
  congr 1
  field_simp

lemma integrable_lr (hσ : σ ≠ 0) :
    Integrable (fun z => Real.exp (z / σ - 1 / (2 * σ ^ 2))) (gaussianReal 0 1) := by
  simp_rw [lr_eq_tilt hσ]
  exact integrable_exp_tilt _

lemma integral_lr (hσ : σ ≠ 0) :
    ∫ z, Real.exp (z / σ - 1 / (2 * σ ^ 2)) ∂gaussianReal 0 1 = 1 := by
  simp_rw [lr_eq_tilt hσ]
  exact integral_exp_tilt _

private lemma lr_call_threshold (hσ : σ ≠ 0) (hk : 0 < k) (z : ℝ) :
    Real.exp (z / σ - 1 / (2 * σ ^ 2)) =
      k * Real.exp ((z - (σ * Real.log k + 1 / (2 * σ))) / σ) := by
  have : z / σ - 1 / (2 * σ ^ 2) = Real.log k + (z - (σ * Real.log k + 1 / (2 * σ))) / σ := by
    field_simp
    ring
  rw [this, Real.exp_add, Real.exp_log hk]

private lemma lr_put_threshold (hσ : σ ≠ 0) (hk : 0 < k) (z : ℝ) :
    k * Real.exp (z / σ - 1 / (2 * σ ^ 2)) =
      Real.exp ((z - (-σ * Real.log k + 1 / (2 * σ))) / σ) := by
  have : (z - (-σ * Real.log k + 1 / (2 * σ))) / σ = Real.log k + (z / σ - 1 / (2 * σ ^ 2)) := by
    field_simp
    ring
  rw [this, Real.exp_add, Real.exp_log hk]

private lemma integral_call_eq_setIntegral (hσ : 0 < σ) (hk : 0 < k) :
    ∫ z, max (Real.exp (z / σ - 1 / (2 * σ ^ 2)) - k) 0 ∂gaussianReal 0 1 =
      ∫ z in Ioi (σ * Real.log k + 1 / (2 * σ)),
        (Real.exp (z / σ - 1 / (2 * σ ^ 2)) - k) ∂gaussianReal 0 1 := by
  refine integral_max_zero_eq_setIntegral measurableSet_Ioi (fun z hz => ?_) (fun z hz => ?_)
  · have hz' : 0 < (z - (σ * Real.log k + 1 / (2 * σ))) / σ :=
      div_pos (sub_pos.2 hz) hσ
    rw [lr_call_threshold hσ.ne' hk, sub_nonneg]
    exact le_mul_of_one_le_right hk.le (Real.one_le_exp hz'.le)
  · have hz' : (z - (σ * Real.log k + 1 / (2 * σ))) / σ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (not_lt.1 hz)) hσ.le
    rw [lr_call_threshold hσ.ne' hk, sub_nonpos]
    exact mul_le_of_le_one_right hk.le (Real.exp_le_one_iff.2 hz')

private lemma integral_put_eq_setIntegral (hσ : 0 < σ) (hk : 0 < k) :
    ∫ z, max (1 - k * Real.exp (z / σ - 1 / (2 * σ ^ 2))) 0 ∂gaussianReal 0 1 =
      ∫ z in Iio (-σ * Real.log k + 1 / (2 * σ)),
        (1 - k * Real.exp (z / σ - 1 / (2 * σ ^ 2))) ∂gaussianReal 0 1 := by
  refine integral_max_zero_eq_setIntegral measurableSet_Iio (fun z hz => ?_) (fun z hz => ?_)
  · have hz' : (z - (-σ * Real.log k + 1 / (2 * σ))) / σ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (le_of_lt hz)) hσ.le
    rw [lr_put_threshold hσ.ne' hk, sub_nonneg]
    exact Real.exp_le_one_iff.2 hz'
  · have hz' : 0 ≤ (z - (-σ * Real.log k + 1 / (2 * σ))) / σ :=
      div_nonneg (sub_nonneg.2 (not_lt.1 hz)) hσ.le
    rw [lr_put_threshold hσ.ne' hk, sub_nonpos]
    exact Real.one_le_exp hz'

private lemma setIntegral_call (hσ : 0 < σ) (k : ℝ) :
    ∫ z in Ioi (σ * Real.log k + 1 / (2 * σ)),
        (Real.exp (z / σ - 1 / (2 * σ ^ 2)) - k) ∂gaussianReal 0 1 =
      Phi (-σ * Real.log k + 1 / (2 * σ)) - k * Phi (-σ * Real.log k - 1 / (2 * σ)) := by
  have hI : IntegrableOn (fun _ : ℝ => k) (Ioi (σ * Real.log k + 1 / (2 * σ)))
      (gaussianReal 0 1) := integrableOn_const
  rw [integral_sub (integrable_lr hσ.ne').integrableOn hI,
    setIntegral_const, measureReal_def, gaussianReal_one_Ioi]
  simp_rw [lr_eq_tilt hσ.ne']
  rw [setIntegral_exp_tilt_Ioi, smul_eq_mul, mul_comm (Phi _) k]
  have h1 : σ⁻¹ - (σ * Real.log k + 1 / (2 * σ)) = -σ * Real.log k + 1 / (2 * σ) := by
    field_simp
    ring
  have h2 : 0 - (σ * Real.log k + 1 / (2 * σ)) = -σ * Real.log k - 1 / (2 * σ) := by ring
  rw [h1, h2]

private lemma setIntegral_put (hσ : 0 < σ) (k : ℝ) :
    ∫ z in Iio (-σ * Real.log k + 1 / (2 * σ)),
        (1 - k * Real.exp (z / σ - 1 / (2 * σ ^ 2))) ∂gaussianReal 0 1 =
      Phi (-σ * Real.log k + 1 / (2 * σ)) - k * Phi (-σ * Real.log k - 1 / (2 * σ)) := by
  have hI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iio (-σ * Real.log k + 1 / (2 * σ)))
      (gaussianReal 0 1) := integrableOn_const
  rw [integral_sub hI ((integrable_lr hσ.ne').const_mul k).integrableOn,
    setIntegral_const, measureReal_def, gaussianReal_one_Iio, integral_const_mul]
  simp_rw [lr_eq_tilt hσ.ne']
  rw [setIntegral_exp_tilt_Iio, smul_eq_mul, mul_one]
  have h1 : -σ * Real.log k + 1 / (2 * σ) - σ⁻¹ = -σ * Real.log k - 1 / (2 * σ) := by
    field_simp
    ring
  rw [h1, sub_zero]

/-- With `Z ~ N(0,1)` and `X = exp(Z/σ - 1/(2σ²))` as in `lem:clone`, `E(X - k)_+ = g_σ(log k)`
for every `k > 0`, with `g_σ` from `eq:gaussian`. -/
theorem integral_lr_sub_pos (hσ : 0 < σ) (hk : 0 < k) :
    ∫ z, max (Real.exp (z / σ - 1 / (2 * σ ^ 2)) - k) 0 ∂gaussianReal 0 1 =
      gaussProfile σ (Real.log k) := by
  rw [integral_call_eq_setIntegral hσ hk, setIntegral_call hσ, gaussProfile, Real.exp_log hk]

/-- With `X` as in `lem:clone`, `E(1 - kX)_+ = g_σ(log k)` for every `k > 0`. -/
theorem integral_one_sub_mul_lr_pos (hσ : 0 < σ) (hk : 0 < k) :
    ∫ z, max (1 - k * Real.exp (z / σ - 1 / (2 * σ ^ 2))) 0 ∂gaussianReal 0 1 =
      gaussProfile σ (Real.log k) := by
  rw [integral_put_eq_setIntegral hσ hk, setIntegral_put hσ, gaussProfile, Real.exp_log hk]

end LikelihoodRatio

/-! ### The sensitivity-one Gaussian profile -/

section Profile

variable {σ : ℝ}

lemma gaussianReal_sq_eq_map (hσ : σ ≠ 0) (m : ℝ) :
    gaussianReal m (σ ^ 2).toNNReal = (gaussianReal (m / σ) 1).map (σ * ·) := by
  rw [gaussianReal_map_const_mul, mul_div_cancel₀ _ hσ]
  congr 1
  ext
  simp [sq_nonneg]

private lemma preimage_mul_Ioi (hσ : 0 < σ) (t : ℝ) : (σ * ·) ⁻¹' Ioi (σ * t) = Ioi t := by
  ext z
  simp [mul_lt_mul_iff_right₀ hσ]

private lemma preimage_mul_Iio (hσ : 0 < σ) (t : ℝ) : (σ * ·) ⁻¹' Iio (σ * t) = Iio t := by
  ext z
  simp [mul_lt_mul_iff_right₀ hσ]

/-- Forward pair: `P(A) - e^ε Q(A)` as an integral against `N(0,1)` after scaling by `σ`. -/
private lemma profile_forward_eq (hσ : 0 < σ) (ε : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (gaussianReal 1 (σ ^ 2).toNNReal A).toReal -
        Real.exp ε * (gaussianReal 0 (σ ^ 2).toNNReal A).toReal
      = ∫ z in (σ * ·) ⁻¹' A, (Real.exp (z / σ - 1 / (2 * σ ^ 2)) - Real.exp ε)
          ∂gaussianReal 0 1 := by
  have hB : MeasurableSet ((σ * ·) ⁻¹' A) := measurable_const_mul σ hA
  rw [gaussianReal_sq_eq_map hσ.ne', gaussianReal_sq_eq_map hσ.ne',
    Measure.map_apply (measurable_const_mul σ) hA, Measure.map_apply (measurable_const_mul σ) hA,
    zero_div, integral_sub (integrable_lr hσ.ne').integrableOn integrableOn_const,
    setIntegral_const, measureReal_def, smul_eq_mul, mul_comm _ (Real.exp ε)]
  simp_rw [lr_eq_tilt hσ.ne']
  rw [setIntegral_exp_tilt _ hB, one_div]

/-- Reverse pair: `Q(A) - e^ε P(A)` as an integral against `N(0,1)` after scaling by `σ`. -/
private lemma profile_reverse_eq (hσ : 0 < σ) (ε : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (gaussianReal 0 (σ ^ 2).toNNReal A).toReal -
        Real.exp ε * (gaussianReal 1 (σ ^ 2).toNNReal A).toReal
      = ∫ z in (σ * ·) ⁻¹' A, (1 - Real.exp ε * Real.exp (z / σ - 1 / (2 * σ ^ 2)))
          ∂gaussianReal 0 1 := by
  have hB : MeasurableSet ((σ * ·) ⁻¹' A) := measurable_const_mul σ hA
  have hI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) ((σ * ·) ⁻¹' A) (gaussianReal 0 1) :=
    integrableOn_const
  rw [gaussianReal_sq_eq_map hσ.ne', gaussianReal_sq_eq_map hσ.ne',
    Measure.map_apply (measurable_const_mul σ) hA, Measure.map_apply (measurable_const_mul σ) hA,
    zero_div, integral_sub hI ((integrable_lr hσ.ne').const_mul _).integrableOn,
    setIntegral_const, measureReal_def, smul_eq_mul, mul_one, integral_const_mul]
  simp_rw [lr_eq_tilt hσ.ne']
  rw [setIntegral_exp_tilt _ hB, one_div]

/-- Equation `eq:gaussian`: the hockey-stick divergence of `N(1,σ²)` from `N(0,σ²)` is the
sensitivity-one Gaussian profile `g_σ(ε)`. -/
theorem hockeyStick_gaussianReal (hσ : 0 < σ) (ε : ℝ) :
    hockeyStick (gaussianReal 1 (σ ^ 2).toNNReal) (gaussianReal 0 (σ ^ 2).toNNReal) ε =
      gaussProfile σ ε := by
  have hg := integral_lr_sub_pos hσ (Real.exp_pos ε)
  rw [Real.log_exp] at hg
  apply le_antisymm
  · refine hockeyStick_le fun A hA => ?_
    rw [profile_forward_eq hσ ε hA, ← hg]
    exact setIntegral_le_integral_max_zero ((integrable_lr hσ.ne').sub (integrable_const _)) _
  · have h := le_hockeyStick (P := gaussianReal 1 (σ ^ 2).toNNReal)
      (Q := gaussianReal 0 (σ ^ 2).toNNReal) ε
      (measurableSet_Ioi (a := σ * (σ * ε + 1 / (2 * σ))))
    have hS := integral_call_eq_setIntegral hσ (Real.exp_pos ε)
    rw [Real.log_exp] at hS
    rwa [profile_forward_eq hσ ε measurableSet_Ioi, preimage_mul_Ioi hσ, ← hS, hg] at h

/-- Equation `eq:gaussian`, reversed pair: the hockey-stick divergence of `N(0,σ²)` from
`N(1,σ²)` is also `g_σ(ε)`. -/
theorem hockeyStick_gaussianReal_symm (hσ : 0 < σ) (ε : ℝ) :
    hockeyStick (gaussianReal 0 (σ ^ 2).toNNReal) (gaussianReal 1 (σ ^ 2).toNNReal) ε =
      gaussProfile σ ε := by
  have hg := integral_one_sub_mul_lr_pos hσ (Real.exp_pos ε)
  rw [Real.log_exp] at hg
  apply le_antisymm
  · refine hockeyStick_le fun A hA => ?_
    rw [profile_reverse_eq hσ ε hA, ← hg]
    exact setIntegral_le_integral_max_zero
      ((integrable_const _).sub ((integrable_lr hσ.ne').const_mul _)) _
  · have h := le_hockeyStick (P := gaussianReal 0 (σ ^ 2).toNNReal)
      (Q := gaussianReal 1 (σ ^ 2).toNNReal) ε
      (measurableSet_Iio (a := σ * (-σ * ε + 1 / (2 * σ))))
    have hS := integral_put_eq_setIntegral hσ (Real.exp_pos ε)
    rw [Real.log_exp] at hS
    rwa [profile_reverse_eq hσ ε measurableSet_Iio, preimage_mul_Iio hσ, ← hS, hg] at h

end Profile

/-! ### The null-clone cost -/

section Clone

variable {σ p : ℝ}

/-- `Λ_p(a) = ∫ (p - exp(a z - a²/2))_+ dN(0,1)(z)`, the clone integral for a scalar
displacement `a σ` written against the standard normal law. -/
private noncomputable def cloneFn (p a : ℝ) : ℝ :=
  ∫ z, max (p - Real.exp (a * z - a ^ 2 / 2)) 0 ∂gaussianReal 0 1

private lemma integrable_p_sub_tilt (p a : ℝ) :
    Integrable (fun z => p - Real.exp (a * z - a ^ 2 / 2)) (gaussianReal 0 1) :=
  (integrable_const p).sub (integrable_exp_tilt a)

private lemma cloneFn_nonneg (p a : ℝ) : 0 ≤ cloneFn p a :=
  integral_nonneg fun _ => le_max_right _ _

private lemma setIntegral_Iio_p_sub_tilt (p a r : ℝ) :
    ∫ z in Iio r, (p - Real.exp (a * z - a ^ 2 / 2)) ∂gaussianReal 0 1 =
      p * Phi r - Phi (r - a) := by
  have hI : IntegrableOn (fun _ : ℝ => p) (Iio r) (gaussianReal 0 1) := integrableOn_const
  rw [integral_sub hI (integrable_exp_tilt a).integrableOn, setIntegral_const, measureReal_def,
    gaussianReal_one_Iio, setIntegral_exp_tilt_Iio, smul_eq_mul, sub_zero, mul_comm]

private lemma cloneFn_inv (hσ : 0 < σ) (hp : 0 < p) : cloneFn p σ⁻¹ = cloneCost σ p := by
  have h : ∀ z, max (p - Real.exp (σ⁻¹ * z - σ⁻¹ ^ 2 / 2)) 0 =
      p * max (1 - p⁻¹ * Real.exp (z / σ - 1 / (2 * σ ^ 2))) 0 := by
    intro z
    rw [mul_max_of_nonneg _ _ hp.le, mul_zero, mul_sub, mul_one, ← mul_assoc,
      mul_inv_cancel₀ hp.ne', one_mul, lr_eq_tilt hσ.ne']
  simp_rw [cloneFn, h]
  rw [integral_const_mul, integral_one_sub_mul_lr_pos hσ (inv_pos.2 hp), gaussProfile,
    cloneCost, Real.exp_log (inv_pos.2 hp), one_div p, mul_sub, ← mul_assoc,
    mul_inv_cancel₀ hp.ne', one_mul]

private lemma cloneFn_neg (p a : ℝ) : cloneFn p (-a) = cloneFn p a := by
  have h := gaussianReal_map_neg (μ := 0) (v := 1)
  rw [neg_zero] at h
  rw [cloneFn, cloneFn]
  conv_rhs => rw [← h, integral_map (by fun_prop) (by fun_prop)]
  congr 1
  ext z
  ring_nf

private lemma cloneFn_zero_le (p : ℝ) {b : ℝ} : cloneFn p 0 ≤ cloneFn p b := by
  have h0 : cloneFn p 0 = max (p - 1) 0 := by
    simp [cloneFn]
  have h1 : p - 1 ≤ cloneFn p b := by
    calc p - 1 = ∫ z, (p - Real.exp (b * z - b ^ 2 / 2)) ∂gaussianReal 0 1 := by
          rw [integral_sub (integrable_const p) (integrable_exp_tilt b), integral_exp_tilt]
          simp
      _ ≤ cloneFn p b :=
          integral_mono (integrable_p_sub_tilt p b) (integrable_p_sub_tilt p b).pos_part
            fun _ => le_max_left _ _
  rw [h0]
  exact max_le h1 (cloneFn_nonneg p b)

private lemma cloneFn_mono (hp : 0 < p) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    cloneFn p a ≤ cloneFn p b := by
  set r := (Real.log p + a ^ 2 / 2) / a with hr
  have hthr : ∀ z, Real.exp (a * z - a ^ 2 / 2) = p * Real.exp (a * (z - r)) := by
    intro z
    have : a * z - a ^ 2 / 2 = Real.log p + a * (z - r) := by
      rw [hr]
      field_simp
      ring
    rw [this, Real.exp_add, Real.exp_log hp]
  have hval : cloneFn p a = p * Phi r - Phi (r - a) := by
    rw [cloneFn, integral_max_zero_eq_setIntegral measurableSet_Iio, setIntegral_Iio_p_sub_tilt]
    · intro z hz
      rw [hthr, sub_nonneg]
      refine mul_le_of_le_one_right hp.le (Real.exp_le_one_iff.2 ?_)
      exact mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.2 (le_of_lt hz))
    · intro z hz
      rw [hthr, sub_nonpos]
      refine le_mul_of_one_le_right hp.le (Real.one_le_exp ?_)
      exact mul_nonneg ha.le (sub_nonneg.2 (not_lt.1 hz))
  have hPhi : Phi (r - b) ≤ Phi (r - a) := monotone_cdf _ (by linarith)
  calc cloneFn p a = p * Phi r - Phi (r - a) := hval
    _ ≤ p * Phi r - Phi (r - b) := by linarith
    _ = ∫ z in Iio r, (p - Real.exp (b * z - b ^ 2 / 2)) ∂gaussianReal 0 1 :=
        (setIntegral_Iio_p_sub_tilt p b r).symm
    _ ≤ cloneFn p b := setIntegral_le_integral_max_zero (integrable_p_sub_tilt p b) _

private lemma cloneFn_le (hp : 0 < p) {a b : ℝ} (hab : |a| ≤ b) : cloneFn p a ≤ cloneFn p b := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [← cloneFn_neg]
    exact cloneFn_mono hp (neg_pos.2 ha) (by rwa [abs_of_neg ha] at hab)
  · rw [ha]
    exact cloneFn_zero_le p
  · exact cloneFn_mono hp ha (by rwa [abs_of_pos ha] at hab)

private lemma coe_toNNReal_sq (σ : ℝ) : ((σ ^ 2).toNNReal : ℝ) = σ ^ 2 :=
  Real.coe_toNNReal _ (sq_nonneg σ)

/-- The scalar clone integral `∫ (p φ_{0,σ²} - φ_{s,σ²})_+ dx` equals `Λ_p(s/σ)`. -/
private lemma integral_clone_eq_cloneFn (hσ : 0 < σ) (p s : ℝ) :
    ∫ x, max (p * gaussianPDFReal 0 (σ ^ 2).toNNReal x - gaussianPDFReal s (σ ^ 2).toNNReal x) 0 =
      cloneFn p (s / σ) := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by simp [hσ.ne']
  have h : ∀ x, max (p * gaussianPDFReal 0 (σ ^ 2).toNNReal x -
        gaussianPDFReal s (σ ^ 2).toNNReal x) 0 =
      gaussianPDFReal 0 (σ ^ 2).toNNReal x •
        max (p - Real.exp ((s * x - s ^ 2 / 2) / σ ^ 2)) 0 := by
    intro x
    rw [gaussianPDFReal_tilt s, coe_toNNReal_sq, smul_eq_mul,
      mul_max_of_nonneg _ _ (gaussianPDFReal_nonneg _ _ _), mul_zero, mul_sub, mul_comm p]
  simp_rw [h]
  rw [← integral_gaussianReal_eq_integral_smul hv, gaussianReal_sq_eq_map hσ.ne', zero_div,
    integral_map (by fun_prop) (by fun_prop), cloneFn]
  congr 1
  ext z
  congr 3
  field_simp

/-- Equation `eq:gamma`: for a unit scalar displacement the clone integral equals
`γ_σ(p)`, `∫ (p φ_{0,σ²} - φ_{1,σ²})_+ dx = γ_σ(p)`. -/
theorem integral_clone_eq_cloneCost (hσ : 0 < σ) (hp : 0 < p) :
    ∫ x, max (p * gaussianPDFReal 0 (σ ^ 2).toNNReal x - gaussianPDFReal 1 (σ ^ 2).toNNReal x) 0 =
      cloneCost σ p := by
  rw [integral_clone_eq_cloneFn hσ, one_div, cloneFn_inv hσ hp]

lemma cloneCost_nonneg (hσ : 0 < σ) (hp : 0 < p) : 0 ≤ cloneCost σ p := by
  rw [← cloneFn_inv hσ hp]
  exact cloneFn_nonneg _ _

/-- Scalar displacements of size at most one cost at most `γ_σ(p)` (`lem:clone`). -/
theorem integral_clone_le_cloneCost (hσ : 0 < σ) (hp : 0 < p) {s : ℝ} (hs : |s| ≤ 1) :
    ∫ x, max (p * gaussianPDFReal 0 (σ ^ 2).toNNReal x - gaussianPDFReal s (σ ^ 2).toNNReal x) 0 ≤
      cloneCost σ p := by
  rw [integral_clone_eq_cloneFn hσ, ← cloneFn_inv hσ hp]
  refine cloneFn_le hp ?_
  rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ, inv_mul_cancel₀ hσ.ne']
  exact hs

/-! #### Displacements in `ℝ^d` -/

variable {ι : Type*} [Fintype ι]

/-- The product of the one-dimensional laws `N(m_i, v)` has density
`y ↦ ∏ i, φ_{m_i,v}(y_i)` with respect to Lebesgue measure on `ι → ℝ`. -/
lemma pi_gaussianReal_eq_withDensity (m : ι → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) v) =
      volume.withDensity (fun y : ι → ℝ => ∏ i, gaussianPDF (m i) v (y i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  have h : ∀ y : ι → ℝ, ∏ i, gaussianPDF (m i) v (y i) =
      ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (y i)) := fun y =>
    (ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg (m i) v (y i)).symm
  simp_rw [h]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (Integrable.fintype_prod fun i => (integrable_gaussianPDFReal (m i) v).restrict)
      (ae_of_all _ fun y => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg (m i) v (y i)),
    integral_fintype_prod_eq_prod (fun i => gaussianPDFReal (m i) v),
    ENNReal.ofReal_prod_of_nonneg fun i _ =>
      integral_nonneg fun x => gaussianPDFReal_nonneg (m i) v x]
  exact Finset.prod_congr rfl fun i _ => (gaussianReal_apply_eq_integral (m i) hv (s i)).symm

private lemma prod_gaussianPDFReal_tilt (v : ℝ≥0) (u x : EuclideanSpace ℝ ι) :
    ∏ i, gaussianPDFReal (u i) v (x i) =
      (∏ i, gaussianPDFReal 0 v (x i)) * Real.exp ((inner ℝ u x - ‖u‖ ^ 2 / 2) / v) := by
  rw [Finset.prod_congr rfl fun i _ => gaussianPDFReal_tilt (u i) v (x i),
    Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.sum_div, EuclideanSpace.real_norm_sq_eq]
  simp [PiLp.inner_apply, mul_comm]

/-- Law of `x ↦ ⟪u, x⟫` under the standard Gaussian measure on `ℝ^d`. -/
private lemma stdGaussian_map_inner (u : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => inner ℝ u x) =
      gaussianReal 0 (‖u‖ ^ 2).toNNReal := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (EuclideanSpace ℝ ι)) (innerSL ℝ u)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  simpa using h

/-- The `d`-dimensional clone integral is the scalar one at displacement `‖u‖`. -/
private lemma integral_clone_euclidean_eq (hσ : 0 < σ) (p : ℝ) (u : EuclideanSpace ℝ ι) :
    ∫ x : EuclideanSpace ℝ ι, max (p * ∏ i, gaussianPDFReal 0 (σ ^ 2).toNNReal (x i) -
        ∏ i, gaussianPDFReal (u i) (σ ^ 2).toNNReal (x i)) 0 = cloneFn p (‖u‖ / σ) := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by simp [hσ.ne']
  set ψ : ℝ → ℝ := fun w => max (p - Real.exp ((w - ‖u‖ ^ 2 / 2) / σ ^ 2)) 0 with hψ
  have h1 : ∀ x : EuclideanSpace ℝ ι, max (p * ∏ i, gaussianPDFReal 0 (σ ^ 2).toNNReal (x i) -
        ∏ i, gaussianPDFReal (u i) (σ ^ 2).toNNReal (x i)) 0 =
      (∏ i, gaussianPDFReal 0 (σ ^ 2).toNNReal (x i)) * ψ (inner ℝ u x) := by
    intro x
    rw [prod_gaussianPDFReal_tilt, coe_toNNReal_sq, hψ, mul_max_of_nonneg _ _
      (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _), mul_zero, mul_sub,
      mul_comm p]
  simp_rw [h1]
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  -- Pass to the product Gaussian law on `ι → ℝ`.
  have h2 : ∫ y : ι → ℝ, (∏ i, gaussianPDFReal 0 (σ ^ 2).toNNReal ((WithLp.toLp 2 y) i)) *
        ψ (inner ℝ u (WithLp.toLp 2 y)) =
      ∫ y, ψ (inner ℝ u (WithLp.toLp 2 y))
        ∂Measure.pi (fun _ : ι => gaussianReal 0 (σ ^ 2).toNNReal) := by
    rw [pi_gaussianReal_eq_withDensity (fun _ => 0) hv,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (ae_of_all _ fun y => ENNReal.prod_lt_top fun i _ => gaussianPDF_lt_top)]
    congr 1
    ext y
    rw [ENNReal.toReal_prod, smul_eq_mul]
    simp [toReal_gaussianPDF]
  rw [h2]
  -- Scale to the standard Gaussian measure on `ℝ^d`.
  have h3 : Measure.pi (fun _ : ι => gaussianReal 0 (σ ^ 2).toNNReal) =
      (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun y i => σ * y i) := by
    rw [Measure.pi_map_pi fun _ => (measurable_const_mul σ).aemeasurable]
    congr 1
    ext1 i
    rw [gaussianReal_sq_eq_map hσ.ne', zero_div]
  have hψm : Measurable ψ := by fun_prop
  have hscale : Measurable (fun (y : ι → ℝ) (i : ι) => σ * y i) := by fun_prop
  rw [h3, integral_map hscale.aemeasurable (by fun_prop)]
  have h4 : ∀ y : ι → ℝ, ψ (inner ℝ u (WithLp.toLp 2 fun i => σ * y i)) =
      ψ (σ * inner ℝ u (WithLp.toLp 2 y)) := by
    intro y
    congr 1
    rw [← inner_smul_right]
    rfl
  simp_rw [h4]
  have h5 : ∫ y, ψ (σ * inner ℝ u (WithLp.toLp 2 y)) ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      ∫ x, ψ (σ * inner ℝ u x) ∂stdGaussian (EuclideanSpace ℝ ι) := by
    rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  have h6 : ∫ x, ψ (σ * inner ℝ u x) ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ w, ψ (σ * w) ∂gaussianReal 0 (‖u‖ ^ 2).toNNReal := by
    rw [← stdGaussian_map_inner u, integral_map (by fun_prop) (by fun_prop)]
  have h7 : gaussianReal 0 (‖u‖ ^ 2).toNNReal = (gaussianReal 0 1).map (‖u‖ * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  rw [h5, h6, h7, integral_map (by fun_prop) (by fun_prop), cloneFn]
  congr 1
  ext z
  rw [hψ]
  field_simp

/-- `lem:clone` (proof): for `‖u‖ ≤ 1`, the clone integral of `N(u, σ² I_d)` against
`p N(0, σ² I_d)` is at most `γ_σ(p)`. The densities are products of one-dimensional ones and
the integral is against Lebesgue measure on `EuclideanSpace ℝ ι`. -/
theorem integral_clone_euclidean_le_cloneCost (hσ : 0 < σ) (hp : 0 < p)
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ 1) :
    ∫ x : EuclideanSpace ℝ ι, max (p * ∏ i, gaussianPDFReal 0 (σ ^ 2).toNNReal (x i) -
        ∏ i, gaussianPDFReal (u i) (σ ^ 2).toNNReal (x i)) 0 ≤ cloneCost σ p := by
  rw [integral_clone_euclidean_eq hσ, ← cloneFn_inv hσ hp]
  refine cloneFn_le hp ?_
  rw [abs_div, abs_of_pos hσ, abs_norm, div_le_iff₀ hσ, inv_mul_cancel₀ hσ.ne']
  exact hu

end Clone

/-! ### Tail correction of the finite upper law -/

section Tail

variable {σ : ℝ}

/-- The truncated likelihood ratio of `app:certificate`, as a function of the normal input `z`:
`Y = X` on `[-10, 10]`, `Y = 0` for `z < -10` and `Y = c` for `z > 10`. -/
noncomputable def truncLR (σ c z : ℝ) : ℝ :=
  if z < -10 then 0 else if z ≤ 10 then Real.exp (z / σ - 1 / (2 * σ ^ 2)) else c

private lemma lr_sub_truncLR (σ c z : ℝ) :
    Real.exp (z / σ - 1 / (2 * σ ^ 2)) - truncLR σ c z =
      (Iio (-10)).indicator (fun z => Real.exp (z / σ - 1 / (2 * σ ^ 2))) z +
        (Ioi 10).indicator (fun z => Real.exp (z / σ - 1 / (2 * σ ^ 2)) - c) z := by
  unfold truncLR
  by_cases h1 : z < -10
  · have h2 : z ∉ Ioi (10 : ℝ) := by
      simp only [mem_Ioi, not_lt]
      linarith
    simp [h1, h2]
  · by_cases h2 : z ≤ 10
    · simp [h1, h2]
    · have h3 : z ∈ Ioi (10 : ℝ) := lt_of_not_ge h2
      simp [h1, h2, h3]

/-- Equation `eq:tau`: `E(X - Y) = Φ(-10 - 1/σ) + Φ(1/σ - 10) - c Φ(-10)`, for every
constant `c`. -/
theorem integral_lr_sub_truncLR (hσ : 0 < σ) (c : ℝ) :
    ∫ z, (Real.exp (z / σ - 1 / (2 * σ ^ 2)) - truncLR σ c z) ∂gaussianReal 0 1 =
      Phi (-10 - 1 / σ) + Phi (1 / σ - 10) - c * Phi (-10) := by
  have hX := integrable_lr hσ.ne'
  have hXc : Integrable (fun z => Real.exp (z / σ - 1 / (2 * σ ^ 2)) - c) (gaussianReal 0 1) :=
    hX.sub (integrable_const c)
  simp_rw [lr_sub_truncLR]
  rw [integral_add (hX.indicator measurableSet_Iio) (hXc.indicator measurableSet_Ioi),
    integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioi,
    integral_sub hX.integrableOn integrableOn_const, setIntegral_const, measureReal_def,
    gaussianReal_one_Ioi, smul_eq_mul]
  simp_rw [lr_eq_tilt hσ.ne']
  rw [setIntegral_exp_tilt_Iio, setIntegral_exp_tilt_Ioi, one_div, zero_sub]
  ring

/-- `Y ≤ X` pointwise as soon as `c ≤ X(10) = exp(10/σ - 1/(2σ²))`. -/
theorem truncLR_le (hσ : 0 < σ) {c : ℝ} (hc : c ≤ Real.exp (10 / σ - 1 / (2 * σ ^ 2))) (z : ℝ) :
    truncLR σ c z ≤ Real.exp (z / σ - 1 / (2 * σ ^ 2)) := by
  unfold truncLR
  split_ifs with h1 h2
  · exact (Real.exp_pos _).le
  · exact le_rfl
  · refine hc.trans (Real.exp_le_exp.2 ?_)
    have : 10 / σ ≤ z / σ := div_le_div_of_nonneg_right (le_of_lt (not_le.1 h2)) hσ.le
    linarith

end Tail

/-! ### Candidate counts (`prop:counts`) -/

section Counts

/-- Law of the likelihood ratio `X = exp(Z/σ - 1/(2σ²))` with `Z ~ N(0,1)`. -/
noncomputable def lrLaw (σ : ℝ) : Measure ℝ :=
  (gaussianReal 0 1).map (fun z => Real.exp (z / σ - 1 / (2 * σ ^ 2)))

instance (σ : ℝ) : IsProbabilityMeasure (lrLaw σ) := by
  unfold lrLaw
  infer_instance

lemma integrable_id_lrLaw {σ : ℝ} (hσ : σ ≠ 0) : Integrable id (lrLaw σ) := by
  rw [lrLaw, integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  exact integrable_lr hσ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `X 0, X 1, …` are independent random variables, each with the law of
`exp(Z/σ - 1/(2σ²))`, `Z ~ N(0,1)`. The paper's `X_i` is `X (i - 1)`. -/
structure IsLRSequence (P : Measure Ω) (σ : ℝ) (X : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  indep : iIndepFun X P
  law : ∀ i, P.map (X i) = lrLaw σ

/-- `S_m = X 0 + ⋯ + X (m - 1)`. -/
def partialSum (X : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range m, X i ω

/-- `F_m(t) = E(S_m - t)_+`. -/
noncomputable def callF (P : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, max (partialSum X m ω - t) 0 ∂P

/-- `J_m(t) = E(t - S_m)_+`. -/
noncomputable def putJ (P : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, max (t - partialSum X m ω) 0 ∂P

/-- The coordinates under the infinite product of copies of `lrLaw σ` satisfy
`IsLRSequence`, so the hypothesis is consistent. -/
lemma isLRSequence_infinitePi (σ : ℝ) :
    IsLRSequence (Measure.infinitePi fun _ : ℕ => lrLaw σ) σ (fun i ω => ω i) where
  measurable i := measurable_pi_apply i
  indep := iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  law i := Measure.infinitePi_map_eval _ i

variable {P : Measure Ω} {σ : ℝ} {X : ℕ → Ω → ℝ}

namespace IsLRSequence

lemma integrable (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) (i : ℕ) : Integrable (X i) P := by
  have h := integrable_id_lrLaw hσ
  rwa [← hX.law i, integrable_map_measure aestronglyMeasurable_id
    (hX.measurable i).aemeasurable] at h

lemma measurable_partialSum (hX : IsLRSequence P σ X) (m : ℕ) : Measurable (partialSum X m) :=
  Finset.measurable_fun_sum _ fun i _ => hX.measurable i

lemma integrable_partialSum (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) (m : ℕ) :
    Integrable (partialSum X m) P :=
  integrable_finsetSum _ fun i _ => hX.integrable hσ i

lemma indepFun_partialSum (hX : IsLRSequence P σ X) (m : ℕ) :
    IndepFun (partialSum X m) (X m) P := by
  have h := hX.indep.indepFun_finsetSum_of_notMem hX.measurable (s := Finset.range m) (i := m)
    (by simp)
  convert h using 1
  ext ω
  simp [partialSum]

lemma integral_comp (hX : IsLRSequence P σ X) (i : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ ω, f (X i ω) ∂P = ∫ z, f (Real.exp (z / σ - 1 / (2 * σ ^ 2))) ∂gaussianReal 0 1 := by
  rw [← integral_map (hX.measurable i).aemeasurable hf.aestronglyMeasurable, hX.law i, lrLaw,
    integral_map (by fun_prop) hf.aestronglyMeasurable]

end IsLRSequence

private lemma integrable_id_map {Y : Ω → ℝ} (hY : Measurable Y) (hYi : Integrable Y P) :
    Integrable (fun y : ℝ => y) (P.map Y) :=
  (integrable_map_measure (g := fun y : ℝ => y) (by fun_prop) hY.aemeasurable).2 hYi

variable [IsProbabilityMeasure P]

/-- Expectation of `g(S, Y)` for independent real `S, Y`, integrating `S` first. -/
private lemma integral_indep_eq {S Y : Ω → ℝ} (hS : Measurable S) (hY : Measurable Y)
    (hSY : IndepFun S Y P) {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (hgi : Integrable g ((P.map S).prod (P.map Y))) :
    ∫ ω, g (S ω, Y ω) ∂P = ∫ y, ∫ ω, g (S ω, y) ∂P ∂(P.map Y) := by
  rw [← integral_map (φ := fun ω => (S ω, Y ω)) (f := g) (hS.prodMk hY).aemeasurable
      hg.aestronglyMeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable hY.aemeasurable).1 hSY,
    integral_prod_symm g hgi]
  congr 1
  ext y
  exact integral_map hS.aemeasurable
    (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable

/-- Recurrence `eq:recurrences` for `F_m`: `F_{m+1}(t) = E F_m(t - X)`. -/
theorem callF_succ (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) (m : ℕ) (t : ℝ) :
    callF P X (m + 1) t = ∫ x, callF P X m (t - x) ∂lrLaw σ := by
  have hS := hX.measurable_partialSum m
  have hSi := integrable_id_map hS (hX.integrable_partialSum hσ m)
  have hYi := integrable_id_map (hX.measurable m) (hX.integrable hσ m)
  have hgi : Integrable (fun q : ℝ × ℝ => max (q.1 + q.2 - t) 0)
      ((P.map (partialSum X m)).prod (P.map (X m))) :=
    (((hSi.comp_fst _).add (hYi.comp_snd _)).sub (integrable_const t)).pos_part
  have h := integral_indep_eq hS (hX.measurable m) (hX.indepFun_partialSum m) (by fun_prop) hgi
  simp only at h
  rw [hX.law m] at h
  have hsum : ∀ ω, partialSum X (m + 1) ω = partialSum X m ω + X m ω := fun ω =>
    Finset.sum_range_succ _ _
  simp_rw [callF, hsum, h]
  congr 1
  ext x
  congr 1
  ext ω
  ring_nf

/-- Recurrence `eq:recurrences` for `J_m`: `J_{m+1}(t) = E J_m(t - X)`. -/
theorem putJ_succ (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) (m : ℕ) (t : ℝ) :
    putJ P X (m + 1) t = ∫ x, putJ P X m (t - x) ∂lrLaw σ := by
  have hS := hX.measurable_partialSum m
  have hSi := integrable_id_map hS (hX.integrable_partialSum hσ m)
  have hYi := integrable_id_map (hX.measurable m) (hX.integrable hσ m)
  have hgi : Integrable (fun q : ℝ × ℝ => max (t - (q.1 + q.2)) 0)
      ((P.map (partialSum X m)).prod (P.map (X m))) :=
    ((integrable_const t).sub ((hSi.comp_fst _).add (hYi.comp_snd _))).pos_part
  have h := integral_indep_eq hS (hX.measurable m) (hX.indepFun_partialSum m) (by fun_prop) hgi
  simp only at h
  rw [hX.law m] at h
  have hsum : ∀ ω, partialSum X (m + 1) ω = partialSum X m ω + X m ω := fun ω =>
    Finset.sum_range_succ _ _
  simp_rw [putJ, hsum, h]
  congr 1
  ext x
  congr 1
  ext ω
  ring_nf

/-- Initial condition of `eq:recurrences`: `F_0(t) = (-t)_+`. -/
theorem callF_zero (t : ℝ) : callF P X 0 t = max (-t) 0 := by
  simp [callF, partialSum]

/-- Initial condition of `eq:recurrences`: `J_0(t) = t_+`. -/
theorem putJ_zero (t : ℝ) : putJ P X 0 t = max t 0 := by
  simp [putJ, partialSum]

private lemma max_convex_combo {a b u w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a * u + b * w) 0 ≤ a * max u 0 + b * max w 0 :=
  max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
    (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))

/-- `F_m` is convex. -/
theorem convexOn_callF (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) (m : ℕ) :
    ConvexOn ℝ univ (callF P X m) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hi : ∀ t, Integrable (fun ω => max (partialSum X m ω - t) 0) P := fun t =>
    ((hX.integrable_partialSum hσ m).sub (integrable_const t)).pos_part
  simp only [smul_eq_mul, callF]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi x).const_mul a) ((hi y).const_mul b)]
  refine integral_mono (hi _) (((hi x).const_mul a).add ((hi y).const_mul b)) fun ω => ?_
  have h : partialSum X m ω - (a * x + b * y) =
      a * (partialSum X m ω - x) + b * (partialSum X m ω - y) := by
    linear_combination (-partialSum X m ω) * hab
  simp only [h]
  exact max_convex_combo ha hb

/-- `J_m` is convex. -/
theorem convexOn_putJ (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) (m : ℕ) :
    ConvexOn ℝ univ (putJ P X m) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hi : ∀ t, Integrable (fun ω => max (t - partialSum X m ω) 0) P := fun t =>
    ((integrable_const t).sub (hX.integrable_partialSum hσ m)).pos_part
  simp only [smul_eq_mul, putJ]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi x).const_mul a) ((hi y).const_mul b)]
  refine integral_mono (hi _) (((hi x).const_mul a).add ((hi y).const_mul b)) fun ω => ?_
  have h : a * x + b * y - partialSum X m ω =
      a * (x - partialSum X m ω) + b * (y - partialSum X m ω) := by
    linear_combination partialSum X m ω * hab
  simp only [h]
  exact max_convex_combo ha hb

omit [IsProbabilityMeasure P] in
/-- Conditioning on `K = m` in the forward direction: `E(L_m - k)_+ = F_m(mk)/m`. -/
theorem integral_avg_sub_pos {m : ℕ} (hm : 1 ≤ m) (k : ℝ) :
    ∫ ω, max (partialSum X m ω / m - k) 0 ∂P = callF P X m (m * k) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [callF, ← integral_div]
  congr 1
  ext ω
  rw [← max_div_div_right hm'.le, zero_div, sub_div, mul_div_cancel_left₀ _ hm'.ne']

omit [IsProbabilityMeasure P] in
/-- Conditioning on `K = m` in the reverse direction: `E(1 - k L_m)_+ = k J_m(m/k)/m`. -/
theorem integral_one_sub_avg_pos {m : ℕ} (hm : 1 ≤ m) {k : ℝ} (hk : 0 < k) :
    ∫ ω, max (1 - k * (partialSum X m ω / m)) 0 ∂P = k * putJ P X m (m / k) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [show k * putJ P X m (m / k) / m = k / m * putJ P X m (m / k) by ring, putJ,
    ← integral_const_mul]
  congr 1
  ext ω
  rw [mul_max_of_nonneg _ _ (div_nonneg hk.le hm'.le), mul_zero]
  congr 1
  field_simp

/-- For every count `m ≥ 1`, `E(L_m - k)_+ ≤ g_σ(log k)`. -/
theorem integral_avg_sub_pos_le (hX : IsLRSequence P σ X) (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m)
    {k : ℝ} (hk : 0 < k) :
    ∫ ω, max (partialSum X m ω / m - k) 0 ∂P ≤ gaussProfile σ (Real.log k) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : ∀ i, Integrable (fun ω => max (X i ω - k) 0) P := fun i =>
    ((hX.integrable hσ.ne' i).sub (integrable_const k)).pos_part
  have hcall : ∀ i, ∫ ω, max (X i ω - k) 0 ∂P = gaussProfile σ (Real.log k) := fun i => by
    rw [hX.integral_comp i (f := fun x => max (x - k) 0) (by fun_prop),
      integral_lr_sub_pos hσ hk]
  have hpt : ∀ ω, max (partialSum X m ω / m - k) 0 ≤
      (∑ i ∈ Finset.range m, max (X i ω - k) 0) / m := by
    intro ω
    have hrepr : partialSum X m ω / m - k = (∑ i ∈ Finset.range m, (X i ω - k)) / m := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, partialSum]
      field_simp
    rw [hrepr]
    exact max_le (div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => le_max_left _ _) hm'.le)
      (div_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _) hm'.le)
  calc ∫ ω, max (partialSum X m ω / m - k) 0 ∂P
      ≤ ∫ ω, (∑ i ∈ Finset.range m, max (X i ω - k) 0) / m ∂P :=
        integral_mono (((hX.integrable_partialSum hσ.ne' m).div_const _).sub
          (integrable_const k)).pos_part
          ((integrable_finsetSum _ fun i _ => hi i).div_const _) hpt
    _ = (∑ i ∈ Finset.range m, ∫ ω, max (X i ω - k) 0 ∂P) / m := by
        rw [integral_div, integral_finsetSum _ fun i _ => hi i]
    _ = gaussProfile σ (Real.log k) := by
        simp_rw [hcall]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- For every count `m ≥ 1`, `E(1 - k L_m)_+ ≤ g_σ(log k)`. -/
theorem integral_one_sub_avg_pos_le (hX : IsLRSequence P σ X) (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m)
    {k : ℝ} (hk : 0 < k) :
    ∫ ω, max (1 - k * (partialSum X m ω / m)) 0 ∂P ≤ gaussProfile σ (Real.log k) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : ∀ i, Integrable (fun ω => max (1 - k * X i ω) 0) P := fun i =>
    ((integrable_const 1).sub ((hX.integrable hσ.ne' i).const_mul k)).pos_part
  have hput : ∀ i, ∫ ω, max (1 - k * X i ω) 0 ∂P = gaussProfile σ (Real.log k) := fun i => by
    rw [hX.integral_comp i (f := fun x => max (1 - k * x) 0) (by fun_prop),
      integral_one_sub_mul_lr_pos hσ hk]
  have hpt : ∀ ω, max (1 - k * (partialSum X m ω / m)) 0 ≤
      (∑ i ∈ Finset.range m, max (1 - k * X i ω) 0) / m := by
    intro ω
    have hrepr : 1 - k * (partialSum X m ω / m) =
        (∑ i ∈ Finset.range m, (1 - k * X i ω)) / m := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, partialSum]
      field_simp
    rw [hrepr]
    exact max_le (div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => le_max_left _ _) hm'.le)
      (div_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _) hm'.le)
  calc ∫ ω, max (1 - k * (partialSum X m ω / m)) 0 ∂P
      ≤ ∫ ω, (∑ i ∈ Finset.range m, max (1 - k * X i ω) 0) / m ∂P :=
        integral_mono ((integrable_const 1).sub
          (((hX.integrable_partialSum hσ.ne' m).div_const _).const_mul k)).pos_part
          ((integrable_finsetSum _ fun i _ => hi i).div_const _) hpt
    _ = (∑ i ∈ Finset.range m, ∫ ω, max (1 - k * X i ω) 0 ∂P) / m := by
        rw [integral_div, integral_finsetSum _ fun i _ => hi i]
    _ = gaussProfile σ (Real.log k) := by
        simp_rw [hput]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

omit [IsProbabilityMeasure P] in
/-- Averaging over an independent count `K` with values in `{1, …, T}`. -/
theorem integral_mixture {K : Ω → ℕ} (hKm : Measurable K) {T : ℕ}
    (hKT : ∀ᵐ ω ∂P, K ω ∈ Finset.Icc 1 T) {V : Ω → ℕ → ℝ} (hV : Measurable V)
    (hKV : IndepFun K V P) (G : ℕ → (ℕ → ℝ) → ℝ) (hG : ∀ m, Measurable (G m))
    (hGi : ∀ m, Integrable (fun ω => G m (V ω)) P) :
    ∫ ω, G (K ω) (V ω) ∂P =
      ∑ m ∈ Finset.Icc 1 T, (P {ω | K ω = m}).toReal * ∫ ω, G m (V ω) ∂P := by
  set ind : ℕ → ℕ → ℝ := fun m n => ({m} : Set ℕ).indicator (fun _ => (1 : ℝ)) n with hind
  have hpt : (fun ω => G (K ω) (V ω)) =ᵐ[P]
      fun ω => ∑ m ∈ Finset.Icc 1 T, ind m (K ω) * G m (V ω) := by
    filter_upwards [hKT] with ω hω
    rw [Finset.sum_eq_single (K ω)]
    · simp [hind]
    · intro b _ hb
      simp [hind, Set.indicator, Ne.symm hb]
    · intro h
      exact absurd hω h
  have hterm : ∀ m, (fun ω => ind m (K ω) * G m (V ω)) =
      (K ⁻¹' {m}).indicator (fun ω => G m (V ω)) := by
    intro m
    ext ω
    by_cases h : K ω = m <;> simp [hind, Set.indicator, h]
  have hKmeas : ∀ m, MeasurableSet (K ⁻¹' {m}) := fun m => hKm (measurableSet_singleton m)
  rw [integral_congr_ae hpt, integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm1 : Measurable (ind m) := measurable_from_nat
    have hindep := hKV.comp hm1 (hG m)
    have h := hindep.integral_fun_mul_eq_mul_integral (hm1.comp hKm).aestronglyMeasurable
      ((hG m).comp hV).aestronglyMeasurable
    simp only [Function.comp_apply] at h
    rw [h]
    congr 1
    have h1 : (fun ω => ind m (K ω)) = (K ⁻¹' {m}).indicator 1 := by
      ext ω
      by_cases h : K ω = m <;> simp [hind, Set.indicator, h]
    rw [h1, integral_indicator_one (hKmeas m), measureReal_def]
    rfl
  · intro m _
    rw [hterm m]
    exact (hGi m).indicator (hKmeas m)

/-- The weights `w_m = P(K = m)` sum to one over `{1, …, T}`. -/
lemma sum_prob_eq_one {K : Ω → ℕ} (hKm : Measurable K) {T : ℕ}
    (hKT : ∀ᵐ ω ∂P, K ω ∈ Finset.Icc 1 T) :
    ∑ m ∈ Finset.Icc 1 T, (P {ω | K ω = m}).toReal = 1 := by
  have h := integral_mixture (P := P) hKm hKT (V := fun _ => 0) measurable_const
    (indepFun_const_right K _) (fun _ _ => 1) (fun _ => measurable_const)
    (fun _ => integrable_const 1)
  simpa using h.symm

/-- Finite-sum step in `prop:counts`. -/
private lemma sum_mul_le_of_le {T M : ℕ} (hMT : M ≤ T) (w e c : ℕ → ℝ) (g : ℝ)
    (hw0 : ∀ m, 0 ≤ w m) (hw1 : ∑ m ∈ Finset.Icc 1 T, w m = 1)
    (hc : ∀ m ∈ Finset.Icc 1 M, e m ≤ c m) (hg : ∀ m ∈ Finset.Icc 1 T, e m ≤ g) :
    ∑ m ∈ Finset.Icc 1 T, w m * e m ≤
      ∑ m ∈ Finset.Icc 1 M, w m * c m + (1 - ∑ m ∈ Finset.Icc 1 M, w m) * g := by
  have hsplit : ∀ f : ℕ → ℝ, ∑ m ∈ Finset.Icc 1 T, f m =
      ∑ m ∈ Finset.Icc 1 M, f m + ∑ m ∈ Finset.Ioc M T, f m := by
    intro f
    rw [← zero_add 1, Finset.Icc_add_one_left_eq_Ioc, Finset.Icc_add_one_left_eq_Ioc,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMT]
  have hrest : ∑ m ∈ Finset.Ioc M T, w m = 1 - ∑ m ∈ Finset.Icc 1 M, w m := by
    rw [← hw1, hsplit w]
    ring
  have hIoc : ∀ m ∈ Finset.Ioc M T, m ∈ Finset.Icc 1 T := fun m hm => by
    simp only [Finset.mem_Ioc] at hm
    simp only [Finset.mem_Icc]
    omega
  rw [hsplit, ← hrest, Finset.sum_mul]
  exact add_le_add
    (Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hc m hm) (hw0 m))
    (Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hg m (hIoc m hm)) (hw0 m))

omit [IsProbabilityMeasure P] in
private lemma measurable_vec (hX : IsLRSequence P σ X) : Measurable fun ω (i : ℕ) => X i ω :=
  measurable_pi_iff.2 hX.measurable

/-- `E(L_K - k)_+ = Σ_m P(K = m) E(L_m - k)_+` for a count `K` independent of the `X`'s. -/
theorem integral_avgK_sub_pos (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) {K : Ω → ℕ}
    (hKm : Measurable K) {T : ℕ} (hKT : ∀ᵐ ω ∂P, K ω ∈ Finset.Icc 1 T)
    (hKX : IndepFun K (fun ω i => X i ω) P) (k : ℝ) :
    ∫ ω, max (partialSum X (K ω) ω / K ω - k) 0 ∂P =
      ∑ m ∈ Finset.Icc 1 T, (P {ω | K ω = m}).toReal *
        ∫ ω, max (partialSum X m ω / m - k) 0 ∂P :=
  integral_mixture hKm hKT (measurable_vec hX) hKX
    (fun m x => max ((∑ i ∈ Finset.range m, x i) / m - k) 0) (fun m => by fun_prop)
    (fun m => (((hX.integrable_partialSum hσ m).div_const _).sub (integrable_const k)).pos_part)

/-- `E(1 - k L_K)_+ = Σ_m P(K = m) E(1 - k L_m)_+` for a count `K` independent of the `X`'s. -/
theorem integral_one_sub_avgK_pos (hX : IsLRSequence P σ X) (hσ : σ ≠ 0) {K : Ω → ℕ}
    (hKm : Measurable K) {T : ℕ} (hKT : ∀ᵐ ω ∂P, K ω ∈ Finset.Icc 1 T)
    (hKX : IndepFun K (fun ω i => X i ω) P) (k : ℝ) :
    ∫ ω, max (1 - k * (partialSum X (K ω) ω / K ω)) 0 ∂P =
      ∑ m ∈ Finset.Icc 1 T, (P {ω | K ω = m}).toReal *
        ∫ ω, max (1 - k * (partialSum X m ω / m)) 0 ∂P :=
  integral_mixture hKm hKT (measurable_vec hX) hKX
    (fun m x => max (1 - k * ((∑ i ∈ Finset.range m, x i) / m)) 0) (fun m => by fun_prop)
    (fun m => ((integrable_const 1).sub
      (((hX.integrable_partialSum hσ m).div_const _).const_mul k)).pos_part)

/-- Proposition `prop:counts`, forward direction. Let `K` take values in `{1, …, T}`,
independently of the `X`'s, and let `M ≤ T`. If the forward conditional epoch divergence `H`
satisfies the conclusion `eq:clonef` of Lemma `lem:clone`, `H ≤ E(L_K - k)_+ + (1+k)β`, and
`Fbar m ≥ F_m(mk)` for `1 ≤ m ≤ M`, then
`H ≤ Σ_{m=1}^M w_m c_m^+ + (1 - Σ_{m=1}^M w_m) g + (1+k)β` with `w_m = P(K = m)`,
`g = g_σ(log k)` and `c_m^+ = min {g, Fbar m / m}`. -/
theorem counts_bound_forward (hX : IsLRSequence P σ X) (hσ : 0 < σ) {k : ℝ} (hk : 0 < k)
    {K : Ω → ℕ} (hKm : Measurable K) {T : ℕ} (hKT : ∀ᵐ ω ∂P, K ω ∈ Finset.Icc 1 T)
    (hKX : IndepFun K (fun ω i => X i ω) P) {M : ℕ} (hMT : M ≤ T) (Fbar : ℕ → ℝ)
    (hF : ∀ m ∈ Finset.Icc 1 M, callF P X m (m * k) ≤ Fbar m) {H β : ℝ}
    (hH : H ≤ ∫ ω, max (partialSum X (K ω) ω / K ω - k) 0 ∂P + (1 + k) * β) :
    H ≤ ∑ m ∈ Finset.Icc 1 M, (P {ω | K ω = m}).toReal *
          min (gaussProfile σ (Real.log k)) (Fbar m / m) +
        (1 - ∑ m ∈ Finset.Icc 1 M, (P {ω | K ω = m}).toReal) * gaussProfile σ (Real.log k) +
        (1 + k) * β := by
  rw [integral_avgK_sub_pos hX hσ.ne' hKm hKT hKX k] at hH
  refine hH.trans (add_le_add (sum_mul_le_of_le hMT _ _ _ _
    (fun _ => ENNReal.toReal_nonneg) (sum_prob_eq_one hKm hKT) (fun m hm => ?_)
    (fun m hm => ?_)) le_rfl)
  · have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    refine le_min (integral_avg_sub_pos_le hX hσ hm1 hk) ?_
    rw [integral_avg_sub_pos hm1]
    exact div_le_div_of_nonneg_right (hF m hm) hm'.le
  · exact integral_avg_sub_pos_le hX hσ (Finset.mem_Icc.1 hm).1 hk

/-- Proposition `prop:counts`, reverse direction, under the same assumptions on `K` and `M`.
If the reverse conditional epoch divergence `H` satisfies the conclusion `eq:cloner` of Lemma
`lem:clone`, `H ≤ E(1 - k L_K)_+ + (1+k)β`, and `Jbar m ≥ J_m(m/k)` for `1 ≤ m ≤ M`, then
`H ≤ Σ_{m=1}^M w_m c_m^- + (1 - Σ_{m=1}^M w_m) g + (1+k)β` with
`c_m^- = min {g, k Jbar m / m}`. -/
theorem counts_bound_reverse (hX : IsLRSequence P σ X) (hσ : 0 < σ) {k : ℝ} (hk : 0 < k)
    {K : Ω → ℕ} (hKm : Measurable K) {T : ℕ} (hKT : ∀ᵐ ω ∂P, K ω ∈ Finset.Icc 1 T)
    (hKX : IndepFun K (fun ω i => X i ω) P) {M : ℕ} (hMT : M ≤ T) (Jbar : ℕ → ℝ)
    (hJ : ∀ m ∈ Finset.Icc 1 M, putJ P X m (m / k) ≤ Jbar m) {H β : ℝ}
    (hH : H ≤ ∫ ω, max (1 - k * (partialSum X (K ω) ω / K ω)) 0 ∂P + (1 + k) * β) :
    H ≤ ∑ m ∈ Finset.Icc 1 M, (P {ω | K ω = m}).toReal *
          min (gaussProfile σ (Real.log k)) (k * Jbar m / m) +
        (1 - ∑ m ∈ Finset.Icc 1 M, (P {ω | K ω = m}).toReal) * gaussProfile σ (Real.log k) +
        (1 + k) * β := by
  rw [integral_one_sub_avgK_pos hX hσ.ne' hKm hKT hKX k] at hH
  refine hH.trans (add_le_add (sum_mul_le_of_le hMT _ _ _ _
    (fun _ => ENNReal.toReal_nonneg) (sum_prob_eq_one hKm hKT) (fun m hm => ?_)
    (fun m hm => ?_)) le_rfl)
  · have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    refine le_min (integral_one_sub_avg_pos_le hX hσ hm1 hk) ?_
    rw [integral_one_sub_avg_pos hm1 hk]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hJ m hm) hk.le) hm'.le
  · exact integral_one_sub_avg_pos_le hX hσ (Finset.mem_Icc.1 hm).1 hk

end Counts

end Gaussian

end ASGA
