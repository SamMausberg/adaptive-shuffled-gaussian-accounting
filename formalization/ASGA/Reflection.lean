import ASGA.Basic

/-!
# The pair `eq:chua` does not dominate adaptive queries

This file formalizes `app:reflection`. All laws are translated transcript laws, in the coordinates
`y_t = Y_t + b` of `sec:capacity`, on `(Fin n → ℝ) × ℝ`: the first factor holds the `n = T - 1`
prefix rounds and the second the final round. Common items have query value `-1`, the differing
item has value `+1` in the prefix rounds, and the neighboring input replaces it by `0`. The real
and null transcripts then have the densities of `P_S` and `Q_S` in `eq:chua` (`chuaReal`,
`chuaNull`). The adaptive analyst changes the differing item's final value to `-1` exactly on the
prefix region `U - e^ε V > 0` (`switchSet`). This moves the real final-round mean from `2` to `0`
when the differing item is in the final round and leaves the null law unchanged; `adaptReal` is
the resulting real-input law. The passage from batch sums to these densities is a modeling step
and is not formalized.

Main results:
* `forward_step` and `reverse_step`, the one-dimensional strict inequalities on a switching
  prefix, and `s_neg_of_r_pos`;
* `hockeyStick_withDensity`: `H_ε(P, Q) = ∫ (p - e^ε q)₊` for integrable nonnegative densities;
* `isProbabilityMeasure_chuaReal`, `isProbabilityMeasure_chuaNull`,
  `isProbabilityMeasure_adaptReal`;
* `chua_pair_strictly_improvable`: for `T ≥ 2`, `σ > 0` and `ε ≥ 0`,
  `H_ε(P_S, Q_S) < H_ε(P', Q_S)` and `H_ε(Q_S, P_S) < H_ε(Q_S, P')`. The forward inequality holds
  at every real `ε` (`hockeyStick_chua_lt_adapt`).
-/

open MeasureTheory ProbabilityTheory

namespace ASGA

namespace Reflection

/-- Density of `N(μ, σ²)` on `ℝ`. -/
noncomputable def gaussDens (σ μ y : ℝ) : ℝ :=
  gaussianPDFReal μ (σ ^ 2).toNNReal y

section Gaussian

variable {σ : ℝ}

private lemma var_ne_zero (hσ : σ ≠ 0) : (σ ^ 2).toNNReal ≠ 0 :=
  (Real.toNNReal_pos.2 (by positivity)).ne'

lemma gaussDens_pos (hσ : σ ≠ 0) (μ y : ℝ) : 0 < gaussDens σ μ y :=
  gaussianPDFReal_pos _ _ _ (var_ne_zero hσ)

lemma gaussDens_nonneg (μ y : ℝ) : 0 ≤ gaussDens σ μ y :=
  gaussianPDFReal_nonneg _ _ _

lemma integrable_gaussDens (μ : ℝ) : Integrable (gaussDens σ μ) :=
  integrable_gaussianPDFReal _ _

lemma integral_gaussDens (hσ : σ ≠ 0) (μ : ℝ) : ∫ y, gaussDens σ μ y = 1 :=
  integral_gaussianPDFReal_eq_one _ (var_ne_zero hσ)

lemma gaussDens_neg (μ y : ℝ) : gaussDens σ μ (-y) = gaussDens σ (-μ) y := by
  simp only [gaussDens, gaussianPDFReal]
  congr 3
  ring

lemma gaussDens_add (μ y c : ℝ) : gaussDens σ μ (y + c) = gaussDens σ (μ - c) y :=
  gaussianPDFReal_add _ _

/-- `f_μ = f_0 · exp((2μy - μ²)/(2σ²))`. -/
lemma gaussDens_eq_mul_exp (hσ : σ ≠ 0) (μ y : ℝ) :
    gaussDens σ μ y = gaussDens σ 0 y * Real.exp ((2 * μ * y - μ ^ 2) / (2 * σ ^ 2)) := by
  simp only [gaussDens, gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg σ)]
  rw [mul_assoc _ (Real.exp _), ← Real.exp_add]
  congr 2
  field_simp
  ring

lemma gaussDens_one (hσ : σ ≠ 0) (y : ℝ) :
    gaussDens σ 1 y = gaussDens σ 0 y * Real.exp ((2 * y - 1) / (2 * σ ^ 2)) := by
  rw [gaussDens_eq_mul_exp hσ]
  congr 3
  ring

lemma gaussDens_neg_one (hσ : σ ≠ 0) (y : ℝ) :
    gaussDens σ (-1) y = gaussDens σ 0 y * Real.exp ((-2 * y - 1) / (2 * σ ^ 2)) := by
  rw [gaussDens_eq_mul_exp hσ]
  congr 3
  ring

end Gaussian

section OneDim

/-- A strict comparison of integrals from a pointwise inequality that is strict on a set of
positive measure. -/
private lemma integral_lt_integral_of_le_of_measure_ne_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hle : ∀ x, f x ≤ g x) (hlt : μ {x | f x < g x} ≠ 0) :
    ∫ x, f x ∂μ < ∫ x, g x ∂μ := by
  rw [← sub_pos, ← integral_sub hg hf, integral_pos_iff_support_of_nonneg_ae]
  · refine pos_iff_ne_zero.2 (mt (measure_mono_null ?_) hlt)
    intro x hx
    exact (sub_pos.2 hx).ne'
  · exact ae_of_all _ fun x => sub_nonneg.2 (hle x)
  · exact hg.sub hf

/-- If `g = αA + βB` with positive weights summing to one, `∫ B₊ = ∫ A₊`, and `A > 0 > B` on a
set of positive measure, then `∫ g₊ < ∫ A₊`. -/
private lemma integral_max_lt_of_split {A B g : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α + β = 1) (hg : ∀ y, g y = α * A y + β * B y) (hA : Integrable A)
    (hB : Integrable B) (hrefl : ∫ y, max (B y) 0 = ∫ y, max (A y) 0)
    (hS : volume {y | 0 < A y ∧ B y < 0} ≠ 0) :
    ∫ y, max (g y) 0 < ∫ y, max (A y) 0 := by
  have hgi : Integrable g := by
    have : g = fun y => α * A y + β * B y := funext hg
    rw [this]
    exact (hA.const_mul α).add (hB.const_mul β)
  have hRi : Integrable fun y => α * max (A y) 0 + β * max (B y) 0 :=
    (hA.pos_part.const_mul α).add (hB.pos_part.const_mul β)
  have hle : ∀ y, max (g y) 0 ≤ α * max (A y) 0 + β * max (B y) 0 := by
    intro y
    have h1 : α * A y ≤ α * max (A y) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hα.le
    have h2 : β * B y ≤ β * max (B y) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hβ.le
    have h3 : 0 ≤ α * max (A y) 0 := mul_nonneg hα.le (le_max_right _ _)
    have h4 : 0 ≤ β * max (B y) 0 := mul_nonneg hβ.le (le_max_right _ _)
    rw [hg y]
    exact max_le (by linarith) (by linarith)
  have hlt : volume {y | max (g y) 0 < α * max (A y) 0 + β * max (B y) 0} ≠ 0 := by
    refine fun h0 => hS (measure_mono_null ?_ h0)
    rintro y ⟨hAy, hBy⟩
    have hA' : max (A y) 0 = A y := max_eq_left hAy.le
    have hB' : max (B y) 0 = 0 := max_eq_right hBy.le
    simp only [Set.mem_ofPred_eq, hA', hB', mul_zero, add_zero]
    rw [hg y]
    have : β * B y < 0 := mul_neg_of_pos_of_neg hβ hBy
    exact max_lt (by linarith) (mul_pos hα hAy)
  calc ∫ y, max (g y) 0 < ∫ y, (α * max (A y) 0 + β * max (B y) 0) :=
        integral_lt_integral_of_le_of_measure_ne_zero hgi.pos_part hRi hle hlt
    _ = ∫ y, max (A y) 0 := by
        rw [integral_add (hA.pos_part.const_mul α) (hB.pos_part.const_mul β), integral_const_mul,
          integral_const_mul, hrefl, ← add_mul, hαβ, one_mul]

/-- Below some point both `(2y - 1)/(2σ²) < L` and `L < (-2y - 1)/(2σ²)`. -/
private lemma exists_threshold {σ : ℝ} (hσ : 0 < σ) (L : ℝ) :
    ∃ y₀, ∀ y ≤ y₀, (2 * y - 1) / (2 * σ ^ 2) < L ∧ L < (-2 * y - 1) / (2 * σ ^ 2) := by
  refine ⟨-(σ ^ 2 * |L|) - 1, fun y hy => ?_⟩
  have hσ2 : 0 < 2 * σ ^ 2 := by positivity
  have h1 : σ ^ 2 * L ≤ σ ^ 2 * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) (sq_nonneg σ)
  have h2 : -(σ ^ 2 * |L|) ≤ σ ^ 2 * L := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le L) (sq_nonneg σ)
    linarith
  rw [div_lt_iff₀ hσ2, lt_div_iff₀ hσ2]
  constructor <;> nlinarith

/-- Reflection `y ↦ -y` exchanges `f_1` and `f_{-1}` and fixes `f_0`. -/
private lemma integral_reflect {σ : ℝ} (a b : ℝ) :
    ∫ y, max (a * gaussDens σ 0 y + b * gaussDens σ 1 y) 0 =
      ∫ y, max (a * gaussDens σ 0 y + b * gaussDens σ (-1) y) 0 := by
  rw [← integral_neg_eq_self (fun y => max (a * gaussDens σ 0 y + b * gaussDens σ 1 y) 0)]
  simp only [gaussDens_neg, neg_zero]

/-- Forward step of `app:reflection` at a switching prefix, with the common positive prefix factor
removed and the final coordinate shifted by `-1`: for `r > 0` and `k > 0`,
`∫ (r f₋ + f₊ - k f₀)₊ < ∫ ((r + 1) f₋ - k f₀)₊`, where `f₋ = f_{-1}` and `f₊ = f_1`. -/
theorem forward_step {σ r k : ℝ} (hσ : 0 < σ) (hr : 0 < r) (hk : 0 < k) :
    ∫ y, max (r * gaussDens σ (-1) y + gaussDens σ 1 y - k * gaussDens σ 0 y) 0 <
      ∫ y, max ((r + 1) * gaussDens σ (-1) y - k * gaussDens σ 0 y) 0 := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hr1 : 0 < r + 1 := by linarith
  set A : ℝ → ℝ := fun y => (r + 1) * gaussDens σ (-1) y - k * gaussDens σ 0 y with hAdef
  set B : ℝ → ℝ := fun y => (r + 1) * gaussDens σ 1 y - k * gaussDens σ 0 y with hBdef
  have hAi : Integrable A :=
    ((integrable_gaussDens _).const_mul _).sub ((integrable_gaussDens _).const_mul _)
  have hBi : Integrable B :=
    ((integrable_gaussDens _).const_mul _).sub ((integrable_gaussDens _).const_mul _)
  have hsplit : ∀ y, r * gaussDens σ (-1) y + gaussDens σ 1 y - k * gaussDens σ 0 y =
      r / (r + 1) * A y + 1 / (r + 1) * B y := by
    intro y
    simp only [hAdef, hBdef]
    field_simp
    ring
  have hrefl : ∫ y, max (B y) 0 = ∫ y, max (A y) 0 := by
    have h1 := integral_reflect (σ := σ) (-k) (r + 1)
    have hB' : ∀ y, B y = -k * gaussDens σ 0 y + (r + 1) * gaussDens σ 1 y := fun y => by
      simp only [hBdef]; ring
    have hA' : ∀ y, A y = -k * gaussDens σ 0 y + (r + 1) * gaussDens σ (-1) y := fun y => by
      simp only [hAdef]; ring
    simp only [hB', hA']
    exact h1
  have hS : volume {y | 0 < A y ∧ B y < 0} ≠ 0 := by
    obtain ⟨y₀, hy₀⟩ := exists_threshold hσ (Real.log (k / (r + 1)))
    refine fun h0 => ?_
    have hsub : Set.Iic y₀ ⊆ {y | 0 < A y ∧ B y < 0} := by
      intro y hy
      obtain ⟨h1, h2⟩ := hy₀ y hy
      have hkr : 0 < k / (r + 1) := div_pos hk hr1
      have e1 : Real.exp ((2 * y - 1) / (2 * σ ^ 2)) < k / (r + 1) := by
        rw [← Real.exp_log hkr]; exact Real.exp_lt_exp.2 h1
      have e2 : k / (r + 1) < Real.exp ((-2 * y - 1) / (2 * σ ^ 2)) := by
        rw [← Real.exp_log hkr]; exact Real.exp_lt_exp.2 h2
      rw [div_lt_iff₀ hr1] at e2
      rw [lt_div_iff₀ hr1] at e1
      have hf0 := gaussDens_pos hσ0 0 y
      simp only [Set.mem_ofPred_eq, hAdef, hBdef, gaussDens_one hσ0, gaussDens_neg_one hσ0]
      constructor
      · have := mul_pos hf0 (sub_pos.2 e2)
        nlinarith
      · have := mul_pos hf0 (sub_pos.2 e1)
        nlinarith
    have := measure_mono_null hsub h0
    simp at this
  exact integral_max_lt_of_split (div_pos hr hr1) (one_div_pos.2 hr1)
    (by field_simp) hsplit hAi hBi hrefl hS

/-- Reverse step of `app:reflection` in the same coordinates: for `s < 0` and `k > 0`,
`∫ (f₀ - k f₊ + s f₋)₊ < ∫ (f₀ - (k - s) f₋)₊`. -/
theorem reverse_step {σ s k : ℝ} (hσ : 0 < σ) (hs : s < 0) (hk : 0 < k) :
    ∫ y, max (gaussDens σ 0 y - k * gaussDens σ 1 y + s * gaussDens σ (-1) y) 0 <
      ∫ y, max (gaussDens σ 0 y - (k - s) * gaussDens σ (-1) y) 0 := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hks : 0 < k - s := by linarith
  set A : ℝ → ℝ := fun y => gaussDens σ 0 y - (k - s) * gaussDens σ (-1) y with hAdef
  set B : ℝ → ℝ := fun y => gaussDens σ 0 y - (k - s) * gaussDens σ 1 y with hBdef
  have hAi : Integrable A :=
    (integrable_gaussDens _).sub ((integrable_gaussDens _).const_mul _)
  have hBi : Integrable B :=
    (integrable_gaussDens _).sub ((integrable_gaussDens _).const_mul _)
  have hsplit : ∀ y, gaussDens σ 0 y - k * gaussDens σ 1 y + s * gaussDens σ (-1) y =
      -s / (k - s) * A y + k / (k - s) * B y := by
    intro y
    simp only [hAdef, hBdef]
    field_simp
    ring
  have hrefl : ∫ y, max (B y) 0 = ∫ y, max (A y) 0 := by
    have h1 := integral_reflect (σ := σ) 1 (-(k - s))
    have hB' : ∀ y, B y = 1 * gaussDens σ 0 y + -(k - s) * gaussDens σ 1 y := fun y => by
      simp only [hBdef]; ring
    have hA' : ∀ y, A y = 1 * gaussDens σ 0 y + -(k - s) * gaussDens σ (-1) y := fun y => by
      simp only [hAdef]; ring
    simp only [hB', hA']
    exact h1
  have hS : volume {y | 0 < A y ∧ B y < 0} ≠ 0 := by
    obtain ⟨y₀, hy₀⟩ := exists_threshold hσ (Real.log (1 / (k - s)))
    refine fun h0 => ?_
    have hsub : Set.Ici (-y₀) ⊆ {y | 0 < A y ∧ B y < 0} := by
      intro y hy
      have hy' : -y ≤ y₀ := by simp only [Set.mem_Ici] at hy; linarith
      obtain ⟨h1, h2⟩ := hy₀ (-y) hy'
      have hks' : 0 < 1 / (k - s) := one_div_pos.2 hks
      have e1 : Real.exp ((-2 * y - 1) / (2 * σ ^ 2)) < 1 / (k - s) := by
        rw [← Real.exp_log hks']
        refine Real.exp_lt_exp.2 ?_
        have : (2 * -y - 1) / (2 * σ ^ 2) = (-2 * y - 1) / (2 * σ ^ 2) := by ring
        linarith
      have e2 : 1 / (k - s) < Real.exp ((2 * y - 1) / (2 * σ ^ 2)) := by
        rw [← Real.exp_log hks']
        refine Real.exp_lt_exp.2 ?_
        have : (-2 * -y - 1) / (2 * σ ^ 2) = (2 * y - 1) / (2 * σ ^ 2) := by ring
        linarith
      rw [lt_div_iff₀ hks] at e1
      rw [div_lt_iff₀ hks] at e2
      have hf0 := gaussDens_pos hσ0 0 y
      simp only [Set.mem_ofPred_eq, hAdef, hBdef, gaussDens_one hσ0, gaussDens_neg_one hσ0]
      constructor
      · have := mul_pos hf0 (sub_pos.2 e1)
        nlinarith
      · have := mul_pos hf0 (sub_pos.2 e2)
        nlinarith
    have := measure_mono_null hsub h0
    simp at this
  exact integral_max_lt_of_split (div_pos (neg_pos.2 hs) hks) (div_pos hk hks)
    (by field_simp; ring) hsplit hAi hBi hrefl hS

/-- On the switching region `r = U - kV > 0`, `k ≥ 1` and `V ≥ 0` force `s = V - kU < 0`. -/
theorem s_neg_of_r_pos {U V k : ℝ} (hk : 1 ≤ k) (hV : 0 ≤ V) (hr : 0 < U - k * V) :
    V - k * U < 0 := by
  have hU : 0 < U := by nlinarith
  nlinarith

end OneDim

section HockeyStick

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private lemma toReal_withDensity_ofReal {p : X → ℝ} (hp : Measurable p) (hp0 : 0 ≤ᵐ[μ] p)
    {A : Set X} (hA : MeasurableSet A) :
    (μ.withDensity (fun x => ENNReal.ofReal (p x)) A).toReal = ∫ x in A, p x ∂μ := by
  rw [withDensity_apply _ hA,
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hp0) hp.aestronglyMeasurable]

private lemma hockeyStick_withDensity_of_measurable {p q : X → ℝ} (hp : Measurable p)
    (hq : Measurable q) (hpi : Integrable p μ) (hqi : Integrable q μ) (hp0 : 0 ≤ᵐ[μ] p)
    (hq0 : 0 ≤ᵐ[μ] q) (ε : ℝ) :
    hockeyStick (μ.withDensity fun x => ENNReal.ofReal (p x))
        (μ.withDensity fun x => ENNReal.ofReal (q x)) ε =
      ∫ x, max (p x - Real.exp ε * q x) 0 ∂μ := by
  have : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (p x)) :=
    isFiniteMeasure_withDensity_ofReal hpi.2
  set k := Real.exp ε
  have hdi : Integrable (fun x => p x - k * q x) μ := hpi.sub (hqi.const_mul k)
  have hmass : ∀ A, MeasurableSet A →
      (μ.withDensity (fun x => ENNReal.ofReal (p x)) A).toReal -
          k * (μ.withDensity (fun x => ENNReal.ofReal (q x)) A).toReal =
        ∫ x in A, (p x - k * q x) ∂μ := by
    intro A hA
    rw [toReal_withDensity_ofReal hp hp0 hA, toReal_withDensity_ofReal hq hq0 hA,
      integral_sub hpi.integrableOn (hqi.const_mul k).integrableOn, integral_const_mul]
  apply le_antisymm
  · refine hockeyStick_le fun A hA => ?_
    rw [hmass A hA]
    calc ∫ x in A, (p x - k * q x) ∂μ ≤ ∫ x in A, max (p x - k * q x) 0 ∂μ :=
          setIntegral_mono_on hdi.integrableOn hdi.pos_part.integrableOn hA
            (fun x _ => le_max_left _ _)
      _ ≤ ∫ x, max (p x - k * q x) 0 ∂μ :=
          setIntegral_le_integral hdi.pos_part (ae_of_all _ fun x => le_max_right _ _)
  · set A := {x | 0 < p x - k * q x}
    have hA : MeasurableSet A := measurableSet_lt measurable_const (hp.sub (hq.const_mul k))
    have heq : ∫ x, max (p x - k * q x) 0 ∂μ = ∫ x in A, (p x - k * q x) ∂μ := by
      rw [← integral_indicator hA]
      congr 1
      funext x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        exact max_eq_left (le_of_lt hx)
      · rw [Set.indicator_of_notMem hx]
        exact max_eq_right (not_lt.1 hx)
    rw [heq, ← hmass A hA]
    exact le_hockeyStick ε hA

/-- For laws with integrable nonnegative densities `p` and `q`,
`H_ε(P, Q) = ∫ (p - e^ε q)₊`. -/
theorem hockeyStick_withDensity {p q : X → ℝ} (hpi : Integrable p μ) (hqi : Integrable q μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) (ε : ℝ) :
    hockeyStick (μ.withDensity fun x => ENNReal.ofReal (p x))
        (μ.withDensity fun x => ENNReal.ofReal (q x)) ε =
      ∫ x, max (p x - Real.exp ε * q x) 0 ∂μ := by
  have hp' := hpi.1.ae_eq_mk
  have hq' := hqi.1.ae_eq_mk
  have ep : (μ.withDensity fun x => ENNReal.ofReal (p x)) =
      μ.withDensity fun x => ENNReal.ofReal (hpi.1.mk p x) :=
    withDensity_congr_ae (hp'.fun_comp ENNReal.ofReal)
  have eq : (μ.withDensity fun x => ENNReal.ofReal (q x)) =
      μ.withDensity fun x => ENNReal.ofReal (hqi.1.mk q x) :=
    withDensity_congr_ae (hq'.fun_comp ENNReal.ofReal)
  have hp0' : 0 ≤ᵐ[μ] hpi.1.mk p := by
    filter_upwards [hp0, hp'] with x h1 h2
    rwa [← h2]
  have hq0' : 0 ≤ᵐ[μ] hqi.1.mk q := by
    filter_upwards [hq0, hq'] with x h1 h2
    rwa [← h2]
  rw [ep, eq, hockeyStick_withDensity_of_measurable hpi.1.stronglyMeasurable_mk.measurable
    hqi.1.stronglyMeasurable_mk.measurable (hpi.congr hp') (hqi.congr hq') hp0' hq0']
  refine integral_congr_ae ?_
  filter_upwards [hp', hq'] with x h1 h2
  rw [h1, h2]

end HockeyStick

section Model

variable {n : ℕ}

/-- Prefix density `∏_{t<n} f_{m_t}(y'_t)` for prefix means `m`. -/
noncomputable def prefixDens (σ : ℝ) (m : Fin n → ℝ) (y' : Fin n → ℝ) : ℝ :=
  ∏ t, gaussDens σ (m t) (y' t)

/-- The prefix mean vector `c e_j`. -/
def bump (c : ℝ) (j : Fin n) : Fin n → ℝ := fun t => if t = j then c else 0

/-- Density of `(1/T) ∑_j N(c e_j, σ² I_T)` with `T = n + 1`, in (prefix, final) coordinates;
the sum over `j` covers the `n` prefix rounds and then the final round. For `c = 2` and `c = 1`
these are the translated transcript densities of `P_S` and `Q_S` in `eq:chua`. -/
noncomputable def mixDens (σ c : ℝ) (x : (Fin n → ℝ) × ℝ) : ℝ :=
  (∑ j, prefixDens σ (bump c j) x.1 * gaussDens σ 0 x.2 +
    prefixDens σ 0 x.1 * gaussDens σ c x.2) / (n + 1)

/-- `U = ∑_{t<T} exp(2 z_t/σ - 2/σ²)`, summed over the `n = T - 1` prefix rounds, with
`z_t = y'_t/σ`. -/
noncomputable def sumU (σ : ℝ) (y' : Fin n → ℝ) : ℝ :=
  ∑ t, Real.exp (2 * (y' t / σ) / σ - 2 / σ ^ 2)

/-- `V = ∑_{t<T} exp(z_t/σ - 1/(2σ²))`, summed over the `n = T - 1` prefix rounds, with
`z_t = y'_t/σ`. -/
noncomputable def sumV (σ : ℝ) (y' : Fin n → ℝ) : ℝ :=
  ∑ t, Real.exp (y' t / σ / σ - 1 / (2 * σ ^ 2))

/-- The switching region `r = U - e^ε V > 0`. -/
def switchSet (σ ε : ℝ) : Set (Fin n → ℝ) :=
  {y' | 0 < sumU σ y' - Real.exp ε * sumV σ y'}

/-- Final-round mean of the real hypothesis when the differing item sits in the final round:
the policy changes the differing value to `-1` on the switching region. -/
noncomputable def finalMean (σ ε : ℝ) (y' : Fin n → ℝ) : ℝ :=
  if 0 < sumU σ y' - Real.exp ε * sumV σ y' then 0 else 2

/-- Translated transcript density of the real input under the adaptive policy. -/
noncomputable def adaptDens (σ ε : ℝ) (x : (Fin n → ℝ) × ℝ) : ℝ :=
  (∑ j, prefixDens σ (bump 2 j) x.1 * gaussDens σ 0 x.2 +
    prefixDens σ 0 x.1 * gaussDens σ (finalMean σ ε x.1) x.2) / (n + 1)

/-- `P_S` of `eq:chua` with `T = n + 1`. -/
noncomputable def chuaReal (n : ℕ) (σ : ℝ) : Measure ((Fin n → ℝ) × ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (mixDens σ 2 x)

/-- `Q_S` of `eq:chua` with `T = n + 1`. -/
noncomputable def chuaNull (n : ℕ) (σ : ℝ) : Measure ((Fin n → ℝ) × ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (mixDens σ 1 x)

/-- The real-input transcript law under the adaptive final query of `app:reflection`. -/
noncomputable def adaptReal (n : ℕ) (σ ε : ℝ) : Measure ((Fin n → ℝ) × ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (adaptDens σ ε x)

variable {σ : ℝ}

lemma prefixDens_pos (hσ : σ ≠ 0) (m y' : Fin n → ℝ) : 0 < prefixDens σ m y' :=
  Finset.prod_pos fun _ _ => gaussDens_pos hσ _ _

lemma integrable_prefixDens (m : Fin n → ℝ) : Integrable (prefixDens σ m) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun t => gaussDens σ (m t)) fun t => integrable_gaussDens _

lemma integral_prefixDens (hσ : σ ≠ 0) (m : Fin n → ℝ) : ∫ y', prefixDens σ m y' = 1 := by
  rw [volume_pi]
  simp only [prefixDens]
  rw [integral_fintype_prod_eq_prod (f := fun t => gaussDens σ (m t))]
  simp [integral_gaussDens hσ]

@[fun_prop]
lemma measurable_sumU : Measurable (sumU (n := n) σ) := by
  unfold sumU; fun_prop

@[fun_prop]
lemma measurable_sumV : Measurable (sumV (n := n) σ) := by
  unfold sumV; fun_prop

lemma measurableSet_switchSet (ε : ℝ) : MeasurableSet (switchSet (n := n) σ ε) :=
  measurableSet_lt measurable_const (by fun_prop)

/-- `∏_t f_{c[t=j]}(y'_t) = (∏_t f_0(y'_t)) · f_c(y'_j)/f_0(y'_j)`. -/
lemma prefixDens_bump (hσ : σ ≠ 0) (c : ℝ) (j : Fin n) (y' : Fin n → ℝ) :
    prefixDens σ (bump c j) y' =
      prefixDens σ 0 y' * Real.exp ((2 * c * y' j - c ^ 2) / (2 * σ ^ 2)) := by
  have h : ∀ t, gaussDens σ (bump c j t) (y' t) = gaussDens σ ((0 : Fin n → ℝ) t) (y' t) *
      (if t = j then Real.exp ((2 * c * y' j - c ^ 2) / (2 * σ ^ 2)) else 1) := by
    intro t
    by_cases ht : t = j
    · subst ht
      simp [bump, gaussDens_eq_mul_exp hσ c]
    · simp [bump, ht]
  simp only [prefixDens, h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ite_true]

/-- `∑_j ∏_t f_{2[t=j]}(y'_t) = (∏_t f_0(y'_t)) · U`. -/
lemma sum_prefixDens_two (hσ : σ ≠ 0) (y' : Fin n → ℝ) :
    ∑ j, prefixDens σ (bump 2 j) y' = prefixDens σ 0 y' * sumU σ y' := by
  simp only [prefixDens_bump hσ, sumU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  field_simp

/-- `∑_j ∏_t f_{[t=j]}(y'_t) = (∏_t f_0(y'_t)) · V`. -/
lemma sum_prefixDens_one (hσ : σ ≠ 0) (y' : Fin n → ℝ) :
    ∑ j, prefixDens σ (bump 1 j) y' = prefixDens σ 0 y' * sumV σ y' := by
  simp only [prefixDens_bump hσ, sumV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  field_simp

lemma mixDens_two (hσ : σ ≠ 0) (y' : Fin n → ℝ) (y : ℝ) :
    mixDens σ 2 (y', y) =
      prefixDens σ 0 y' / (n + 1) * (sumU σ y' * gaussDens σ 0 y + gaussDens σ 2 y) := by
  simp only [mixDens]
  rw [← Finset.sum_mul, sum_prefixDens_two hσ]
  ring

lemma mixDens_one (hσ : σ ≠ 0) (y' : Fin n → ℝ) (y : ℝ) :
    mixDens σ 1 (y', y) =
      prefixDens σ 0 y' / (n + 1) * (sumV σ y' * gaussDens σ 0 y + gaussDens σ 1 y) := by
  simp only [mixDens]
  rw [← Finset.sum_mul, sum_prefixDens_one hσ]
  ring

lemma adaptDens_eq (hσ : σ ≠ 0) (ε : ℝ) (y' : Fin n → ℝ) (y : ℝ) :
    adaptDens σ ε (y', y) = prefixDens σ 0 y' / (n + 1) *
      (sumU σ y' * gaussDens σ 0 y + gaussDens σ (finalMean σ ε y') y) := by
  simp only [adaptDens]
  rw [← Finset.sum_mul, sum_prefixDens_two hσ]
  ring

end Model

section Laws

variable {n : ℕ} {σ : ℝ}

lemma prefixDens_nonneg (m y' : Fin n → ℝ) : 0 ≤ prefixDens σ m y' :=
  Finset.prod_nonneg fun _ _ => gaussDens_nonneg _ _

lemma mixDens_nonneg (c : ℝ) (x : (Fin n → ℝ) × ℝ) : 0 ≤ mixDens σ c x := by
  unfold mixDens
  refine div_nonneg (add_nonneg (Finset.sum_nonneg fun j _ => ?_) ?_) (by positivity)
  · exact mul_nonneg (prefixDens_nonneg _ _) (gaussDens_nonneg _ _)
  · exact mul_nonneg (prefixDens_nonneg _ _) (gaussDens_nonneg _ _)

lemma adaptDens_nonneg (ε : ℝ) (x : (Fin n → ℝ) × ℝ) : 0 ≤ adaptDens σ ε x := by
  unfold adaptDens
  refine div_nonneg (add_nonneg (Finset.sum_nonneg fun j _ => ?_) ?_) (by positivity)
  · exact mul_nonneg (prefixDens_nonneg _ _) (gaussDens_nonneg _ _)
  · exact mul_nonneg (prefixDens_nonneg _ _) (gaussDens_nonneg _ _)

/-- `adaptDens` with the final factor split along the switching region. -/
lemma adaptDens_eq_indicator (ε : ℝ) (x : (Fin n → ℝ) × ℝ) :
    adaptDens σ ε x = (∑ j, prefixDens σ (bump 2 j) x.1 * gaussDens σ 0 x.2 +
      (switchSet σ ε).indicator (prefixDens σ 0) x.1 * gaussDens σ 0 x.2 +
      (switchSet σ ε)ᶜ.indicator (prefixDens σ 0) x.1 * gaussDens σ 2 x.2) / (n + 1) := by
  simp only [adaptDens, finalMean]
  by_cases h : x.1 ∈ switchSet σ ε
  · have h' : 0 < sumU σ x.1 - Real.exp ε * sumV σ x.1 := h
    simp [h, h']
  · have h' : ¬ 0 < sumU σ x.1 - Real.exp ε * sumV σ x.1 := h
    simp [h, h']

lemma integrable_mixDens (c : ℝ) : Integrable (mixDens (n := n) σ c) := by
  unfold mixDens
  rw [Measure.volume_eq_prod]
  refine Integrable.div_const ((integrable_finsetSum _ fun j _ => ?_).add ?_) _
  · exact (integrable_prefixDens _).mul_prod (integrable_gaussDens _)
  · exact (integrable_prefixDens _).mul_prod (integrable_gaussDens _)

lemma integrable_adaptDens (ε : ℝ) : Integrable (adaptDens (n := n) σ ε) := by
  rw [funext (adaptDens_eq_indicator ε), Measure.volume_eq_prod]
  have hS := measurableSet_switchSet (n := n) (σ := σ) ε
  refine Integrable.div_const (((integrable_finsetSum _ fun j _ => ?_).add ?_).add ?_) _
  · exact (integrable_prefixDens _).mul_prod (integrable_gaussDens _)
  · exact ((integrable_prefixDens _).indicator hS).mul_prod (integrable_gaussDens _)
  · exact ((integrable_prefixDens _).indicator hS.compl).mul_prod (integrable_gaussDens _)

lemma integral_mixDens (hσ : σ ≠ 0) (c : ℝ) : ∫ x, mixDens (n := n) σ c x = 1 := by
  unfold mixDens
  rw [Measure.volume_eq_prod, integral_div,
    integral_add (integrable_finsetSum _ fun j _ =>
      (integrable_prefixDens _).mul_prod (integrable_gaussDens _))
      ((integrable_prefixDens _).mul_prod (integrable_gaussDens _)),
    integral_finsetSum _ fun j _ => (integrable_prefixDens _).mul_prod (integrable_gaussDens _)]
  simp only [integral_prod_mul, integral_prefixDens hσ, integral_gaussDens hσ, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma integral_adaptDens (hσ : σ ≠ 0) (ε : ℝ) : ∫ x, adaptDens (n := n) σ ε x = 1 := by
  have hS := measurableSet_switchSet (n := n) (σ := σ) ε
  have hD := integrable_prefixDens (n := n) (σ := σ) 0
  have i1 : Integrable (fun x : (Fin n → ℝ) × ℝ =>
      ∑ j, prefixDens σ (bump 2 j) x.1 * gaussDens σ 0 x.2) (volume.prod volume) :=
    integrable_finsetSum _ fun j _ => (integrable_prefixDens _).mul_prod (integrable_gaussDens _)
  have i2 : Integrable (fun x : (Fin n → ℝ) × ℝ =>
      (switchSet σ ε).indicator (prefixDens σ 0) x.1 * gaussDens σ 0 x.2) (volume.prod volume) :=
    (hD.indicator hS).mul_prod (integrable_gaussDens _)
  have i3 : Integrable (fun x : (Fin n → ℝ) × ℝ =>
      (switchSet σ ε)ᶜ.indicator (prefixDens σ 0) x.1 * gaussDens σ 2 x.2)
      (volume.prod volume) :=
    (hD.indicator hS.compl).mul_prod (integrable_gaussDens _)
  have i12 : Integrable (fun x : (Fin n → ℝ) × ℝ =>
      ∑ j, prefixDens σ (bump 2 j) x.1 * gaussDens σ 0 x.2 +
        (switchSet σ ε).indicator (prefixDens σ 0) x.1 * gaussDens σ 0 x.2)
      (volume.prod volume) := i1.add i2
  rw [funext (adaptDens_eq_indicator ε), Measure.volume_eq_prod, integral_div,
    integral_add i12 i3, integral_add i1 i2,
    integral_finsetSum _ fun j _ => (integrable_prefixDens _).mul_prod (integrable_gaussDens _)]
  simp only [integral_prod_mul, integral_prefixDens hσ, integral_gaussDens hσ, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [add_assoc, integral_indicator hS, integral_indicator hS.compl,
    integral_add_compl hS hD, integral_prefixDens hσ]
  field_simp

private lemma isProbabilityMeasure_withDensity_ofReal {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : X → ℝ} (hpi : Integrable p μ) (hp0 : ∀ x, 0 ≤ p x)
    (h1 : ∫ x, p x ∂μ = 1) : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (p x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hpi (ae_of_all _ hp0), h1, ENNReal.ofReal_one]

theorem isProbabilityMeasure_chuaReal (hσ : 0 < σ) : IsProbabilityMeasure (chuaReal n σ) :=
  isProbabilityMeasure_withDensity_ofReal (integrable_mixDens 2) (mixDens_nonneg 2)
    (integral_mixDens hσ.ne' 2)

theorem isProbabilityMeasure_chuaNull (hσ : 0 < σ) : IsProbabilityMeasure (chuaNull n σ) :=
  isProbabilityMeasure_withDensity_ofReal (integrable_mixDens 1) (mixDens_nonneg 1)
    (integral_mixDens hσ.ne' 1)

theorem isProbabilityMeasure_adaptReal (hσ : 0 < σ) (ε : ℝ) :
    IsProbabilityMeasure (adaptReal n σ ε) :=
  isProbabilityMeasure_withDensity_ofReal (integrable_adaptDens ε) (adaptDens_nonneg ε)
    (integral_adaptDens hσ.ne' ε)

end Laws

section Main

variable {n : ℕ} {σ : ℝ}

private lemma integral_max_const_mul {c : ℝ} (hc : 0 ≤ c) (h : ℝ → ℝ) :
    ∫ y, max (c * h y) 0 = c * ∫ y, max (h y) 0 := by
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

/-- The shift `y ↦ y + 1` of the final coordinate maps `(f₀, f₁, f₂)` to `(f₋₁, f₀, f₁)`. -/
private lemma integral_shift (H : ℝ → ℝ → ℝ → ℝ) :
    ∫ y, H (gaussDens σ 0 y) (gaussDens σ 1 y) (gaussDens σ 2 y) =
      ∫ y, H (gaussDens σ (-1) y) (gaussDens σ 0 y) (gaussDens σ 1 y) := by
  rw [← integral_add_right_eq_self
    (fun y => H (gaussDens σ 0 y) (gaussDens σ 1 y) (gaussDens σ 2 y)) 1]
  simp only [gaussDens_add]
  norm_num

/-- Fubini comparison: fiberwise `≤`, strict on a set of positive measure. -/
private lemma integral_lt_of_fiberwise {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    (F G : α × β → ℝ) (hF : Integrable F) (hG : Integrable G) {S : Set α}
    (hS : volume S ≠ 0) (hle : ∀ a, ∫ b, F (a, b) ≤ ∫ b, G (a, b))
    (hlt : ∀ a ∈ S, ∫ b, F (a, b) < ∫ b, G (a, b)) :
    ∫ x, F x < ∫ x, G x := by
  rw [Measure.volume_eq_prod] at hF hG ⊢
  rw [integral_prod F hF, integral_prod G hG]
  exact integral_lt_integral_of_le_of_measure_ne_zero hF.integral_prod_left
    hG.integral_prod_left hle fun h0 => hS (measure_mono_null hlt h0)

/-- The switching region has positive Lebesgue measure: it contains the box where every prefix
coordinate exceeds `σ²ε + 3/2`. -/
theorem volume_switchSet_ne_zero (hn : 1 ≤ n) (hσ : 0 < σ) (ε : ℝ) :
    volume (switchSet (n := n) σ ε) ≠ 0 := by
  set M := σ ^ 2 * ε + 3 / 2 with hM
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsub : Set.univ.pi (fun _ : Fin n => Set.Ioi M) ⊆ switchSet σ ε := by
    intro y' hy'
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioi, true_implies] at hy'
    show 0 < sumU σ y' - Real.exp ε * sumV σ y'
    rw [sumU, sumV, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_pos (fun t _ => ?_) Finset.univ_nonempty
    rw [← Real.exp_add, sub_pos, Real.exp_lt_exp]
    have key : 2 * (y' t / σ) / σ - 2 / σ ^ 2 - (ε + (y' t / σ / σ - 1 / (2 * σ ^ 2))) =
        (y' t - M) / σ ^ 2 := by
      rw [hM]
      field_simp
      ring
    have : 0 < (y' t - M) / σ ^ 2 := div_pos (by linarith [hy' t]) (by positivity)
    linarith
  have hbox : volume (Set.univ.pi (fun _ : Fin n => Set.Ioi M)) ≠ 0 := by
    rw [volume_pi, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => by simp [Real.volume_Ioi]
  exact fun h0 => hbox (measure_mono_null hsub h0)

/-- Forward comparison on one switching prefix. -/
private lemma fiber_forward (hσ : 0 < σ) (ε : ℝ) {y' : Fin n → ℝ} (h : y' ∈ switchSet σ ε) :
    ∫ y, max (mixDens σ 2 (y', y) - Real.exp ε * mixDens σ 1 (y', y)) 0 <
      ∫ y, max (adaptDens σ ε (y', y) - Real.exp ε * mixDens σ 1 (y', y)) 0 := by
  have hσ0 := hσ.ne'
  set k := Real.exp ε
  set r := sumU σ y' - k * sumV σ y'
  have hr : 0 < r := h
  set c := prefixDens σ 0 y' / (n + 1)
  have hc : 0 < c := div_pos (prefixDens_pos hσ0 _ _) (by positivity)
  have hm : finalMean σ ε y' = 0 := ite_eq_left hr
  have e1 : ∀ y, mixDens σ 2 (y', y) - k * mixDens σ 1 (y', y) =
      c * (r * gaussDens σ 0 y + gaussDens σ 2 y - k * gaussDens σ 1 y) := by
    intro y
    rw [mixDens_two hσ0, mixDens_one hσ0]
    ring
  have e2 : ∀ y, adaptDens σ ε (y', y) - k * mixDens σ 1 (y', y) =
      c * ((r + 1) * gaussDens σ 0 y - k * gaussDens σ 1 y) := by
    intro y
    rw [adaptDens_eq hσ0, mixDens_one hσ0, hm]
    ring
  simp only [e1, e2, integral_max_const_mul hc.le]
  refine mul_lt_mul_of_pos_left ?_ hc
  have s1 := integral_shift (σ := σ) fun a b d => max (r * a + d - k * b) 0
  have s2 := integral_shift (σ := σ) fun a b d => max ((r + 1) * a - k * b) 0
  beta_reduce at s1 s2
  rw [s1, s2]
  exact forward_step hσ hr (Real.exp_pos ε)

/-- Reverse comparison on one switching prefix, for `ε ≥ 0`. -/
private lemma fiber_reverse (hσ : 0 < σ) {ε : ℝ} (hε : 0 ≤ ε) {y' : Fin n → ℝ}
    (h : y' ∈ switchSet σ ε) :
    ∫ y, max (mixDens σ 1 (y', y) - Real.exp ε * mixDens σ 2 (y', y)) 0 <
      ∫ y, max (mixDens σ 1 (y', y) - Real.exp ε * adaptDens σ ε (y', y)) 0 := by
  have hσ0 := hσ.ne'
  set k := Real.exp ε
  have hk1 : 1 ≤ k := Real.one_le_exp hε
  have hr : 0 < sumU σ y' - k * sumV σ y' := h
  have hV : 0 ≤ sumV σ y' := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  set s := sumV σ y' - k * sumU σ y'
  have hs : s < 0 := s_neg_of_r_pos hk1 hV hr
  set c := prefixDens σ 0 y' / (n + 1)
  have hc : 0 < c := div_pos (prefixDens_pos hσ0 _ _) (by positivity)
  have hm : finalMean σ ε y' = 0 := ite_eq_left hr
  have e1 : ∀ y, mixDens σ 1 (y', y) - k * mixDens σ 2 (y', y) =
      c * (gaussDens σ 1 y - k * gaussDens σ 2 y + s * gaussDens σ 0 y) := by
    intro y
    rw [mixDens_two hσ0, mixDens_one hσ0]
    ring
  have e2 : ∀ y, mixDens σ 1 (y', y) - k * adaptDens σ ε (y', y) =
      c * (gaussDens σ 1 y - (k - s) * gaussDens σ 0 y) := by
    intro y
    rw [adaptDens_eq hσ0, mixDens_one hσ0, hm]
    ring
  simp only [e1, e2, integral_max_const_mul hc.le]
  refine mul_lt_mul_of_pos_left ?_ hc
  have s1 := integral_shift (σ := σ) fun a b d => max (b - k * d + s * a) 0
  have s2 := integral_shift (σ := σ) fun a b d => max (b - (k - s) * a) 0
  beta_reduce at s1 s2
  rw [s1, s2]
  exact reverse_step hσ hs (Real.exp_pos ε)

/-- Off the switching region the adaptive law has the same density as `P_S`. -/
private lemma adaptDens_of_not_mem (ε : ℝ) {y' : Fin n → ℝ} (h : y' ∉ switchSet σ ε) (y : ℝ) :
    adaptDens σ ε (y', y) = mixDens σ 2 (y', y) := by
  have hm : finalMean σ ε y' = 2 := ite_eq_right h
  simp only [adaptDens, mixDens, hm]

/-- Forward half of `app:reflection`, at every real `ε`. -/
theorem hockeyStick_chua_lt_adapt (hn : 1 ≤ n) (hσ : 0 < σ) (ε : ℝ) :
    hockeyStick (chuaReal n σ) (chuaNull n σ) ε <
      hockeyStick (adaptReal n σ ε) (chuaNull n σ) ε := by
  unfold chuaReal chuaNull adaptReal
  rw [hockeyStick_withDensity (integrable_mixDens 2) (integrable_mixDens 1)
      (ae_of_all _ (mixDens_nonneg 2)) (ae_of_all _ (mixDens_nonneg 1)),
    hockeyStick_withDensity (integrable_adaptDens ε) (integrable_mixDens 1)
      (ae_of_all _ (adaptDens_nonneg ε)) (ae_of_all _ (mixDens_nonneg 1))]
  refine integral_lt_of_fiberwise
    (fun x => max (mixDens σ 2 x - Real.exp ε * mixDens σ 1 x) 0)
    (fun x => max (adaptDens σ ε x - Real.exp ε * mixDens σ 1 x) 0)
    ((integrable_mixDens 2).sub ((integrable_mixDens 1).const_mul _)).pos_part
    ((integrable_adaptDens ε).sub ((integrable_mixDens 1).const_mul _)).pos_part
    (volume_switchSet_ne_zero hn hσ ε) (fun y' => ?_) (fun y' h => fiber_forward hσ ε h)
  by_cases h : y' ∈ switchSet σ ε
  · exact (fiber_forward hσ ε h).le
  · simp only [adaptDens_of_not_mem ε h, le_refl]

/-- Reverse half of `app:reflection`, for `ε ≥ 0`. -/
theorem hockeyStick_chua_lt_adapt_reverse (hn : 1 ≤ n) (hσ : 0 < σ) {ε : ℝ} (hε : 0 ≤ ε) :
    hockeyStick (chuaNull n σ) (chuaReal n σ) ε <
      hockeyStick (chuaNull n σ) (adaptReal n σ ε) ε := by
  unfold chuaReal chuaNull adaptReal
  rw [hockeyStick_withDensity (integrable_mixDens 1) (integrable_mixDens 2)
      (ae_of_all _ (mixDens_nonneg 1)) (ae_of_all _ (mixDens_nonneg 2)),
    hockeyStick_withDensity (integrable_mixDens 1) (integrable_adaptDens ε)
      (ae_of_all _ (mixDens_nonneg 1)) (ae_of_all _ (adaptDens_nonneg ε))]
  refine integral_lt_of_fiberwise
    (fun x => max (mixDens σ 1 x - Real.exp ε * mixDens σ 2 x) 0)
    (fun x => max (mixDens σ 1 x - Real.exp ε * adaptDens σ ε x) 0)
    ((integrable_mixDens 1).sub ((integrable_mixDens 2).const_mul _)).pos_part
    ((integrable_mixDens 1).sub ((integrable_adaptDens ε).const_mul _)).pos_part
    (volume_switchSet_ne_zero hn hσ ε) (fun y' => ?_) (fun y' h => fiber_reverse hσ hε h)
  by_cases h : y' ∈ switchSet σ ε
  · exact (fiber_reverse hσ hε h).le
  · simp only [adaptDens_of_not_mem ε h, le_refl]

/-- `app:reflection`: for `T = n + 1 ≥ 2` rounds, `σ > 0` and `ε ≥ 0`, the adaptive final query
strictly increases both ordered hockey-stick divergences of the pair `eq:chua`, so that pair
does not dominate every adaptive query. -/
theorem chua_pair_strictly_improvable (hn : 1 ≤ n) (hσ : 0 < σ) {ε : ℝ} (hε : 0 ≤ ε) :
    hockeyStick (chuaReal n σ) (chuaNull n σ) ε <
        hockeyStick (adaptReal n σ ε) (chuaNull n σ) ε ∧
      hockeyStick (chuaNull n σ) (chuaReal n σ) ε <
        hockeyStick (chuaNull n σ) (adaptReal n σ ε) ε :=
  ⟨hockeyStick_chua_lt_adapt hn hσ ε, hockeyStick_chua_lt_adapt_reverse hn hσ hε⟩

end Main

end Reflection

end ASGA
