import Mathlib

/-!
# Shared definitions

Definitions used by every module of the formalization: the hockey-stick
divergence, total variation distance, the testing tradeoff function, the
standard normal CDF, the sensitivity-one Gaussian privacy profile, the
null-clone cost, and finite binary experiments on `Fin n`.

Paper references are to "Certified Accounting for Adaptive Shuffled Gaussian
Training" (equation and theorem labels as in `paper/main.tex`).
-/

open MeasureTheory ProbabilityTheory

namespace ASGA

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Hockey-stick divergence `H_ε(P,Q) = sup_A (P(A) - e^ε Q(A))`, the supremum
taken over measurable sets. -/
noncomputable def hockeyStick (P Q : Measure Ω) (ε : ℝ) : ℝ :=
  ⨆ A : {s : Set Ω // MeasurableSet s}, ((P A).toReal - Real.exp ε * (Q A).toReal)

/-- Total variation distance `sup_A |P(A) - Q(A)|` over measurable sets. -/
noncomputable def tvDist (P Q : Measure Ω) : ℝ :=
  ⨆ A : {s : Set Ω // MeasurableSet s}, |(P A).toReal - (Q A).toReal|

/-- Randomized tests: measurable functions with values in `[0,1]`. -/
def IsTest (φ : Ω → ℝ) : Prop := Measurable φ ∧ ∀ x, 0 ≤ φ x ∧ φ x ≤ 1

/-- Testing tradeoff `T_{P,Q}(a) = inf {1 - E_P φ : φ a test, E_Q φ ≤ a}`. -/
noncomputable def tradeoff (P Q : Measure Ω) (a : ℝ) : ℝ :=
  ⨅ φ : {φ : Ω → ℝ // IsTest φ ∧ ∫ x, φ x ∂Q ≤ a}, (1 - ∫ x, φ.1 x ∂P)

/-- Standard normal CDF `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Sensitivity-one Gaussian privacy profile `g_σ(ε)`, equation `eq:gaussian`. -/
noncomputable def gaussProfile (σ ε : ℝ) : ℝ :=
  Phi (-σ * ε + 1 / (2 * σ)) - Real.exp ε * Phi (-σ * ε - 1 / (2 * σ))

/-- Null-clone cost `γ_σ(p)` with `h = log (1/p)`, equation `eq:gamma`. -/
noncomputable def cloneCost (σ p : ℝ) : ℝ :=
  p * Phi (-σ * Real.log (1 / p) + 1 / (2 * σ)) - Phi (-σ * Real.log (1 / p) - 1 / (2 * σ))

/-- The finite measure on `Fin n` with masses `w i` (negative entries are read as `0`). -/
noncomputable def finMeasure {n : ℕ} (w : Fin n → ℝ) : Measure (Fin n) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

section API

variable {P Q : Measure Ω}

lemma hockeyStick_bddAbove [IsFiniteMeasure P] (ε : ℝ) :
    BddAbove (Set.range fun A : {s : Set Ω // MeasurableSet s} =>
      (P A).toReal - Real.exp ε * (Q A).toReal) := by
  refine ⟨(P Set.univ).toReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  have h1 : (P A).toReal ≤ (P Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (Set.subset_univ _))
  have h2 : 0 ≤ Real.exp ε * (Q A).toReal := by positivity
  linarith

lemma le_hockeyStick [IsFiniteMeasure P] (ε : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    (P A).toReal - Real.exp ε * (Q A).toReal ≤ hockeyStick P Q ε :=
  le_ciSup (f := fun A : {s : Set Ω // MeasurableSet s} =>
    (P A).toReal - Real.exp ε * (Q A).toReal) (hockeyStick_bddAbove ε) ⟨A, hA⟩

lemma hockeyStick_le {ε c : ℝ}
    (h : ∀ A, MeasurableSet A → (P A).toReal - Real.exp ε * (Q A).toReal ≤ c) :
    hockeyStick P Q ε ≤ c :=
  ciSup_le fun A => h A.1 A.2

lemma hockeyStick_nonneg [IsFiniteMeasure P] (ε : ℝ) : 0 ≤ hockeyStick P Q ε := by
  have := le_hockeyStick (P := P) (Q := Q) ε MeasurableSet.empty
  simpa using this

lemma tvDist_bddAbove [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    BddAbove (Set.range fun A : {s : Set Ω // MeasurableSet s} =>
      |(P A).toReal - (Q A).toReal|) := by
  refine ⟨(P Set.univ).toReal + (Q Set.univ).toReal, ?_⟩
  rintro _ ⟨A, rfl⟩
  have h1 : (P A).toReal ≤ (P Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (Set.subset_univ _))
  have h2 : (Q A).toReal ≤ (Q Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono (Set.subset_univ _))
  have h3 : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (Q A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

lemma le_tvDist [IsFiniteMeasure P] [IsFiniteMeasure Q] {A : Set Ω} (hA : MeasurableSet A) :
    |(P A).toReal - (Q A).toReal| ≤ tvDist P Q :=
  le_ciSup (f := fun A : {s : Set Ω // MeasurableSet s} =>
    |(P A).toReal - (Q A).toReal|) tvDist_bddAbove ⟨A, hA⟩

lemma tvDist_le {c : ℝ} (h : ∀ A, MeasurableSet A → |(P A).toReal - (Q A).toReal| ≤ c) :
    tvDist P Q ≤ c :=
  ciSup_le fun A => h A.1 A.2

lemma finMeasure_apply {n : ℕ} (w : Fin n → ℝ) (A : Set (Fin n)) :
    finMeasure w A = ∑ i, ENNReal.ofReal (w i) * Set.indicator A 1 i := by
  simp [finMeasure, Finset.sum_apply, Measure.dirac_apply', Set.indicator]

instance {n : ℕ} (w : Fin n → ℝ) : IsFiniteMeasure (finMeasure w) := by
  constructor
  rw [finMeasure_apply]
  exact ENNReal.sum_lt_top.2 fun i _ => by
    by_cases h : i ∈ (Set.univ : Set (Fin n)) <;> simp

end API

end ASGA
