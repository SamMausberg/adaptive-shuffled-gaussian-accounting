import ASGA.Basic

/-!
# The testing envelope and its finite rational pair

This file proves the first claim of `thm:main` and the facts used for it in the proof given in
`sec:composition`. The input is a finite list of rational lines `(k_j, d_j⁺, d_j⁻)` with
`k_j ≥ 1` and `0 ≤ d_j^± ≤ 1`, and the envelope `f` of `eq:envelope`.

* `envelope_convexOn`, `envelope_antitoneOn`, `envelope_nonneg`, `envelope_le_one_sub`,
  `envelope_one`: the envelope is convex and decreasing on `[0,1]`, lies between `0` and `1 - a`,
  and vanishes at `1`.
* `integral_sub_le_hockeyStick`: a hockey-stick bound extends from sets to randomized tests.
* `envelope_le_tradeoff`: the line inequalities give `T_{P,Q} ≥ f` on `[0,1]`.
* `hockeyStick_swap`, `hockeyStick_swap_le`: the reverse divergence is determined by the forward
  one (`sec:model`), so forward dominance at every threshold gives reverse dominance.
* `envR`, `envS`: the finite pair of `eq:atoms`, built on the sorted crossings of the envelope
  lines in `[0,1]`, with rational masses.
* `envPair_tradeoff`, `envPair_dominates`: the pair has testing tradeoff `f` and dominates every
  pair satisfying the line inequalities. `envPair_spec` collects the properties of this explicit
  pair and `envelope_pair_exists` states the existence claim of `thm:main`.
-/

open MeasureTheory Set

namespace ASGA

/-! ### Input lines and the envelope -/

/-- One certified input of `thm:main`: a threshold `k ≥ 1` and bounds `d⁺, d⁻ ∈ [0,1]`, read as
`H_{log k}(P,Q) ≤ d⁺` and `H_{log k}(Q,P) ≤ d⁻`. -/
structure EnvLine where
  /-- The threshold `k`, with privacy level `log k`. -/
  k : ℚ
  /-- The forward bound `d⁺`. -/
  dplus : ℚ
  /-- The reverse bound `d⁻`. -/
  dminus : ℚ
  one_le_k : 1 ≤ k
  dplus_nonneg : 0 ≤ dplus
  dplus_le_one : dplus ≤ 1
  dminus_nonneg : 0 ≤ dminus
  dminus_le_one : dminus ≤ 1

namespace EnvLine

variable (l : EnvLine)

lemma one_le_k_real : (1 : ℝ) ≤ l.k := by exact_mod_cast l.one_le_k

lemma k_pos_real : (0 : ℝ) < l.k := lt_of_lt_of_le one_pos l.one_le_k_real

lemma dplus_nonneg_real : (0 : ℝ) ≤ l.dplus := by exact_mod_cast l.dplus_nonneg

lemma dminus_nonneg_real : (0 : ℝ) ≤ l.dminus := by exact_mod_cast l.dminus_nonneg

end EnvLine

/-- The envelope `f` of `eq:envelope`:
`f(a) = max {0, max_j (1 - d_j⁺ - k_j a), max_j (1 - d_j⁻ - a)/k_j}`, and `0` for the empty
list. -/
noncomputable def envelope (L : List EnvLine) (a : ℝ) : ℝ :=
  L.foldr (fun l m => max m (max (1 - (l.dplus : ℝ) - (l.k : ℝ) * a)
    ((1 - (l.dminus : ℝ) - a) / (l.k : ℝ)))) 0

/-- The envelope evaluated at rational points, used for the atom masses. -/
def envelopeQ (L : List EnvLine) (a : ℚ) : ℚ :=
  L.foldr (fun l m => max m (max (1 - l.dplus - l.k * a) ((1 - l.dminus - a) / l.k))) 0

section EnvelopeBasic

variable (L : List EnvLine)

lemma envelope_nil (a : ℝ) : envelope [] a = 0 := rfl

lemma envelope_cons (l : EnvLine) (a : ℝ) :
    envelope (l :: L) a = max (envelope L a) (max (1 - (l.dplus : ℝ) - (l.k : ℝ) * a)
      ((1 - (l.dminus : ℝ) - a) / (l.k : ℝ))) := rfl

lemma envelopeQ_cast (a : ℚ) : ((envelopeQ L a : ℚ) : ℝ) = envelope L a := by
  induction L with
  | nil => simp [envelopeQ, envelope]
  | cons l L ih =>
    rw [envelope_cons, ← ih]
    simp only [envelopeQ, List.foldr_cons]
    push_cast
    rfl

/-- `f ≥ 0` (`sec:composition`). -/
theorem envelope_nonneg (a : ℝ) : 0 ≤ envelope L a := by
  induction L with
  | nil => exact le_rfl
  | cons l L ih => rw [envelope_cons]; exact le_max_of_le_left ih

variable {L}

lemma fwd_le_envelope {l : EnvLine} (hl : l ∈ L) (a : ℝ) :
    1 - (l.dplus : ℝ) - (l.k : ℝ) * a ≤ envelope L a := by
  induction L with
  | nil => simp at hl
  | cons l' L ih =>
    rw [envelope_cons]
    rcases List.mem_cons.1 hl with rfl | h
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_left (ih h)

lemma rev_le_envelope {l : EnvLine} (hl : l ∈ L) (a : ℝ) :
    (1 - (l.dminus : ℝ) - a) / (l.k : ℝ) ≤ envelope L a := by
  induction L with
  | nil => simp at hl
  | cons l' L ih =>
    rw [envelope_cons]
    rcases List.mem_cons.1 hl with rfl | h
    · exact le_max_of_le_right (le_max_right _ _)
    · exact le_max_of_le_left (ih h)

variable (L)

/-- The envelope is attained by one of the terms of `eq:envelope`. -/
lemma envelope_cases (a : ℝ) :
    envelope L a = 0 ∨ ∃ l ∈ L, envelope L a = 1 - (l.dplus : ℝ) - (l.k : ℝ) * a ∨
      envelope L a = (1 - (l.dminus : ℝ) - a) / (l.k : ℝ) := by
  induction L with
  | nil => exact Or.inl rfl
  | cons l L ih =>
    rw [envelope_cons]
    rcases max_choice (envelope L a) (max (1 - (l.dplus : ℝ) - (l.k : ℝ) * a)
      ((1 - (l.dminus : ℝ) - a) / (l.k : ℝ))) with h | h <;> rw [h]
    · rcases ih with h0 | ⟨l', hl', h'⟩
      · exact Or.inl h0
      · exact Or.inr ⟨l', List.mem_cons_of_mem _ hl', h'⟩
    · refine Or.inr ⟨l, List.mem_cons_self .., ?_⟩
      rcases max_choice (1 - (l.dplus : ℝ) - (l.k : ℝ) * a)
        ((1 - (l.dminus : ℝ) - a) / (l.k : ℝ)) with h2 | h2 <;> rw [h2] <;> simp

/-- `envelope L a` is the least upper bound of `0` and of all terms of `eq:envelope`. -/
theorem envelope_le_iff (a c : ℝ) :
    envelope L a ≤ c ↔ 0 ≤ c ∧ ∀ l ∈ L, 1 - (l.dplus : ℝ) - (l.k : ℝ) * a ≤ c ∧
      (1 - (l.dminus : ℝ) - a) / (l.k : ℝ) ≤ c := by
  constructor
  · intro h
    exact ⟨(envelope_nonneg L a).trans h, fun l hl =>
      ⟨(fwd_le_envelope hl a).trans h, (rev_le_envelope hl a).trans h⟩⟩
  · rintro ⟨h0, h⟩
    rcases envelope_cases L a with he | ⟨l, hl, he | he⟩ <;> rw [he]
    · exact h0
    · exact (h l hl).1
    · exact (h l hl).2

end EnvelopeBasic

/-! ### Affine pieces -/

/-- The affine pieces of the envelope; `(α, β)` stands for `a ↦ α - β a`. The first piece is the
zero line. -/
def pieces (L : List EnvLine) : List (ℚ × ℚ) :=
  (0, 0) :: L.flatMap fun l => [(1 - l.dplus, l.k), ((1 - l.dminus) / l.k, 1 / l.k)]

/-- Value of the piece `(α, β)` at `a`. -/
noncomputable def pval (p : ℚ × ℚ) (a : ℝ) : ℝ := (p.1 : ℝ) - (p.2 : ℝ) * a

section Pieces

variable {L : List EnvLine}

lemma zero_mem_pieces : ((0, 0) : ℚ × ℚ) ∈ pieces L := List.mem_cons_self ..

lemma fwd_mem_pieces {l : EnvLine} (hl : l ∈ L) : (1 - l.dplus, l.k) ∈ pieces L :=
  List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨l, hl, by simp⟩)

lemma rev_mem_pieces {l : EnvLine} (hl : l ∈ L) :
    ((1 - l.dminus) / l.k, 1 / l.k) ∈ pieces L :=
  List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨l, hl, by simp⟩)

lemma pieces_cases {p : ℚ × ℚ} (hp : p ∈ pieces L) :
    p = (0, 0) ∨ ∃ l ∈ L, p = (1 - l.dplus, l.k) ∨ p = ((1 - l.dminus) / l.k, 1 / l.k) := by
  rcases List.mem_cons.1 hp with h | h
  · exact Or.inl h
  · obtain ⟨l, hl, hp⟩ := List.mem_flatMap.1 h
    refine Or.inr ⟨l, hl, ?_⟩
    simpa using hp

lemma pval_zero (a : ℝ) : pval (0, 0) a = 0 := by simp [pval]

lemma pval_fwd (l : EnvLine) (a : ℝ) :
    pval (1 - l.dplus, l.k) a = 1 - (l.dplus : ℝ) - (l.k : ℝ) * a := by
  simp [pval]

lemma pval_rev (l : EnvLine) (a : ℝ) :
    pval ((1 - l.dminus) / l.k, 1 / l.k) a = (1 - (l.dminus : ℝ) - a) / (l.k : ℝ) := by
  have hk := l.k_pos_real.ne'
  simp only [pval]
  push_cast
  field_simp

lemma pieces_slope_nonneg {p : ℚ × ℚ} (hp : p ∈ pieces L) : (0 : ℝ) ≤ p.2 := by
  rcases pieces_cases hp with rfl | ⟨l, -, rfl | rfl⟩
  · simp
  · exact l.k_pos_real.le
  · have := l.k_pos_real
    push_cast
    positivity

lemma pval_le_envelope {p : ℚ × ℚ} (hp : p ∈ pieces L) (a : ℝ) : pval p a ≤ envelope L a := by
  rcases pieces_cases hp with rfl | ⟨l, hl, rfl | rfl⟩
  · rw [pval_zero]; exact envelope_nonneg L a
  · rw [pval_fwd]; exact fwd_le_envelope hl a
  · rw [pval_rev]; exact rev_le_envelope hl a

variable (L)

lemma exists_pval_eq_envelope (a : ℝ) : ∃ p ∈ pieces L, envelope L a = pval p a := by
  rcases envelope_cases L a with h | ⟨l, hl, h | h⟩
  · exact ⟨_, zero_mem_pieces, by rw [h, pval_zero]⟩
  · exact ⟨_, fwd_mem_pieces hl, by rw [h, pval_fwd]⟩
  · exact ⟨_, rev_mem_pieces hl, by rw [h, pval_rev]⟩

end Pieces

/-! ### Shape of the envelope -/

section Shape

variable (L : List EnvLine)

/-- Every piece has nonpositive slope, so the envelope is antitone on all of `ℝ`. -/
theorem envelope_antitone : Antitone (envelope L) := by
  intro x y hxy
  obtain ⟨p, hp, hpy⟩ := exists_pval_eq_envelope L y
  rw [hpy]
  have hβ := pieces_slope_nonneg hp
  calc pval p y ≤ pval p x := by
        simp only [pval]; nlinarith
    _ ≤ envelope L x := pval_le_envelope hp x

/-- The envelope is decreasing on `[0,1]` (`sec:composition`). -/
theorem envelope_antitoneOn : AntitoneOn (envelope L) (Icc 0 1) :=
  (envelope_antitone L).antitoneOn _

/-- As a maximum of affine functions, the envelope is convex on all of `ℝ`. -/
theorem envelope_convexOn_univ : ConvexOn ℝ univ (envelope L) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨p, hp, hpz⟩ := exists_pval_eq_envelope L (a • x + b • y)
  rw [hpz]
  have hx := pval_le_envelope hp x
  have hy := pval_le_envelope hp y
  have hlin : pval p (a • x + b • y) = a * pval p x + b * pval p y := by
    simp only [pval, smul_eq_mul]
    linear_combination (-(p.1 : ℝ)) * hab
  rw [hlin, smul_eq_mul, smul_eq_mul]
  gcongr

/-- The envelope is convex on `[0,1]` (`sec:composition`). -/
theorem envelope_convexOn : ConvexOn ℝ (Icc 0 1) (envelope L) :=
  (envelope_convexOn_univ L).subset (subset_univ _) (convex_Icc 0 1)

/-- The envelope lies below `1 - a` on `[0,1]` (`sec:composition`). -/
theorem envelope_le_one_sub {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : envelope L a ≤ 1 - a := by
  rw [envelope_le_iff]
  refine ⟨by linarith, fun l _ => ⟨?_, ?_⟩⟩
  · have := l.one_le_k_real
    have := l.dplus_nonneg_real
    nlinarith
  · have hk := l.k_pos_real
    have := l.one_le_k_real
    have := l.dminus_nonneg_real
    rw [div_le_iff₀ hk]
    nlinarith

/-- `f(1) = 0` (`sec:composition`). -/
theorem envelope_one : envelope L 1 = 0 :=
  le_antisymm (by simpa using envelope_le_one_sub L zero_le_one le_rfl) (envelope_nonneg L 1)

lemma envelope_zero_le_one : envelope L 0 ≤ 1 := by
  simpa using envelope_le_one_sub L le_rfl zero_le_one

end Shape

/-! ### Randomized tests -/

section Tests

variable {Ω : Type*} [MeasurableSpace Ω]

lemma IsTest.integrable {φ : Ω → ℝ} (hφ : IsTest φ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable φ μ :=
  Integrable.of_bound hφ.1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hφ.2 x).1, (hφ.2 x).2])

lemma IsTest.one_sub {φ : Ω → ℝ} (hφ : IsTest φ) : IsTest fun x => 1 - φ x :=
  ⟨measurable_const.sub hφ.1, fun x => ⟨by linarith [(hφ.2 x).2], by linarith [(hφ.2 x).1]⟩⟩

lemma isTest_zero : IsTest fun _ : Ω => (0 : ℝ) :=
  ⟨measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩

lemma isTest_indicator {A : Set Ω} (hA : MeasurableSet A) : IsTest (A.indicator 1) :=
  ⟨measurable_const.indicator hA, fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩

lemma IsTest.integral_nonneg {φ : Ω → ℝ} (hφ : IsTest φ) (μ : Measure Ω) :
    0 ≤ ∫ x, φ x ∂μ :=
  MeasureTheory.integral_nonneg fun x => (hφ.2 x).1

lemma IsTest.integral_le_one {φ : Ω → ℝ} (hφ : IsTest φ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : ∫ x, φ x ∂μ ≤ 1 := by
  calc ∫ x, φ x ∂μ ≤ ∫ _, (1 : ℝ) ∂μ :=
        integral_mono (hφ.integrable μ) (integrable_const 1) fun x => (hφ.2 x).2
    _ = 1 := by simp

lemma IsTest.integral_one_sub {φ : Ω → ℝ} (hφ : IsTest φ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : ∫ x, (1 - φ x) ∂μ = 1 - ∫ x, φ x ∂μ := by
  rw [integral_sub (integrable_const 1) (hφ.integrable μ)]
  simp

/-- A hockey-stick bound holds for randomized tests (`sec:composition`): for finite measures,
`E_P φ - e^ε E_Q φ ≤ H_ε(P,Q)` for every test `φ`. The proof splits along a Hahn decomposition
of `P` against `e^ε Q`. -/
theorem integral_sub_le_hockeyStick (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (ε : ℝ) {φ : Ω → ℝ} (hφ : IsTest φ) :
    ∫ x, φ x ∂P - Real.exp ε * ∫ x, φ x ∂Q ≤ hockeyStick P Q ε := by
  set c : ℝ := Real.exp ε with hc
  have hc0 : 0 ≤ c := (Real.exp_pos ε).le
  set ν : Measure Ω := ENNReal.ofReal c • Q with hν
  have : IsFiniteMeasure ν := by
    constructor
    rw [hν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top Q _)
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition ν P
  have hsm : MeasurableSet s := hs.measurableSet
  have hiP := hφ.integrable P
  have hiν := hφ.integrable ν
  have hνint : ∫ x, φ x ∂ν = c * ∫ x, φ x ∂Q := by
    rw [hν, integral_smul_measure, ENNReal.toReal_ofReal hc0, smul_eq_mul]
  have hνs : ν.real s = c * (Q s).toReal := by
    rw [measureReal_def, hν, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc0]
  have h1 : ∫ x in sᶜ, φ x ∂P ≤ ∫ x in sᶜ, φ x ∂ν :=
    integral_mono_measure hs.ge_on_compl (ae_of_all _ fun x => (hφ.2 x).1) hiν.restrict
  have h2 : ∫ x in s, (1 - φ x) ∂ν ≤ ∫ x in s, (1 - φ x) ∂P :=
    integral_mono_measure hs.le_on (ae_of_all _ fun x => sub_nonneg.2 (hφ.2 x).2)
      (hφ.one_sub.integrable P).restrict
  have hsub : ∀ (μ : Measure Ω) [IsFiniteMeasure μ],
      ∫ x in s, (1 - φ x) ∂μ = μ.real s - ∫ x in s, φ x ∂μ := by
    intro μ _
    rw [integral_sub (integrable_const 1) (hφ.integrable μ).restrict, setIntegral_const,
      smul_eq_mul, mul_one]
  rw [hsub P, hsub ν] at h2
  have hP := integral_add_compl hsm hiP
  have hν' := integral_add_compl hsm hiν
  have key : ∫ x, φ x ∂P - ∫ x, φ x ∂ν ≤ P.real s - ν.real s := by linarith
  rw [hνint, hνs, measureReal_def] at key
  exact key.trans (le_hockeyStick ε hsm)

/-- The randomized-test form of a hockey-stick inequality used in `sec:composition`: if
`H_ε(P,Q) ≤ d` then `E_P φ - e^ε E_Q φ ≤ d` for every randomized test `φ`. -/
theorem integral_sub_le_of_hockeyStick_le {P Q : Measure Ω} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] {ε d : ℝ} (h : hockeyStick P Q ε ≤ d) {φ : Ω → ℝ} (hφ : IsTest φ) :
    ∫ x, φ x ∂P - Real.exp ε * ∫ x, φ x ∂Q ≤ d :=
  (integral_sub_le_hockeyStick P Q ε hφ).trans h

/-! ### The tradeoff lower bound -/

lemma tradeoff_bddBelow (P Q : Measure Ω) [IsProbabilityMeasure P] (a : ℝ) :
    BddBelow (range fun φ : {φ : Ω → ℝ // IsTest φ ∧ ∫ x, φ x ∂Q ≤ a} =>
      1 - ∫ x, φ.1 x ∂P) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨φ, rfl⟩
  have := φ.2.1.integral_le_one P
  simp only
  linarith

lemma tradeoff_le {P Q : Measure Ω} [IsProbabilityMeasure P] {a : ℝ} {φ : Ω → ℝ}
    (hφ : IsTest φ) (ha : ∫ x, φ x ∂Q ≤ a) : tradeoff P Q a ≤ 1 - ∫ x, φ x ∂P :=
  ciInf_le (tradeoff_bddBelow P Q a) ⟨φ, hφ, ha⟩

/-- The line inequalities of `thm:main` bound every test (`sec:composition`): if
`E_Q φ ≤ a` then `f(a) ≤ 1 - E_P φ`. -/
theorem envelope_le_one_sub_integral (L : List EnvLine) {P Q : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hL : ∀ l ∈ L, hockeyStick P Q (Real.log l.k) ≤ l.dplus ∧
      hockeyStick Q P (Real.log l.k) ≤ l.dminus)
    {φ : Ω → ℝ} (hφ : IsTest φ) {a : ℝ} (ha : ∫ x, φ x ∂Q ≤ a) :
    envelope L a ≤ 1 - ∫ x, φ x ∂P := by
  rw [envelope_le_iff]
  refine ⟨by linarith [hφ.integral_le_one P], fun l hl => ⟨?_, ?_⟩⟩
  · have hk := l.k_pos_real
    have h := integral_sub_le_of_hockeyStick_le (hL l hl).1 hφ
    rw [Real.exp_log hk] at h
    nlinarith
  · have hk := l.k_pos_real
    have h := integral_sub_le_of_hockeyStick_le (hL l hl).2 hφ.one_sub
    rw [Real.exp_log hk, hφ.integral_one_sub Q, hφ.integral_one_sub P] at h
    rw [div_le_iff₀ hk]
    nlinarith

/-- `T_{P,Q} ≥ f` on `[0,1]` (`sec:composition`). -/
theorem envelope_le_tradeoff (L : List EnvLine) {P Q : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hL : ∀ l ∈ L, hockeyStick P Q (Real.log l.k) ≤ l.dplus ∧
      hockeyStick Q P (Real.log l.k) ≤ l.dminus) :
    ∀ a ∈ Icc (0 : ℝ) 1, envelope L a ≤ tradeoff P Q a := by
  intro a ha
  have : Nonempty {φ : Ω → ℝ // IsTest φ ∧ ∫ x, φ x ∂Q ≤ a} :=
    ⟨⟨fun _ => 0, isTest_zero, by simpa using ha.1⟩⟩
  exact le_ciInf fun φ => envelope_le_one_sub_integral L hL φ.2.1 φ.2.2

/-! ### Forward and reverse divergences -/

lemma toReal_compl {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    (μ Aᶜ).toReal = 1 - (μ A).toReal := by
  simpa [measureReal_def] using probReal_compl_eq_one_sub (μ := μ) hA

lemma hockeyStick_swap_le_aux (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ε : ℝ) :
    hockeyStick Q P ε ≤ 1 - Real.exp ε + Real.exp ε * hockeyStick P Q (-ε) := by
  have he : 0 < Real.exp ε := Real.exp_pos ε
  have hee : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
  apply hockeyStick_le
  intro A hA
  have hid : (Q A).toReal - Real.exp ε * (P A).toReal =
      1 - Real.exp ε + Real.exp ε * ((P Aᶜ).toReal - Real.exp (-ε) * (Q Aᶜ).toReal) := by
    rw [toReal_compl hA, toReal_compl hA]
    linear_combination (1 - (Q A).toReal) * hee
  rw [hid]
  have h := mul_le_mul_of_nonneg_left (le_hockeyStick (P := P) (Q := Q) (-ε) hA.compl) he.le
  linarith

/-- The reverse divergence is a function of the forward one (`sec:model`):
`H_ε(Q,P) = 1 - e^ε + e^ε H_{-ε}(P,Q)` for probability measures. -/
theorem hockeyStick_swap (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ε : ℝ) : hockeyStick Q P ε = 1 - Real.exp ε + Real.exp ε * hockeyStick P Q (-ε) := by
  have he : 0 < Real.exp ε := Real.exp_pos ε
  have hee : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
  refine le_antisymm (hockeyStick_swap_le_aux P Q ε) ?_
  have h := hockeyStick_swap_le_aux Q P (-ε)
  rw [neg_neg] at h
  have h' := mul_le_mul_of_nonneg_left h he.le
  have hexp : Real.exp ε * (1 - Real.exp (-ε) + Real.exp (-ε) * hockeyStick Q P ε) =
      Real.exp ε - 1 + hockeyStick Q P ε := by
    linear_combination (hockeyStick Q P ε - 1) * hee
  linarith

/-- Forward dominance at every threshold gives reverse dominance (`sec:model`). The two pairs
may live on different spaces. -/
theorem hockeyStick_swap_le {Ω' : Type*} [MeasurableSpace Ω'] {P Q : Measure Ω}
    {R S : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] [IsProbabilityMeasure S]
    (h : ∀ ε, hockeyStick P Q ε ≤ hockeyStick R S ε) (ε : ℝ) :
    hockeyStick Q P ε ≤ hockeyStick S R ε := by
  rw [hockeyStick_swap P Q, hockeyStick_swap R S]
  have := mul_le_mul_of_nonneg_left (h (-ε)) (Real.exp_pos ε).le
  linarith

end Tests

/-! ### Subdivision nodes -/

/-- The crossing point of two pieces, the root of their difference (`0` when the slopes agree). -/
def cross (p q : ℚ × ℚ) : ℚ := (q.1 - p.1) / (q.2 - p.2)

/-- Subdivision nodes of `[0,1]`: `0`, `1` and every crossing of two pieces of the envelope
that lies in `[0,1]`. -/
def nodes (L : List EnvLine) : Finset ℚ :=
  (insert 0 (insert 1 (((pieces L).toFinset ×ˢ (pieces L).toFinset).image
    fun pq => cross pq.1 pq.2))).filter fun r => 0 ≤ r ∧ r ≤ 1

/-- Number of atoms of the envelope pair, equal to the number of nodes. -/
def numAtoms (L : List EnvLine) : ℕ := (nodes L).card

lemma card_nodes (L : List EnvLine) : (nodes L).card = numAtoms L := rfl

/-- The `j`-th node in increasing order (`a_j` in `sec:composition`), and `1` past the last
node. -/
def node (L : List EnvLine) (j : ℕ) : ℚ :=
  if h : j < numAtoms L then (nodes L).orderEmbOfFin (card_nodes L) ⟨j, h⟩ else 1

section Nodes

variable (L : List EnvLine)

lemma zero_mem_nodes : (0 : ℚ) ∈ nodes L := by simp [nodes]

lemma one_mem_nodes : (1 : ℚ) ∈ nodes L := by simp [nodes]

lemma nodes_bounds {r : ℚ} (hr : r ∈ nodes L) : 0 ≤ r ∧ r ≤ 1 := (Finset.mem_filter.1 hr).2

lemma cross_mem_nodes {p q : ℚ × ℚ} (hp : p ∈ pieces L) (hq : q ∈ pieces L)
    (h0 : 0 ≤ cross p q) (h1 : cross p q ≤ 1) : cross p q ∈ nodes L := by
  refine Finset.mem_filter.2 ⟨?_, h0, h1⟩
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_image.2 ⟨(p, q), ?_, rfl⟩))
  simp [hp, hq]

lemma two_le_numAtoms : 2 ≤ numAtoms L :=
  Finset.one_lt_card.2 ⟨0, zero_mem_nodes L, 1, one_mem_nodes L, by norm_num⟩

lemma node_of_lt {j : ℕ} (h : j < numAtoms L) :
    node L j = (nodes L).orderEmbOfFin (card_nodes L) ⟨j, h⟩ := by
  simp [node, h]

lemma node_mem {j : ℕ} (h : j < numAtoms L) : node L j ∈ nodes L := by
  rw [node_of_lt L h]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma node_bounds (j : ℕ) : 0 ≤ node L j ∧ node L j ≤ 1 := by
  by_cases h : j < numAtoms L
  · exact nodes_bounds L (node_mem L h)
  · simp [node, h]

lemma node_lt {i j : ℕ} (hij : i < j) (hj : j < numAtoms L) : node L i < node L j := by
  rw [node_of_lt L (hij.trans hj), node_of_lt L hj]
  exact ((nodes L).orderEmbOfFin (card_nodes L)).strictMono (Fin.mk_lt_mk.2 hij)

lemma node_mono {i j : ℕ} (hij : i ≤ j) : node L i ≤ node L j := by
  by_cases hj : j < numAtoms L
  · rcases eq_or_lt_of_le hij with rfl | h
    · exact le_rfl
    · exact (node_lt L h hj).le
  · simp only [node, hj, dite_false]
    exact (node_bounds L i).2

lemma node_zero : node L 0 = 0 := by
  have h2 := two_le_numAtoms L
  rw [node_of_lt L (by omega), Finset.orderEmbOfFin_zero (card_nodes L) (by omega)]
  exact le_antisymm (Finset.min'_le _ _ (zero_mem_nodes L))
    (nodes_bounds L (Finset.min'_mem _ _)).1

lemma node_last : node L (numAtoms L - 1) = 1 := by
  have h2 := two_le_numAtoms L
  rw [node_of_lt L (by omega), Finset.orderEmbOfFin_last (card_nodes L) (by omega)]
  exact le_antisymm (nodes_bounds L (Finset.max'_mem _ _)).2
    (Finset.le_max' _ _ (one_mem_nodes L))

/-- No node lies strictly between two consecutive nodes. -/
lemma node_gap (i : ℕ) {r : ℚ} (hr : r ∈ nodes L) :
    ¬ (node L i < r ∧ r < node L (i + 1)) := by
  rintro ⟨h1, h2⟩
  have hr' : r ∈ Set.range ((nodes L).orderEmbOfFin (card_nodes L)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hr
  obtain ⟨⟨m, hm⟩, rfl⟩ := hr'
  rw [← node_of_lt L hm] at h1 h2
  have a1 : i < m := by
    by_contra h
    exact absurd (node_mono L (not_lt.1 h)) (not_le.2 h1)
  have a2 : m < i + 1 := by
    by_contra h
    exact absurd (node_mono L (not_lt.1 h)) (not_le.2 h2)
  omega

end Nodes

/-! ### The envelope is affine between consecutive nodes -/

section Affine

variable (L : List EnvLine)

/-- If no node lies strictly inside `[u, v] ⊆ [0,1]`, a single piece equals the envelope on
`[u, v]`. Two pieces can exchange the maximum only at a crossing, and every crossing in `[0,1]`
is a node. -/
lemma envelope_affine_on_gap {u v : ℚ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hgap : ∀ r ∈ nodes L, ¬ (u < r ∧ r < v)) :
    ∃ p ∈ pieces L, ∀ t : ℝ, (u : ℝ) ≤ t → t ≤ v → envelope L t = pval p t := by
  have huv' : (u : ℝ) < v := by exact_mod_cast huv
  set m : ℝ := ((u : ℝ) + v) / 2 with hm
  obtain ⟨p, hp, hpm⟩ := exists_pval_eq_envelope L m
  refine ⟨p, hp, fun t ht1 ht2 => le_antisymm ?_ (pval_le_envelope hp t)⟩
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨q, hq, hqt⟩ := exists_pval_eq_envelope L t
  have hqm : pval q m ≤ pval p m := hpm ▸ pval_le_envelope hq m
  have hqt' : pval p t < pval q t := hqt ▸ hlt
  have hne : (q.2 : ℝ) - p.2 ≠ 0 := by
    intro h
    have h' : (q.2 : ℝ) = p.2 := by linarith
    simp only [pval, h'] at hqm hqt'
    linarith
  set c : ℝ := (q.2 : ℝ) - p.2 with hc
  set r : ℝ := ((q.1 : ℝ) - p.1) / c with hr
  have hD : ∀ s : ℝ, pval q s - pval p s = c * (r - s) := by
    intro s
    simp only [pval, hr]
    field_simp
    ring
  have hcast : ((cross p q : ℚ) : ℝ) = r := by
    simp only [cross, hr, hc]
    push_cast
    rfl
  have e1 := hD m
  have e2 := hD t
  have hrange : (u : ℝ) < r ∧ r < v := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hrm : m ≤ r := by nlinarith
      have hrt : r < t := by nlinarith
      constructor <;> linarith
    · have hrm : r ≤ m := by nlinarith
      have hrt : t < r := by nlinarith
      constructor <;> linarith
  rw [← hcast] at hrange
  have hur : u < cross p q := by exact_mod_cast hrange.1
  have hrv : cross p q < v := by exact_mod_cast hrange.2
  exact hgap _ (cross_mem_nodes L hp hq (hu.trans hur.le) (hrv.le.trans hv)) ⟨hur, hrv⟩

lemma envelope_affine_on_atom {i : ℕ} (hi : i + 1 < numAtoms L) :
    ∃ p ∈ pieces L, ∀ t : ℝ, (node L i : ℝ) ≤ t → t ≤ node L (i + 1) →
      envelope L t = pval p t :=
  envelope_affine_on_gap L (node_bounds L i).1 (node_lt L (Nat.lt_succ_self i) hi)
    (node_bounds L (i + 1)).2 fun _ hr => node_gap L i hr

end Affine

/-! ### The finite pair of `eq:atoms` -/

/-- `S`-masses of `eq:atoms`. Atom `0` is the `R`-only atom; atom `i ≥ 1` carries the interval
`[a_{i-1}, a_i]` and has `S`-mass `a_i - a_{i-1}`. -/
def envS (L : List EnvLine) (i : ℕ) : ℚ :=
  if i = 0 then 0 else node L i - node L (i - 1)

/-- `R`-masses of `eq:atoms`: `1 - f(0)` on the `R`-only atom and `f(a_{i-1}) - f(a_i)` on atom
`i ≥ 1`, which is `t_i (a_i - a_{i-1})` for the slope `-t_i` of `f` there
(`envR_eq_slope_mul_envS`). -/
def envR (L : List EnvLine) (i : ℕ) : ℚ :=
  if i = 0 then 1 - envelopeQ L 0 else envelopeQ L (node L (i - 1)) - envelopeQ L (node L i)

/-- The Neyman-Pearson test of the envelope pair at `S`-level `a`: it accepts the `R`-only atom,
accepts every interval atom to the left of `a` and randomizes on the atom containing `a`. -/
noncomputable def npTest (L : List EnvLine) (a : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 1 else
    (min a (node L i : ℝ) - min a (node L (i - 1) : ℝ)) / ((node L i : ℝ) - node L (i - 1))

section Pair

variable (L : List EnvLine)

lemma envS_zero : envS L 0 = 0 := rfl

lemma envS_succ (i : ℕ) : (envS L (i + 1) : ℝ) = (node L (i + 1) : ℝ) - node L i := by
  simp [envS]

lemma envR_zero : (envR L 0 : ℝ) = 1 - envelope L 0 := by
  simp [envR, envelopeQ_cast]

lemma envR_succ (i : ℕ) :
    (envR L (i + 1) : ℝ) = envelope L (node L i) - envelope L (node L (i + 1)) := by
  simp [envR, envelopeQ_cast]

lemma npTest_zero (a : ℝ) : npTest L a 0 = 1 := rfl

lemma npTest_succ (a : ℝ) (i : ℕ) : npTest L a (i + 1) =
    (min a (node L (i + 1) : ℝ) - min a (node L i : ℝ)) / ((node L (i + 1) : ℝ) - node L i) := by
  simp [npTest]

lemma exists_numAtoms_eq : ∃ N, numAtoms L = N + 1 ∧ node L N = 1 := by
  have h2 := two_le_numAtoms L
  refine ⟨numAtoms L - 1, by omega, node_last L⟩

lemma node_lt_succ {i : ℕ} (hi : i + 1 < numAtoms L) : (node L i : ℝ) < node L (i + 1) := by
  exact_mod_cast node_lt L (Nat.lt_succ_self i) hi

theorem envS_nonneg (i : ℕ) : 0 ≤ envS L i := by
  rcases i with _ | i
  · exact le_rfl
  · simp only [envS, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    exact sub_nonneg.2 (node_mono L (Nat.le_succ i))

theorem envR_nonneg (i : ℕ) : 0 ≤ envR L i := by
  have h : (0 : ℝ) ≤ envR L i := by
    rcases i with _ | i
    · rw [envR_zero]
      linarith [envelope_zero_le_one L]
    · rw [envR_succ]
      exact sub_nonneg.2 (envelope_antitone L (by exact_mod_cast node_mono L (Nat.le_succ i)))
  exact_mod_cast h

theorem sum_envS : ∑ i ∈ Finset.range (numAtoms L), (envS L i : ℝ) = 1 := by
  obtain ⟨N, hN, hlast⟩ := exists_numAtoms_eq L
  rw [hN, Finset.sum_range_succ']
  simp only [envS_succ, envS_zero, Rat.cast_zero, add_zero]
  rw [Finset.sum_range_sub (fun j => (node L j : ℝ)) N, hlast, node_zero]
  simp

theorem sum_envR : ∑ i ∈ Finset.range (numAtoms L), (envR L i : ℝ) = 1 := by
  obtain ⟨N, hN, hlast⟩ := exists_numAtoms_eq L
  rw [hN, Finset.sum_range_succ']
  simp only [envR_succ, envR_zero]
  rw [Finset.sum_range_sub' (fun j => envelope L (node L j)) N, hlast, node_zero]
  simp [envelope_one]

lemma npTest_mem (a : ℝ) {i : ℕ} (hi : i < numAtoms L) : 0 ≤ npTest L a i ∧ npTest L a i ≤ 1 := by
  rcases i with _ | i
  · simp [npTest_zero]
  · rw [npTest_succ]
    have hlt := node_lt_succ L hi
    set u : ℝ := ((node L i : ℚ) : ℝ)
    set v : ℝ := ((node L (i + 1) : ℚ) : ℝ)
    have hd : 0 < v - u := sub_pos.2 hlt
    constructor
    · apply div_nonneg _ hd.le
      exact sub_nonneg.2 (min_le_min_left a hlt.le)
    · rw [div_le_one hd]
      rcases le_total a u with h | h
      · rw [min_eq_left h, min_eq_left (h.trans hlt.le)]
        linarith
      · rw [min_eq_right h]
        rcases le_total a v with h' | h'
        · rw [min_eq_left h']
          linarith
        · rw [min_eq_right h']

theorem sum_envS_npTest {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∑ i ∈ Finset.range (numAtoms L), (envS L i : ℝ) * npTest L a i = a := by
  obtain ⟨N, hN, hlast⟩ := exists_numAtoms_eq L
  rw [hN, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range N, (envS L (i + 1) : ℝ) * npTest L a (i + 1) =
      min a (node L (i + 1) : ℝ) - min a (node L i : ℝ) := by
    intro i hi
    have hlt := node_lt_succ L (i := i) (by rw [hN]; simpa using hi)
    rw [envS_succ, npTest_succ]
    field_simp [(sub_pos.2 hlt).ne']
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j => min a (node L j : ℝ)) N,
    hlast, node_zero]
  simp [envS_zero, min_eq_left ha1, min_eq_right ha0]

theorem sum_envR_npTest {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∑ i ∈ Finset.range (numAtoms L), (envR L i : ℝ) * npTest L a i = 1 - envelope L a := by
  obtain ⟨N, hN, hlast⟩ := exists_numAtoms_eq L
  rw [hN, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range N, (envR L (i + 1) : ℝ) * npTest L a (i + 1) =
      envelope L (min a (node L i : ℝ)) - envelope L (min a (node L (i + 1) : ℝ)) := by
    intro i hi
    have hi' : i + 1 < numAtoms L := by rw [hN]; simpa using hi
    have hlt := node_lt_succ L hi'
    obtain ⟨p, -, hp⟩ := envelope_affine_on_atom L hi'
    rw [envR_succ, npTest_succ]
    set u : ℝ := ((node L i : ℚ) : ℝ)
    set v : ℝ := ((node L (i + 1) : ℚ) : ℝ)
    have hu := hp u le_rfl hlt.le
    have hv := hp v hlt.le le_rfl
    rw [hu, hv]
    have hd : v - u ≠ 0 := (sub_pos.2 hlt).ne'
    rcases le_total a u with h | h
    · rw [min_eq_left h, min_eq_left (h.trans hlt.le)]
      simp
    · rw [min_eq_right h, hp _ (le_min h hlt.le) (min_le_right _ _), hu]
      simp only [pval]
      field_simp
      ring
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_range_sub' (fun j => envelope L (min a (node L j : ℝ))) N, hlast, node_zero]
  simp [envR_zero, npTest_zero, min_eq_left ha1, min_eq_right ha0]

/-- On each interval atom `R = t S`, where `-t ≤ 0` is the slope of the envelope on that interval
(`eq:atoms`). -/
theorem envR_eq_slope_mul_envS {i : ℕ} (hi : i + 1 < numAtoms L) :
    ∃ t : ℝ, 0 ≤ t ∧ (envR L (i + 1) : ℝ) = t * envS L (i + 1) ∧
      ∀ s : ℝ, (node L i : ℝ) ≤ s → s ≤ node L (i + 1) →
        envelope L s = envelope L (node L i) - t * (s - node L i) := by
  have hlt := node_lt_succ L hi
  obtain ⟨p, hp, hpe⟩ := envelope_affine_on_atom L hi
  refine ⟨p.2, pieces_slope_nonneg hp, ?_, fun s hs1 hs2 => ?_⟩
  · rw [envR_succ, envS_succ, hpe _ le_rfl hlt.le, hpe _ hlt.le le_rfl]
    simp only [pval]
    ring
  · rw [hpe s hs1 hs2, hpe _ le_rfl hlt.le]
    simp only [pval]
    ring

/-- Positive drops along a sequence that is quasi-convex on `0, …, N` add up to at most
`H 0 - H m` for some `m`. -/
lemma sum_drop_le (H : ℕ → ℝ) (N : ℕ)
    (hq : ∀ i j k, i < j → j < k → k ≤ N → H j ≤ max (H i) (H k)) :
    ∀ M ≤ N, ∃ m ≤ M, ∑ j ∈ Finset.range M, max 0 (H j - H (j + 1)) ≤ H 0 - H m := by
  intro M
  induction M with
  | zero => exact fun _ => ⟨0, le_rfl, by simp⟩
  | succ M ih =>
    intro hM
    obtain ⟨m, hm, hsum⟩ := ih (by omega)
    rw [Finset.sum_range_succ]
    by_cases hdrop : H M ≤ H (M + 1)
    · refine ⟨m, by omega, ?_⟩
      rw [max_eq_left (by linarith)]
      linarith
    · replace hdrop := not_le.1 hdrop
      have hMm : H M ≤ H m := by
        rcases eq_or_lt_of_le hm with h | h
        · rw [h]
        · have := hq m M (M + 1) h (by omega) hM
          rcases max_cases (H m) (H (M + 1)) with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
      refine ⟨M + 1, le_rfl, ?_⟩
      rw [max_eq_right (by linarith)]
      linarith

/-- For a piece `a ↦ α - β a` of the envelope, `∑ᵢ (Rᵢ - β Sᵢ)₊ ≤ 1 - α` on the envelope pair. -/
lemma sum_posPart_le {p : ℚ × ℚ} (hp : p ∈ pieces L) :
    ∑ i ∈ Finset.range (numAtoms L), max 0 ((envR L i : ℝ) - p.2 * envS L i) ≤ 1 - p.1 := by
  obtain ⟨N, hN, hlast⟩ := exists_numAtoms_eq L
  set H : ℕ → ℝ := fun j => envelope L (node L j) + p.2 * node L j - p.1 with hH
  have hterm : ∀ i ∈ Finset.range N, max 0 ((envR L (i + 1) : ℝ) - p.2 * envS L (i + 1)) =
      max 0 (H i - H (i + 1)) := by
    intro i _
    rw [envR_succ, envS_succ]
    congr 1
    simp only [hH]
    ring
  have hconv : ConvexOn ℝ univ fun t => envelope L t + (p.2 : ℝ) * t :=
    (envelope_convexOn_univ L).add
      ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  have hq : ∀ i j k, i < j → j < k → k ≤ N → H j ≤ max (H i) (H k) := by
    intro i j k hij hjk hkN
    have hk : k < numAtoms L := by omega
    have hseg : (node L j : ℝ) ∈ segment ℝ (node L i : ℝ) (node L k : ℝ) := by
      rw [segment_eq_Icc (by exact_mod_cast (node_lt L (hij.trans hjk) hk).le)]
      exact ⟨by exact_mod_cast (node_lt L hij (hjk.trans hk)).le,
        by exact_mod_cast (node_lt L hjk hk).le⟩
    have := hconv.le_on_segment (mem_univ _) (mem_univ _) hseg
    simp only [hH]
    rw [max_sub_sub_right]
    linarith
  obtain ⟨m, -, hm⟩ := sum_drop_le H N hq N le_rfl
  have hHm : 0 ≤ H m := by
    have := pval_le_envelope hp (node L m)
    simp only [pval] at this
    simp only [hH]
    linarith
  have hH0 : H 0 = envelope L 0 - p.1 := by simp [hH, node_zero]
  rw [hN, Finset.sum_range_succ', Finset.sum_congr rfl hterm, envR_zero, envS_zero,
    Rat.cast_zero, mul_zero, sub_zero, max_eq_right (by linarith [envelope_zero_le_one L])]
  linarith

/-- The envelope pair satisfies `T ≥ f` for randomized tests, written with atom sums. -/
lemma envelope_le_one_sub_sum {φ : ℕ → ℝ} (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ 1) {a : ℝ}
    (ha : ∑ i ∈ Finset.range (numAtoms L), (envS L i : ℝ) * φ i ≤ a) :
    envelope L a ≤ 1 - ∑ i ∈ Finset.range (numAtoms L), (envR L i : ℝ) * φ i := by
  set y := ∑ i ∈ Finset.range (numAtoms L), (envS L i : ℝ) * φ i with hy
  obtain ⟨p, hp, hpy⟩ := exists_pval_eq_envelope L y
  have hfa : envelope L a ≤ envelope L y := envelope_antitone L ha
  have hsplit : ∑ i ∈ Finset.range (numAtoms L), (envR L i : ℝ) * φ i - p.2 * y =
      ∑ i ∈ Finset.range (numAtoms L), ((envR L i : ℝ) - p.2 * envS L i) * φ i := by
    rw [hy, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hle : ∑ i ∈ Finset.range (numAtoms L), ((envR L i : ℝ) - p.2 * envS L i) * φ i ≤
      ∑ i ∈ Finset.range (numAtoms L), max 0 ((envR L i : ℝ) - p.2 * envS L i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, h1⟩ := hφ i
    rcases le_total 0 ((envR L i : ℝ) - p.2 * envS L i) with hx | hx
    · rw [max_eq_right hx]
      nlinarith
    · exact (mul_nonpos_of_nonpos_of_nonneg hx h0).trans (le_max_left _ _)
  have := sum_posPart_le L hp
  simp only [pval] at hpy
  linarith

end Pair

/-! ### Integrals against `finMeasure` -/

lemma integral_finMeasure {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (φ : Fin n → ℝ) :
    ∫ i, φ i ∂(finMeasure w) = ∑ i, w i * φ i := by
  rw [finMeasure, integral_finsetSum_measure fun i _ =>
    Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

lemma isProbabilityMeasure_finMeasure {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) : IsProbabilityMeasure (finMeasure w) := by
  constructor
  rw [finMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw i, h1, ENNReal.ofReal_one]

/-! ### Tradeoff and dominance of the envelope pair -/

section Main

variable (L : List EnvLine)

lemma sum_fin_envR : ∑ i : Fin (numAtoms L), (envR L i : ℝ) = 1 :=
  (Fin.sum_univ_eq_sum_range (fun j => (envR L j : ℝ)) _).trans (sum_envR L)

lemma sum_fin_envS : ∑ i : Fin (numAtoms L), (envS L i : ℝ) = 1 :=
  (Fin.sum_univ_eq_sum_range (fun j => (envS L j : ℝ)) _).trans (sum_envS L)

instance : IsProbabilityMeasure (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ)) :=
  isProbabilityMeasure_finMeasure (fun i => by exact_mod_cast envR_nonneg L i) (sum_fin_envR L)

instance : IsProbabilityMeasure (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) :=
  isProbabilityMeasure_finMeasure (fun i => by exact_mod_cast envS_nonneg L i) (sum_fin_envS L)

lemma isTest_npTest (a : ℝ) : IsTest fun i : Fin (numAtoms L) => npTest L a i :=
  ⟨measurable_of_finite _, fun i => npTest_mem L a i.2⟩

lemma integral_envS_npTest {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ i, npTest L a i ∂(finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) = a := by
  rw [integral_finMeasure fun i => by exact_mod_cast envS_nonneg L i]
  exact (Fin.sum_univ_eq_sum_range (fun j => (envS L j : ℝ) * npTest L a j) _).trans
    (sum_envS_npTest L ha0 ha1)

lemma integral_envR_npTest {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ i, npTest L a i ∂(finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ)) =
      1 - envelope L a := by
  rw [integral_finMeasure fun i => by exact_mod_cast envR_nonneg L i]
  exact (Fin.sum_univ_eq_sum_range (fun j => (envR L j : ℝ) * npTest L a j) _).trans
    (sum_envR_npTest L ha0 ha1)

/-- The envelope pair has testing tradeoff exactly `f` on `[0,1]` (`sec:composition`). -/
theorem envPair_tradeoff :
    ∀ a ∈ Icc (0 : ℝ) 1,
      tradeoff (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ))
        (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) a = envelope L a := by
  rintro a ⟨ha0, ha1⟩
  apply le_antisymm
  · calc _ ≤ 1 - ∫ i, npTest L a i
          ∂(finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ)) :=
          tradeoff_le (isTest_npTest L a) (integral_envS_npTest L ha0 ha1).le
      _ = envelope L a := by rw [integral_envR_npTest L ha0 ha1]; ring
  · have : Nonempty {φ : Fin (numAtoms L) → ℝ // IsTest φ ∧
        ∫ i, φ i ∂(finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) ≤ a} :=
      ⟨⟨_, isTest_npTest L a, (integral_envS_npTest L ha0 ha1).le⟩⟩
    refine le_ciInf fun φ => ?_
    obtain ⟨φ, hφ, hφa⟩ := φ
    set ψ : ℕ → ℝ := fun j => if h : j < numAtoms L then φ ⟨j, h⟩ else 0 with hψ
    have hψφ : ∀ i : Fin (numAtoms L), ψ i = φ i := fun i => by simp [hψ, i.2]
    have hψ01 : ∀ j, 0 ≤ ψ j ∧ ψ j ≤ 1 := by
      intro j
      by_cases h : j < numAtoms L
      · simpa [hψ, h] using hφ.2 ⟨j, h⟩
      · simp [hψ, h]
    have hsum : ∀ w : ℕ → ℚ, (∀ i, 0 ≤ w i) →
        ∫ i, φ i ∂(finMeasure fun i : Fin (numAtoms L) => (w i : ℝ)) =
          ∑ j ∈ Finset.range (numAtoms L), (w j : ℝ) * ψ j := by
      intro w hw
      rw [integral_finMeasure fun i => by exact_mod_cast hw i]
      rw [← Fin.sum_univ_eq_sum_range (fun j => (w j : ℝ) * ψ j)]
      exact Finset.sum_congr rfl fun i _ => by rw [hψφ]
    rw [hsum _ (envS_nonneg L)] at hφa
    simp only
    rw [hsum _ (envR_nonneg L)]
    exact envelope_le_one_sub_sum L hψ01 hφa

/-- The envelope pair dominates every pair that satisfies the line inequalities, in both
directions and at every real threshold (`thm:main`, `sec:composition`). -/
theorem envPair_dominates {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hL : ∀ l ∈ L, hockeyStick P Q (Real.log l.k) ≤ l.dplus ∧
      hockeyStick Q P (Real.log l.k) ≤ l.dminus) (ε : ℝ) :
    hockeyStick P Q ε ≤ hockeyStick (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ))
        (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) ε ∧
      hockeyStick Q P ε ≤ hockeyStick (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ))
        (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ)) ε := by
  have hfwd : ∀ ε, hockeyStick P Q ε ≤
      hockeyStick (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ))
        (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) ε := by
    intro ε
    apply hockeyStick_le
    intro A hA
    set a := (Q A).toReal with ha
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have ha1 : a ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    have hint : ∀ μ : Measure Ω, ∫ x, A.indicator 1 x ∂μ = (μ A).toReal := fun μ => by
      rw [integral_indicator_one hA, measureReal_def]
    have hPA := envelope_le_one_sub_integral L hL (isTest_indicator hA) (a := a) (hint Q).le
    rw [hint P] at hPA
    have hfin := integral_sub_le_hockeyStick
      (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ))
      (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) ε (isTest_npTest L a)
    rw [integral_envR_npTest L ha0 ha1, integral_envS_npTest L ha0 ha1] at hfin
    linarith
  exact ⟨hfwd ε, hockeyStick_swap_le hfwd ε⟩

end Main

/-- The explicit envelope pair of `eq:atoms` has nonnegative rational masses summing to one under
each law, has testing tradeoff `f` on `[0,1]`, and dominates in both directions every pair of
probability measures satisfying the line inequalities (`thm:main`, `sec:composition`). -/
theorem envPair_spec (L : List EnvLine) :
    (∀ i : Fin (numAtoms L), 0 ≤ envR L i) ∧ (∀ i : Fin (numAtoms L), 0 ≤ envS L i) ∧
      ∑ i : Fin (numAtoms L), envR L i = 1 ∧ ∑ i : Fin (numAtoms L), envS L i = 1 ∧
      (∀ a ∈ Icc (0 : ℝ) 1, tradeoff (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ))
        (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) a = envelope L a) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
        [IsProbabilityMeasure Q],
        (∀ l ∈ L, hockeyStick P Q (Real.log l.k) ≤ l.dplus ∧
          hockeyStick Q P (Real.log l.k) ≤ l.dminus) →
        ∀ ε : ℝ,
          hockeyStick P Q ε ≤ hockeyStick (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ))
            (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ)) ε ∧
          hockeyStick Q P ε ≤ hockeyStick (finMeasure fun i : Fin (numAtoms L) => (envS L i : ℝ))
            (finMeasure fun i : Fin (numAtoms L) => (envR L i : ℝ)) ε := by
  refine ⟨fun i => envR_nonneg L i, fun i => envS_nonneg L i, ?_, ?_, envPair_tradeoff L,
    fun P Q _ _ hL ε => envPair_dominates L P Q hL ε⟩
  · exact_mod_cast sum_fin_envR L
  · exact_mod_cast sum_fin_envS L

/-- First claim of `thm:main`: there is a finite pair `(R, S)` with rational masses whose testing
tradeoff is the envelope `f` of `eq:envelope` on `[0,1]` and which dominates, in both directions,
every pair of probability measures satisfying the line inequalities. The pair depends only on
the lines. -/
theorem envelope_pair_exists (L : List EnvLine) :
    ∃ (n : ℕ) (R S : Fin n → ℚ), (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ S i) ∧ ∑ i, R i = 1 ∧
      ∑ i, S i = 1 ∧
      (∀ a ∈ Icc (0 : ℝ) 1, tradeoff (finMeasure fun i => (R i : ℝ))
        (finMeasure fun i => (S i : ℝ)) a = envelope L a) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
        [IsProbabilityMeasure Q],
        (∀ l ∈ L, hockeyStick P Q (Real.log l.k) ≤ l.dplus ∧
          hockeyStick Q P (Real.log l.k) ≤ l.dminus) →
        ∀ ε : ℝ, hockeyStick P Q ε ≤ hockeyStick (finMeasure fun i => (R i : ℝ))
            (finMeasure fun i => (S i : ℝ)) ε ∧
          hockeyStick Q P ε ≤ hockeyStick (finMeasure fun i => (S i : ℝ))
            (finMeasure fun i => (R i : ℝ)) ε :=
  ⟨numAtoms L, fun i => envR L i, fun i => envS L i, envPair_spec L⟩

end ASGA
