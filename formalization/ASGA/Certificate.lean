import ASGA.Basic

/-!
# Soundness of the finite certificate computations

This module proves the mathematical steps of `app:certificate` that let a finite
computation bound the continuous quantities of the paper.

* Endpoint spreads (`eq:spread`, and the Poisson spread of the last subsection of
  `app:certificate`) have nonnegative masses with the bin's mass and first moment, and
  they dominate the bin law in convex order.
* The call and put functions `F_m`, `J_m` of `eq:recurrences` are convex and satisfy the
  boundary identities used by the directed convolution. Node arrays that dominate the
  chord recursion dominate `F_m` and `J_m` at every node, for a finite law of the summand.
  The recursion agrees with the expectation over independent draws, both for finite laws
  and for laws with finite mean.
* Moving rounded-away probability to the largest or smallest support point gives
  conservative expectations for monotone functions, hence larger `F_m` and `J_m`.
* The positive-part Lipschitz inequality gives the tail correction of `eq:tau`.
* These steps combine into `certificate_call_sound` and `certificate_put_sound`.
* The upper profile `eq:upperpld` and the lower profile of the maximum statistic bound
  the hockey-stick divergence of a finite pair. Lower submeasures survive convolution,
  downward rounding and cropping, so both bounds hold for the `E`-fold product pair.
* Exact integer packing in bases `2^128` and `2^192` has no carries.
* The decimal ratios quoted in `sec:evaluation` and the introduction are checked.
-/

open MeasureTheory

namespace ASGA

/-! ## Endpoint spreads and convex order -/

section Spread

/-- Lower endpoint mass `w_l = (v p - u) / (v - l)` of `eq:spread`. -/
noncomputable def spreadLow (l v p u : ℝ) : ℝ := (v * p - u) / (v - l)

/-- Upper endpoint mass `w_v = (u - l p) / (v - l)` of `eq:spread`. -/
noncomputable def spreadHigh (l v p u : ℝ) : ℝ := (u - l * p) / (v - l)

variable {l v p u : ℝ}

theorem spreadLow_nonneg (hlv : l < v) (hu : u ≤ v * p) : 0 ≤ spreadLow l v p u :=
  div_nonneg (by linarith) (by linarith)

theorem spreadHigh_nonneg (hlv : l < v) (hu : l * p ≤ u) : 0 ≤ spreadHigh l v p u :=
  div_nonneg (by linarith) (by linarith)

theorem spreadLow_add_spreadHigh (hlv : l < v) :
    spreadLow l v p u + spreadHigh l v p u = p := by
  have h : v - l ≠ 0 := by linarith
  unfold spreadLow spreadHigh
  field_simp
  ring

theorem spread_first_moment (hlv : l < v) :
    l * spreadLow l v p u + v * spreadHigh l v p u = u := by
  have h : v - l ≠ 0 := by linarith
  unfold spreadLow spreadHigh
  field_simp
  ring

/-- The endpoint masses of `eq:spread` are nonnegative, sum to `p`, and preserve the first
moment `u`, whenever `l < v` and `l p ≤ u ≤ v p`. -/
theorem spread_masses (hlv : l < v) (h1 : l * p ≤ u) (h2 : u ≤ v * p) :
    0 ≤ spreadLow l v p u ∧ 0 ≤ spreadHigh l v p u ∧
      spreadLow l v p u + spreadHigh l v p u = p ∧
      l * spreadLow l v p u + v * spreadHigh l v p u = u :=
  ⟨spreadLow_nonneg hlv h2, spreadHigh_nonneg hlv h1, spreadLow_add_spreadHigh hlv,
    spread_first_moment hlv⟩

/-- The chord inequality: on `[a, b]` a convex function lies below the chord through
any upper bounds `Ua ≥ f a`, `Ub ≥ f b` of its endpoint values. -/
theorem le_chord_of_convexOn {f : ℝ → ℝ} {a b t Ua Ub : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hab : a < b) (ht : t ∈ Set.Icc a b)
    (ha : f a ≤ Ua) (hb : f b ≤ Ub) :
    f t ≤ ((b - t) * Ua + (t - a) * Ub) / (b - a) := by
  have hba : 0 < b - a := by linarith
  have hwa : 0 ≤ (b - t) / (b - a) := div_nonneg (by linarith [ht.2]) hba.le
  have hwb : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) hba.le
  have hsum : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
    field_simp
    ring
  have hpt : ((b - t) / (b - a)) • a + ((t - a) / (b - a)) • b = t := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have hconv := hf.2 (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le) hwa hwb hsum
  rw [hpt] at hconv
  simp only [smul_eq_mul] at hconv
  calc f t ≤ (b - t) / (b - a) * f a + (t - a) / (b - a) * f b := hconv
    _ ≤ (b - t) / (b - a) * Ua + (t - a) / (b - a) * Ub := by gcongr
    _ = ((b - t) * Ua + (t - a) * Ub) / (b - a) := by
      field_simp

/-- A function convex on `[l, v]` is integrable against any finite measure concentrated on
`[l, v]`: it is continuous on `(l, v)` and bounded on `[l, v]`. -/
theorem integrable_of_convexOn_Icc {ν : Measure ℝ} [IsFiniteMeasure ν] {φ : ℝ → ℝ}
    (hlv : l < v) (hsupp : ν (Set.Icc l v)ᶜ = 0) (hφ : ConvexOn ℝ (Set.Icc l v) φ) :
    Integrable φ ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc l v := ae_iff.2 hsupp
  have hmeas : AEStronglyMeasurable φ ν := by
    have hcont : ContinuousOn φ (Set.Ioo l v) := by
      have h := hφ.continuousOn_interior
      rwa [interior_Icc] at h
    rw [← Measure.restrict_univ (μ := ν), ← Set.union_compl_self (Set.Ioo l v),
      aestronglyMeasurable_union_iff]
    refine ⟨hcont.aestronglyMeasurable measurableSet_Ioo, ?_⟩
    have hg : Measurable fun x : ℝ => if x = l then φ l else φ v :=
      Measurable.ite (measurableSet_singleton l) measurable_const measurable_const
    refine hg.aestronglyMeasurable.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo.compl]
    filter_upwards [hae] with x hx hxc
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      simp
    · have hxv : x = v := by
        by_contra hne
        exact hxc ⟨h, lt_of_le_of_ne hx.2 hne⟩
      subst hxv
      simp [hlv.ne']
  set M := max (φ l) (φ v)
  set c := (l + v) / 2
  have hup : ∀ x ∈ Set.Icc l v, φ x ≤ M := by
    intro x hx
    have h := le_chord_of_convexOn hφ hlv hx (le_max_left (φ l) (φ v)) (le_max_right (φ l) (φ v))
    have hvl : v - l ≠ 0 := by linarith
    have heq : ((v - x) * M + (x - l) * M) / (v - l) = M := by
      field_simp
      ring
    linarith
  have hc : c ∈ Set.Icc l v := ⟨by simp only [c]; linarith, by simp only [c]; linarith⟩
  have hlow : ∀ x ∈ Set.Icc l v, 2 * φ c - M ≤ φ x := by
    intro x hx
    have hx' : l + v - x ∈ Set.Icc l v := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := hφ.2 hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have hpt : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (l + v - x) = c := by
      simp only [smul_eq_mul, c]
      ring
    rw [hpt] at h
    simp only [smul_eq_mul] at h
    linarith [hup _ hx']
  refine Integrable.mono' (integrable_const (|M| + |2 * φ c - M|)) hmeas ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [hlow x hx, neg_abs_le (2 * φ c - M), abs_nonneg M]
  · linarith [hup x hx, le_abs_self M, abs_nonneg (2 * φ c - M)]

/-- Convex-order domination by the endpoint spread (`eq:spread`): a finite measure `ν`
on `[l, v]` with mass `p` and first moment `u` integrates every function convex on
`[l, v]` to at most its value under the two-point law `w_l δ_l + w_v δ_v`. -/
theorem integral_le_spread {ν : Measure ℝ} [IsFiniteMeasure ν] {φ : ℝ → ℝ}
    (hlv : l < v) (hsupp : ν (Set.Icc l v)ᶜ = 0) (hp : ν.real Set.univ = p)
    (hu : ∫ x, x ∂ν = u) (hφ : ConvexOn ℝ (Set.Icc l v) φ) :
    ∫ x, φ x ∂ν ≤ spreadLow l v p u * φ l + spreadHigh l v p u * φ v := by
  have hint : Integrable φ ν := integrable_of_convexOn_Icc hlv hsupp hφ
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc l v := ae_iff.2 hsupp
  have hid : Integrable (fun x : ℝ => x) ν := by
    refine Integrable.mono' (integrable_const (|l| + |v|)) aestronglyMeasurable_id ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hx.1, neg_abs_le l, abs_nonneg v]
    · linarith [hx.2, le_abs_self v, abs_nonneg l]
  set A := (v * φ l - l * φ v) / (v - l)
  set B := (φ v - φ l) / (v - l)
  have hchord : ∀ x, ((v - x) * φ l + (x - l) * φ v) / (v - l) = A + B * x := by
    intro x
    simp only [A, B]
    field_simp
    ring
  have hlin : Integrable (fun x : ℝ => A + B * x) ν :=
    (integrable_const A).add (hid.const_mul B)
  calc ∫ x, φ x ∂ν ≤ ∫ x, (A + B * x) ∂ν := by
        refine integral_mono_ae hint hlin ?_
        filter_upwards [hae] with x hx
        rw [← hchord]
        exact le_chord_of_convexOn hφ hlv hx le_rfl le_rfl
    _ = A * p + B * u := by
        rw [integral_add (integrable_const A) (hid.const_mul B), integral_const,
          integral_const_mul, hu, hp, smul_eq_mul, mul_comm]
    _ = spreadLow l v p u * φ l + spreadHigh l v p u * φ v := by
        simp only [A, B, spreadLow, spreadHigh]
        field_simp
        ring

/-- For a bin law `ν` on `[l, v]` with mass `p` and first moment `u`, the moment satisfies
`l p ≤ u ≤ v p`, so the endpoint masses of `eq:spread` are those of `spread_masses`. -/
theorem spread_moment_bounds {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν (Set.Icc l v)ᶜ = 0)
    (hp : ν.real Set.univ = p) (hu : ∫ x, x ∂ν = u) : l * p ≤ u ∧ u ≤ v * p := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc l v := ae_iff.2 hsupp
  have hid : Integrable (fun x : ℝ => x) ν := by
    refine Integrable.mono' (integrable_const (|l| + |v|)) aestronglyMeasurable_id ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hx.1, neg_abs_le l, abs_nonneg v]
    · linarith [hx.2, le_abs_self v, abs_nonneg l]
  constructor
  · have h := integral_mono_ae (integrable_const l) hid (hae.mono fun x hx => hx.1)
    rwa [integral_const, hp, hu, smul_eq_mul, mul_comm] at h
  · have h := integral_mono_ae hid (integrable_const v) (hae.mono fun x hx => hx.2)
    rwa [integral_const, hp, hu, smul_eq_mul, mul_comm] at h

/-- Endpoint masses of the continuous Poisson comparison (last subsection of
`app:certificate`): for a likelihood bin `[a, b]` with `B`-mass `q` and `A`-mass `p`, the
endpoint `B`-masses `s_a = (b q - p)/(b - a)`, `s_b = (p - a q)/(b - a)` are nonnegative,
sum to `q`, and the endpoint `A`-masses `a s_a`, `b s_b` sum to `p`. -/
theorem poisson_spread {a b q p : ℝ} (hab : a < b) (h1 : a * q ≤ p) (h2 : p ≤ b * q) :
    0 ≤ (b * q - p) / (b - a) ∧ 0 ≤ (p - a * q) / (b - a) ∧
      (b * q - p) / (b - a) + (p - a * q) / (b - a) = q ∧
      a * ((b * q - p) / (b - a)) + b * ((p - a * q) / (b - a)) = p :=
  ⟨spreadLow_nonneg hab h2, spreadHigh_nonneg hab h1, spreadLow_add_spreadHigh hab,
    spread_first_moment hab⟩

/-- Convex-order domination for the Poisson spread: if `ν` is the `B`-law of the
likelihood ratio restricted to the bin `[a, b]`, with mass `q` and first moment `p` (the
bin's `A`-mass), then every convex function of the likelihood ratio has `ν`-integral at
most its value under the endpoint `B`-masses `s_a`, `s_b`. -/
theorem poisson_spread_convex_order {ν : Measure ℝ} [IsFiniteMeasure ν] {φ : ℝ → ℝ}
    {a b q p : ℝ} (hab : a < b) (hsupp : ν (Set.Icc a b)ᶜ = 0) (hq : ν.real Set.univ = q)
    (hp : ∫ x, x ∂ν = p) (hφ : ConvexOn ℝ (Set.Icc a b) φ) :
    ∫ x, φ x ∂ν ≤ (b * q - p) / (b - a) * φ a + (p - a * q) / (b - a) * φ b :=
  integral_le_spread hab hsupp hq hp hφ

end Spread

/-! ## Directed conditional convolution -/

section Candidate

variable {ι : Type*} [Fintype ι] (π y : ι → ℝ)

/-- The conditional call function `F_m(t) = E(S_m - t)_+` for a finite law of `Y` with
atoms `y k` and probabilities `π k`, through the recurrence of `eq:recurrences`. -/
noncomputable def callFin : ℕ → ℝ → ℝ
  | 0, t => max (-t) 0
  | m + 1, t => ∑ k, π k * callFin m (t - y k)

/-- The conditional put function `J_m(t) = E(t - S_m)_+`, through `eq:recurrences`. -/
noncomputable def putFin : ℕ → ℝ → ℝ
  | 0, t => max t 0
  | m + 1, t => ∑ k, π k * putFin m (t - y k)

theorem callFin_succ (m : ℕ) (t : ℝ) :
    callFin π y (m + 1) t = ∑ k, π k * callFin π y m (t - y k) := rfl

theorem putFin_succ (m : ℕ) (t : ℝ) :
    putFin π y (m + 1) t = ∑ k, π k * putFin π y m (t - y k) := rfl

/-- The recurrence computes the expectation over `m` independent draws:
`F_m(t) = E(S_m - t)_+` with `S_m = y_{k_1} + ... + y_{k_m}`. -/
theorem callFin_eq_expectation (m : ℕ) (t : ℝ) :
    callFin π y m t = ∑ x : Fin m → ι, (∏ i, π (x i)) * max (∑ i, y (x i) - t) 0 := by
  induction m generalizing t with
  | zero => simp [callFin]
  | succ m ih =>
    rw [callFin_succ, ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    ring_nf

/-- The recurrence computes `J_m(t) = E(t - S_m)_+` over `m` independent draws. -/
theorem putFin_eq_expectation (m : ℕ) (t : ℝ) :
    putFin π y m t = ∑ x : Fin m → ι, (∏ i, π (x i)) * max (t - ∑ i, y (x i)) 0 := by
  induction m generalizing t with
  | zero => simp [putFin]
  | succ m ih =>
    rw [putFin_succ, ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    ring_nf

variable {π y}

/-- Averaging translates of a convex function with nonnegative weights keeps convexity. -/
private theorem convexOn_sum_translate {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hπ : ∀ k, 0 ≤ π k) : ConvexOn ℝ Set.univ fun t => ∑ k, π k * f (t - y k) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := hf.2 (Set.mem_univ (s - y k)) (Set.mem_univ (t - y k)) ha hb hab
  simp only [smul_eq_mul] at h
  have heq : a * s + b * t - y k = a * (s - y k) + b * (t - y k) := by
    have : y k = (a + b) * y k := by rw [hab, one_mul]
    linarith [this]
  rw [heq]
  calc π k * f (a * (s - y k) + b * (t - y k))
      ≤ π k * (a * f (s - y k) + b * f (t - y k)) := mul_le_mul_of_nonneg_left h (hπ k)
    _ = a * (π k * f (s - y k)) + b * (π k * f (t - y k)) := by ring

theorem callFin_convexOn (hπ : ∀ k, 0 ≤ π k) (m : ℕ) : ConvexOn ℝ Set.univ (callFin π y m) := by
  induction m with
  | zero =>
    have h : ConvexOn ℝ Set.univ ((fun t : ℝ => -t) ⊔ fun _ => (0 : ℝ)) :=
      (concaveOn_id convex_univ).neg.sup (convexOn_const 0 convex_univ)
    convert h using 1
    funext t
    rfl
  | succ m ih => exact convexOn_sum_translate ih hπ

theorem putFin_convexOn (hπ : ∀ k, 0 ≤ π k) (m : ℕ) : ConvexOn ℝ Set.univ (putFin π y m) := by
  induction m with
  | zero =>
    have h : ConvexOn ℝ Set.univ ((fun t : ℝ => t) ⊔ fun _ => (0 : ℝ)) :=
      (convexOn_id convex_univ).sup (convexOn_const 0 convex_univ)
    convert h using 1
    funext t
    rfl
  | succ m ih => exact convexOn_sum_translate ih hπ

theorem callFin_nonneg (hπ : ∀ k, 0 ≤ π k) (m : ℕ) (t : ℝ) : 0 ≤ callFin π y m t := by
  induction m generalizing t with
  | zero => exact le_max_right _ _
  | succ m ih => exact Finset.sum_nonneg fun k _ => mul_nonneg (hπ k) (ih _)

theorem putFin_nonneg (hπ : ∀ k, 0 ≤ π k) (m : ℕ) (t : ℝ) : 0 ≤ putFin π y m t := by
  induction m generalizing t with
  | zero => exact le_max_right _ _
  | succ m ih => exact Finset.sum_nonneg fun k _ => mul_nonneg (hπ k) (ih _)

/-- `F_m` is nonincreasing, so evaluating it at a downward-rounded argument is
conservative. -/
theorem callFin_antitone (hπ : ∀ k, 0 ≤ π k) (m : ℕ) : Antitone (callFin π y m) := by
  induction m with
  | zero => exact fun s t hst => max_le_max (by linarith) le_rfl
  | succ m ih =>
    exact fun s t hst => Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (ih (by linarith)) (hπ k)

/-- `J_m` is nondecreasing, so evaluating it at an upward-rounded argument is
conservative. -/
theorem putFin_monotone (hπ : ∀ k, 0 ≤ π k) (m : ℕ) : Monotone (putFin π y m) := by
  induction m with
  | zero => exact fun s t hst => max_le_max hst le_rfl
  | succ m ih =>
    exact fun s t hst => Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (ih (by linarith)) (hπ k)

/-- Boundary identity below zero: `F_m(s) = m E Y - s` for `s ≤ 0`. -/
theorem callFin_of_nonpos (hπ1 : ∑ k, π k = 1) (hy : ∀ k, 0 ≤ y k) (m : ℕ) {s : ℝ}
    (hs : s ≤ 0) : callFin π y m s = m * (∑ k, π k * y k) - s := by
  induction m generalizing s with
  | zero => simp [callFin, hs]
  | succ m ih =>
    rw [callFin_succ]
    have h : ∀ k, π k * callFin π y m (s - y k) =
        π k * (m * (∑ k, π k * y k) - s) + π k * y k := by
      intro k
      rw [ih (by linarith [hy k])]
      ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hπ1]
    push_cast
    ring

/-- Boundary identity below zero for the put: `J_m(s) = 0` for `s ≤ 0`. -/
theorem putFin_of_nonpos (hy : ∀ k, 0 ≤ y k) (m : ℕ) {s : ℝ} (hs : s ≤ 0) :
    putFin π y m s = 0 := by
  induction m generalizing s with
  | zero => simp [putFin, hs]
  | succ m ih =>
    rw [putFin_succ]
    exact Finset.sum_eq_zero fun k _ => by rw [ih (by linarith [hy k]), mul_zero]

/-- Beyond the largest possible sum the call vanishes: `F_m(s) = 0` when
`s ≥ m · max y`. -/
theorem callFin_eq_zero {ymax : ℝ} (hymax : ∀ k, y k ≤ ymax) (m : ℕ) {s : ℝ}
    (hs : m * ymax ≤ s) : callFin π y m s = 0 := by
  induction m generalizing s with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul] at hs
    simp [callFin, hs]
  | succ m ih =>
    rw [callFin_succ]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [ih, mul_zero]
    push_cast at hs
    linarith [hymax k]

end Candidate

section Grid

/-- Index of the grid interval used at `s`: the largest `j ≤ N - 1` with `g j ≤ s`. -/
noncomputable def nodeIndex (g : ℕ → ℝ) (N : ℕ) (s : ℝ) : ℕ :=
  Nat.findGreatest (fun j => g j ≤ s) (N - 1)

/-- Chord through the stored node values `U j`, `U (j + 1)` evaluated at `s`, on the grid
interval `[g j, g (j + 1)]` with `j = nodeIndex g N s`. -/
noncomputable def interp (g : ℕ → ℝ) (N : ℕ) (U : ℕ → ℝ) (s : ℝ) : ℝ :=
  ((g (nodeIndex g N s + 1) - s) * U (nodeIndex g N s) +
      (s - g (nodeIndex g N s)) * U (nodeIndex g N s + 1)) /
    (g (nodeIndex g N s + 1) - g (nodeIndex g N s))

/-- Stored upper continuation in the forward recursion at the `m`-th step: the boundary
value `m μ - s` below zero, the node chord on `[0, g N]`, and zero beyond the last node. -/
noncomputable def forwardCont (g : ℕ → ℝ) (N : ℕ) (μ : ℝ) (m : ℕ) (U : ℕ → ℝ) (s : ℝ) : ℝ :=
  if s < 0 then m * μ - s else if s ≤ g N then interp g N U s else 0

/-- Stored upper continuation in the reverse recursion: zero below zero and the node chord
on `[0, g N]`. -/
noncomputable def reverseCont (g : ℕ → ℝ) (N : ℕ) (U : ℕ → ℝ) (s : ℝ) : ℝ :=
  if s < 0 then 0 else interp g N U s

variable {g : ℕ → ℝ} {N : ℕ}

theorem grid_mono (hgs : ∀ j < N, g j < g (j + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    g i ≤ g j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hgs j (by omega)).le

theorem nodeIndex_spec (hN : 0 < N) (hgs : ∀ j < N, g j < g (j + 1)) {s : ℝ}
    (h0 : g 0 ≤ s) (hs : s ≤ g N) :
    nodeIndex g N s < N ∧ g (nodeIndex g N s) ≤ s ∧ s ≤ g (nodeIndex g N s + 1) ∧
      g (nodeIndex g N s) < g (nodeIndex g N s + 1) := by
  have hj : nodeIndex g N s = Nat.findGreatest (fun j => g j ≤ s) (N - 1) := rfl
  rw [hj]
  set j := Nat.findGreatest (fun j => g j ≤ s) (N - 1) with hjdef
  have hjle : j ≤ N - 1 := Nat.findGreatest_le _
  have hjN : j < N := by omega
  have hgj : g j ≤ s := Nat.findGreatest_spec (P := fun j => g j ≤ s) (Nat.zero_le _) h0
  refine ⟨hjN, hgj, ?_, hgs j hjN⟩
  by_cases hlt : j + 1 ≤ N - 1
  · have hnot := Nat.findGreatest_is_greatest (P := fun j => g j ≤ s) (k := j + 1)
      (by omega) hlt
    exact (not_le.1 hnot).le
  · have : j + 1 = N := by omega
    rw [this]
    exact hs

/-- The chord bound on a node grid: a convex function bounded above at the nodes by `U`
is bounded above on `[g 0, g N]` by the chord of the stored values. -/
theorem le_interp {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hN : 0 < N)
    (hgs : ∀ j < N, g j < g (j + 1)) {U : ℕ → ℝ} (hU : ∀ i ≤ N, f (g i) ≤ U i) {s : ℝ}
    (h0 : g 0 ≤ s) (hs : s ≤ g N) : f s ≤ interp g N U s := by
  obtain ⟨hjN, hgj, hgj1, hlt⟩ := nodeIndex_spec hN hgs h0 hs
  exact le_chord_of_convexOn (hf.subset (Set.subset_univ _) (convex_Icc _ _)) hlt ⟨hgj, hgj1⟩
    (hU _ hjN.le) (hU _ hjN)

variable {ι : Type*} [Fintype ι] {π y : ι → ℝ}

/-- Forward continuation bound on `(-∞, g N]`: if the stored values dominate `F_m` at the
nodes, the stored continuation dominates `F_m`. -/
theorem callFin_le_forwardCont (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    (hπ : ∀ k, 0 ≤ π k) (hπ1 : ∑ k, π k = 1) (hy : ∀ k, 0 ≤ y k) {μ : ℝ}
    (hμ : ∑ k, π k * y k ≤ μ) {m : ℕ} {U : ℕ → ℝ} (hU : ∀ i ≤ N, callFin π y m (g i) ≤ U i)
    {s : ℝ} (hs : s ≤ g N) : callFin π y m s ≤ forwardCont g N μ m U s := by
  unfold forwardCont
  split_ifs with hneg
  · rw [callFin_of_nonpos hπ1 hy m hneg.le]
    have : (m : ℝ) * ∑ k, π k * y k ≤ m * μ := mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg m)
    linarith
  · exact le_interp (callFin_convexOn hπ m) hN hgs hU (by rw [hg0]; linarith) hs

/-- Reverse continuation bound on `(-∞, g N]`. -/
theorem putFin_le_reverseCont (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    (hπ : ∀ k, 0 ≤ π k) (hy : ∀ k, 0 ≤ y k) {m : ℕ} {U : ℕ → ℝ}
    (hU : ∀ i ≤ N, putFin π y m (g i) ≤ U i) {s : ℝ} (hs : s ≤ g N) :
    putFin π y m s ≤ reverseCont g N U s := by
  unfold reverseCont
  split_ifs with hneg
  · rw [putFin_of_nonpos hy m hneg.le]
  · exact le_interp (putFin_convexOn hπ m) hN hgs hU (by rw [hg0]; linarith) hs

/-- Chord induction for the forward recursion (subsection "Directed conditional
convolution" of `app:certificate`). The grid `g 0 = 0 < g 1 < ... < g N` is arbitrary.
The node arrays `U m` dominate the base function `F_0` and each step dominates the
average, under upward-rounded probabilities `πu k ≥ π k`, of the stored continuation of
the previous array. The mean `μ` used below zero is any upper bound for `E Y`. Then
`U m` dominates `F_m` at every node and every `m`. -/
theorem callFin_le_nodes (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    (hπ : ∀ k, 0 ≤ π k) (hπ1 : ∑ k, π k = 1) (hy : ∀ k, 0 ≤ y k) {πu : ι → ℝ}
    (hπu : ∀ k, π k ≤ πu k) {μ : ℝ} (hμ : ∑ k, π k * y k ≤ μ) (U : ℕ → ℕ → ℝ)
    (hbase : ∀ i ≤ N, callFin π y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * forwardCont g N μ m (U m) (g i - y k) ≤ U (m + 1) i)
    (m : ℕ) : ∀ i ≤ N, callFin π y m (g i) ≤ U m i := by
  induction m with
  | zero => exact hbase
  | succ m ih =>
    intro i hi
    rw [callFin_succ]
    refine le_trans ?_ (hstep m i hi)
    refine Finset.sum_le_sum fun k _ => ?_
    have hle : g i - y k ≤ g N := by linarith [grid_mono hgs hi le_rfl, hy k]
    have hc := callFin_le_forwardCont hN hg0 hgs hπ hπ1 hy hμ ih hle
    have hc0 := callFin_nonneg (y := y) hπ m (g i - y k)
    calc π k * callFin π y m (g i - y k) ≤ π k * forwardCont g N μ m (U m) (g i - y k) :=
          mul_le_mul_of_nonneg_left hc (hπ k)
      _ ≤ πu k * forwardCont g N μ m (U m) (g i - y k) :=
          mul_le_mul_of_nonneg_right (hπu k) (hc0.trans hc)

/-- Chord induction for the reverse recursion: the node arrays `U m` dominate `J_m` at
every node and every `m`. -/
theorem putFin_le_nodes (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    (hπ : ∀ k, 0 ≤ π k) (hy : ∀ k, 0 ≤ y k) {πu : ι → ℝ} (hπu : ∀ k, π k ≤ πu k)
    (U : ℕ → ℕ → ℝ) (hbase : ∀ i ≤ N, putFin π y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * reverseCont g N (U m) (g i - y k) ≤ U (m + 1) i)
    (m : ℕ) : ∀ i ≤ N, putFin π y m (g i) ≤ U m i := by
  induction m with
  | zero => exact hbase
  | succ m ih =>
    intro i hi
    rw [putFin_succ]
    refine le_trans ?_ (hstep m i hi)
    refine Finset.sum_le_sum fun k _ => ?_
    have hle : g i - y k ≤ g N := by linarith [grid_mono hgs hi le_rfl, hy k]
    have hc := putFin_le_reverseCont hN hg0 hgs hπ hy ih hle
    have hc0 := putFin_nonneg (y := y) hπ m (g i - y k)
    calc π k * putFin π y m (g i - y k) ≤ π k * reverseCont g N (U m) (g i - y k) :=
          mul_le_mul_of_nonneg_left hc (hπ k)
      _ ≤ πu k * reverseCont g N (U m) (g i - y k) :=
          mul_le_mul_of_nonneg_right (hπu k) (hc0.trans hc)

/-- Evaluation of the forward bound at an arbitrary threshold. When the grid reaches
`m · max y`, the stored continuation of `U m` dominates `F_m` everywhere. -/
theorem callFin_le_eval (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    (hπ : ∀ k, 0 ≤ π k) (hπ1 : ∑ k, π k = 1) (hy : ∀ k, 0 ≤ y k) {πu : ι → ℝ}
    (hπu : ∀ k, π k ≤ πu k) {μ : ℝ} (hμ : ∑ k, π k * y k ≤ μ) (U : ℕ → ℕ → ℝ)
    (hbase : ∀ i ≤ N, callFin π y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * forwardCont g N μ m (U m) (g i - y k) ≤ U (m + 1) i)
    {ymax : ℝ} (hymax : ∀ k, y k ≤ ymax) {m : ℕ} (hcover : m * ymax ≤ g N) (s : ℝ) :
    callFin π y m s ≤ forwardCont g N μ m (U m) s := by
  have hnodes := callFin_le_nodes hN hg0 hgs hπ hπ1 hy hπu hμ U hbase hstep m
  by_cases hs : s ≤ g N
  · exact callFin_le_forwardCont hN hg0 hgs hπ hπ1 hy hμ hnodes hs
  · have hpos : ¬ s < 0 := by
      have := grid_mono hgs (Nat.zero_le N) le_rfl
      rw [hg0] at this
      linarith
    rw [callFin_eq_zero hymax m (by linarith)]
    simp [forwardCont, hpos, hs]

/-- Evaluation of the reverse bound at a threshold inside the grid. -/
theorem putFin_le_eval (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    (hπ : ∀ k, 0 ≤ π k) (hy : ∀ k, 0 ≤ y k) {πu : ι → ℝ} (hπu : ∀ k, π k ≤ πu k)
    (U : ℕ → ℕ → ℝ) (hbase : ∀ i ≤ N, putFin π y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * reverseCont g N (U m) (g i - y k) ≤ U (m + 1) i)
    (m : ℕ) {s : ℝ} (hs : s ≤ g N) : putFin π y m s ≤ reverseCont g N (U m) s :=
  putFin_le_reverseCont hN hg0 hgs hπ hy (putFin_le_nodes hN hg0 hgs hπ hy hπu U hbase hstep m) hs

end Grid

/-! ## Relocation of rounded-away mass -/

section Relocation

variable {ι : Type*} [Fintype ι] {π πd y : ι → ℝ}

/-- Forward relocation: rounding the masses of a probability law `π` down to `πd ≤ π` and
moving the whole deficit `1 - ∑ πd` to a point `top` above every atom gives a law whose
expectation of every nondecreasing `ψ` is at least that of `π`. -/
theorem expect_le_relocate_top (hπ1 : ∑ k, π k = 1) (hle : ∀ k, πd k ≤ π k) {top : ℝ}
    (htop : ∀ k, y k ≤ top) {ψ : ℝ → ℝ} (hψ : Monotone ψ) :
    ∑ k, π k * ψ (y k) ≤ ∑ k, πd k * ψ (y k) + (1 - ∑ k, πd k) * ψ top := by
  have h : ∑ k, πd k * ψ (y k) + (1 - ∑ k, πd k) * ψ top - ∑ k, π k * ψ (y k) =
      ∑ k, (π k - πd k) * (ψ top - ψ (y k)) := by
    rw [← hπ1, ← Finset.sum_sub_distrib, Finset.sum_mul]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have h0 : 0 ≤ ∑ k, (π k - πd k) * (ψ top - ψ (y k)) :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (sub_nonneg.2 (hle k)) (sub_nonneg.2 (hψ (htop k)))
  linarith

/-- Reverse relocation: moving the deficit to a point `bot` below every atom gives a
law whose expectation of every nonincreasing `ψ` is at least that of `π`. -/
theorem expect_le_relocate_bot (hπ1 : ∑ k, π k = 1) (hle : ∀ k, πd k ≤ π k) {bot : ℝ}
    (hbot : ∀ k, bot ≤ y k) {ψ : ℝ → ℝ} (hψ : Antitone ψ) :
    ∑ k, π k * ψ (y k) ≤ ∑ k, πd k * ψ (y k) + (1 - ∑ k, πd k) * ψ bot := by
  have h : ∑ k, πd k * ψ (y k) + (1 - ∑ k, πd k) * ψ bot - ∑ k, π k * ψ (y k) =
      ∑ k, (π k - πd k) * (ψ bot - ψ (y k)) := by
    rw [← hπ1, ← Finset.sum_sub_distrib, Finset.sum_mul]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have h0 : 0 ≤ ∑ k, (π k - πd k) * (ψ bot - ψ (y k)) :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (sub_nonneg.2 (hle k)) (sub_nonneg.2 (hψ (hbot k)))
  linarith

/-- The array `πd` with its deficit `1 - ∑ πd` added at the atom `k0`. -/
def relocate [DecidableEq ι] (πd : ι → ℝ) (k0 : ι) (k : ι) : ℝ :=
  πd k + if k = k0 then 1 - ∑ j, πd j else 0

theorem relocate_deficit_nonneg (hπ1 : ∑ k, π k = 1) (hle : ∀ k, πd k ≤ π k) :
    0 ≤ 1 - ∑ k, πd k := by
  rw [← hπ1, sub_nonneg]
  exact Finset.sum_le_sum fun k _ => hle k

/-- The relocated arrays are normalized exactly: if `0 ≤ πd ≤ π` and `π` sums to one, the
relocated masses are nonnegative and sum to one. -/
theorem relocate_normalized [DecidableEq ι] (hπ1 : ∑ k, π k = 1) (hd0 : ∀ k, 0 ≤ πd k)
    (hle : ∀ k, πd k ≤ π k) (k0 : ι) :
    (∀ k, 0 ≤ relocate πd k0 k) ∧ ∑ k, relocate πd k0 k = 1 := by
  have hdef := relocate_deficit_nonneg hπ1 hle
  refine ⟨fun k => add_nonneg (hd0 k) (by split_ifs <;> simp [hdef]), ?_⟩
  simp only [relocate, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Forward relocation onto an existing atom `ktop` of largest location, written as the
modified array `πd + (1 - ∑ πd) δ_ktop` used by the certificate. -/
theorem expect_le_relocate_atom_top [DecidableEq ι] (hπ1 : ∑ k, π k = 1)
    (hle : ∀ k, πd k ≤ π k) {ktop : ι} (htop : ∀ k, y k ≤ y ktop) {ψ : ℝ → ℝ}
    (hψ : Monotone ψ) :
    ∑ k, π k * ψ (y k) ≤ ∑ k, relocate πd ktop k * ψ (y k) := by
  have h := expect_le_relocate_top hπ1 hle htop hψ
  simp only [relocate, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact h

/-- Reverse relocation onto an existing atom `kbot` of smallest location. -/
theorem expect_le_relocate_atom_bot [DecidableEq ι] (hπ1 : ∑ k, π k = 1)
    (hle : ∀ k, πd k ≤ π k) {kbot : ι} (hbot : ∀ k, y kbot ≤ y k) {ψ : ℝ → ℝ}
    (hψ : Antitone ψ) :
    ∑ k, π k * ψ (y k) ≤ ∑ k, relocate πd kbot k * ψ (y k) := by
  have h := expect_le_relocate_bot hπ1 hle hbot hψ
  simp only [relocate, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact h

end Relocation

/-! ## Comparison of finite laws in the recursion -/

section Comparison

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {π y : ι → ℝ} {π' y' : ι' → ℝ}

private theorem convexOn_reflect {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (t : ℝ) :
    ConvexOn ℝ Set.univ fun z => f (t - z) := by
  refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
  have h := hf.2 (Set.mem_univ (t - a)) (Set.mem_univ (t - b)) hα hβ hαβ
  simp only [smul_eq_mul] at h ⊢
  have heq : t - (α * a + β * b) = α * (t - a) + β * (t - b) := by
    have ht : t = (α + β) * t := by rw [hαβ, one_mul]
    linarith
  rw [heq]
  exact h

/-- If `(π', y')` dominates `(π, y)` for every convex nondecreasing function, then
`F_m^π ≤ F_m^{π'}` for every `m`: the summand `y ↦ F_{m-1}(t - y)` is convex and
nondecreasing. -/
theorem callFin_le_of_dominates (hπ : ∀ k, 0 ≤ π k) (hπ' : ∀ k, 0 ≤ π' k)
    (hdom : ∀ ψ : ℝ → ℝ, ConvexOn ℝ Set.univ ψ → Monotone ψ →
      ∑ k, π k * ψ (y k) ≤ ∑ k, π' k * ψ (y' k)) (m : ℕ) (t : ℝ) :
    callFin π y m t ≤ callFin π' y' m t := by
  induction m generalizing t with
  | zero => exact le_rfl
  | succ m ih =>
    rw [callFin_succ, callFin_succ]
    calc ∑ k, π k * callFin π y m (t - y k) ≤ ∑ k, π k * callFin π' y' m (t - y k) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ih _) (hπ k)
      _ ≤ ∑ k, π' k * callFin π' y' m (t - y' k) :=
          hdom (fun z => callFin π' y' m (t - z)) (convexOn_reflect (callFin_convexOn hπ' m) t)
            fun a b hab => callFin_antitone hπ' m (by linarith)

/-- If `(π', y')` dominates `(π, y)` for every convex nonincreasing function, then
`J_m^π ≤ J_m^{π'}` for every `m`. -/
theorem putFin_le_of_dominates (hπ : ∀ k, 0 ≤ π k) (hπ' : ∀ k, 0 ≤ π' k)
    (hdom : ∀ ψ : ℝ → ℝ, ConvexOn ℝ Set.univ ψ → Antitone ψ →
      ∑ k, π k * ψ (y k) ≤ ∑ k, π' k * ψ (y' k)) (m : ℕ) (t : ℝ) :
    putFin π y m t ≤ putFin π' y' m t := by
  induction m generalizing t with
  | zero => exact le_rfl
  | succ m ih =>
    rw [putFin_succ, putFin_succ]
    calc ∑ k, π k * putFin π y m (t - y k) ≤ ∑ k, π k * putFin π' y' m (t - y k) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ih _) (hπ k)
      _ ≤ ∑ k, π' k * putFin π' y' m (t - y' k) :=
          hdom (fun z => putFin π' y' m (t - z)) (convexOn_reflect (putFin_convexOn hπ' m) t)
            fun a b hab => putFin_monotone hπ' m (by linarith)

/-- The forward upper law (rounded-down masses `πd`, deficit moved to the atom `ktop` of
largest location) gives an upper bound on `F_m` of the exact law. -/
theorem callFin_le_relocate_top [DecidableEq ι] (hπ : ∀ k, 0 ≤ π k) (hπ1 : ∑ k, π k = 1)
    {πd : ι → ℝ} (hd0 : ∀ k, 0 ≤ πd k) (hle : ∀ k, πd k ≤ π k) {ktop : ι}
    (htop : ∀ k, y k ≤ y ktop) (m : ℕ) (t : ℝ) :
    callFin π y m t ≤ callFin (relocate πd ktop) y m t :=
  callFin_le_of_dominates hπ (relocate_normalized hπ1 hd0 hle ktop).1
    (fun _ _ hψ => expect_le_relocate_atom_top hπ1 hle htop hψ) m t

/-- The reverse upper law (deficit moved to the atom `kbot` of smallest location) gives an
upper bound on `J_m` of the exact law. -/
theorem putFin_le_relocate_bot [DecidableEq ι] (hπ : ∀ k, 0 ≤ π k) (hπ1 : ∑ k, π k = 1)
    {πd : ι → ℝ} (hd0 : ∀ k, 0 ≤ πd k) (hle : ∀ k, πd k ≤ π k) {kbot : ι}
    (hbot : ∀ k, y kbot ≤ y k) (m : ℕ) (t : ℝ) :
    putFin π y m t ≤ putFin (relocate πd kbot) y m t :=
  putFin_le_of_dominates hπ (relocate_normalized hπ1 hd0 hle kbot).1
    (fun _ _ hψ => expect_le_relocate_atom_bot hπ1 hle hbot hψ) m t

end Comparison

/-! ## The recursion for a general summand law -/

section LawRecursion

/-- `F_m` of `eq:recurrences` when the summand has an arbitrary law `ν`. -/
noncomputable def callLaw (ν : Measure ℝ) : ℕ → ℝ → ℝ
  | 0, t => max (-t) 0
  | m + 1, t => ∫ x, callLaw ν m (t - x) ∂ν

/-- `J_m` of `eq:recurrences` when the summand has an arbitrary law `ν`. -/
noncomputable def putLaw (ν : Measure ℝ) : ℕ → ℝ → ℝ
  | 0, t => max t 0
  | m + 1, t => ∫ x, putLaw ν m (t - x) ∂ν

theorem callLaw_nonneg (ν : Measure ℝ) (m : ℕ) (t : ℝ) : 0 ≤ callLaw ν m t := by
  induction m generalizing t with
  | zero => exact le_max_right _ _
  | succ m ih => exact integral_nonneg fun x => ih _

theorem putLaw_nonneg (ν : Measure ℝ) (m : ℕ) (t : ℝ) : 0 ≤ putLaw ν m t := by
  induction m generalizing t with
  | zero => exact le_max_right _ _
  | succ m ih => exact integral_nonneg fun x => ih _

private theorem integrable_abs_coord (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x => x) ν) {m : ℕ} (i : Fin m) :
    Integrable (fun x : Fin m → ℝ => |x i|) (Measure.pi fun _ : Fin m => ν) :=
  ((measurePreserving_eval (fun _ : Fin m => ν) i).integrable_comp
    (g := fun x : ℝ => |x|) continuous_abs.aestronglyMeasurable).2 hν.abs

private theorem integrable_prod_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x => x) ν) (m : ℕ) (t : ℝ) :
    Integrable (fun p : ℝ × (Fin m → ℝ) => |p.1| + ∑ i, |p.2 i| + |t|)
      (ν.prod (Measure.pi fun _ : Fin m => ν)) :=
  ((hν.abs.comp_fst _).add (integrable_finsetSum Finset.univ
    fun i _ => (integrable_abs_coord ν hν i).comp_snd ν)).add (integrable_const |t|)

/-- For a probability law `ν` with finite first moment, the recurrence `eq:recurrences`
computes `F_m(t) = E(S_m - t)_+`, where `S_m` is the sum of the coordinates under the
product law `ν^{⊗m}`. -/
theorem callLaw_eq_integral_pi (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x => x) ν) (m : ℕ) (t : ℝ) :
    callLaw ν m t = ∫ x, max (∑ i, x i - t) 0 ∂(Measure.pi fun _ : Fin m => ν) := by
  induction m generalizing t with
  | zero =>
    rw [Measure.pi_of_empty, integral_dirac]
    simp [callLaw]
  | succ m ih =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) 0
    set g : ℝ × (Fin m → ℝ) → ℝ := fun p => max (p.1 + ∑ i, p.2 i - t) 0 with hg
    have hcomp : ∀ x : Fin (m + 1) → ℝ,
        max (∑ i, x i - t) 0 = g (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x) := by
      intro x
      simp [g, MeasurableEquiv.piFinSuccAbove_apply, Fin.sum_univ_succ, add_sub_assoc, Fin.tail]
    have hcont : Continuous g := by
      simp only [hg]
      fun_prop
    have hint : Integrable g (ν.prod (Measure.pi fun _ : Fin m => ν)) := by
      refine Integrable.mono' (integrable_prod_bound ν hν m t) hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [hg, Real.norm_eq_abs]
      have h1 : |∑ i, p.2 i| ≤ ∑ i, |p.2 i| := Finset.abs_sum_le_sum_abs _ _
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      linarith [le_abs_self p.1, le_abs_self (∑ i, p.2 i), neg_abs_le t]
    rw [integral_congr_ae (Filter.Eventually.of_forall hcomp), hmp.integral_comp' g,
      integral_prod g hint]
    simp only [callLaw]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hg, ih]
    congr 1
    funext x
    ring_nf

/-- For a probability law `ν` with finite first moment, the recurrence computes
`J_m(t) = E(t - S_m)_+` under the product law `ν^{⊗m}`. -/
theorem putLaw_eq_integral_pi (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x => x) ν) (m : ℕ) (t : ℝ) :
    putLaw ν m t = ∫ x, max (t - ∑ i, x i) 0 ∂(Measure.pi fun _ : Fin m => ν) := by
  induction m generalizing t with
  | zero =>
    rw [Measure.pi_of_empty, integral_dirac]
    simp [putLaw]
  | succ m ih =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) 0
    set g : ℝ × (Fin m → ℝ) → ℝ := fun p => max (t - (p.1 + ∑ i, p.2 i)) 0 with hg
    have hcomp : ∀ x : Fin (m + 1) → ℝ,
        max (t - ∑ i, x i) 0 = g (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x) := by
      intro x
      simp [g, MeasurableEquiv.piFinSuccAbove_apply, Fin.sum_univ_succ, Fin.tail]
    have hcont : Continuous g := by
      simp only [hg]
      fun_prop
    have hint : Integrable g (ν.prod (Measure.pi fun _ : Fin m => ν)) := by
      refine Integrable.mono' (integrable_prod_bound ν hν m t) hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [hg, Real.norm_eq_abs]
      have h1 : |∑ i, p.2 i| ≤ ∑ i, |p.2 i| := Finset.abs_sum_le_sum_abs _ _
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      linarith [neg_abs_le p.1, neg_abs_le (∑ i, p.2 i), le_abs_self t]
    rw [integral_congr_ae (Filter.Eventually.of_forall hcomp), hmp.integral_comp' g,
      integral_prod g hint]
    simp only [putLaw]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hg, ih]
    congr 1
    funext x
    ring_nf

/-- Endpoint spreads applied bin by bin (`eq:spread`): if `ν = ∑_b ν_b + ρ`, where `ν_b` is
concentrated on `[l_b, v_b]` with mass `p_b` and first moment `u_b`, and `ρ` holds the
retained tail atoms, then every convex `φ` integrable for `ρ` satisfies
`∫ φ dν ≤ ∑_b (w_l φ(l_b) + w_v φ(v_b)) + ∫ φ dρ`. -/
theorem integral_le_spread_sum {β : Type*} (B : Finset β) (νb : β → Measure ℝ)
    [∀ b, IsFiniteMeasure (νb b)] (ρ : Measure ℝ) (l v p u : β → ℝ)
    (hlv : ∀ b ∈ B, l b < v b) (hsupp : ∀ b ∈ B, νb b (Set.Icc (l b) (v b))ᶜ = 0)
    (hp : ∀ b ∈ B, (νb b).real Set.univ = p b) (hu : ∀ b ∈ B, ∫ x, x ∂(νb b) = u b)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (hρ : Integrable φ ρ) :
    ∫ x, φ x ∂(∑ b ∈ B, νb b + ρ) ≤
      ∑ b ∈ B, (spreadLow (l b) (v b) (p b) (u b) * φ (l b) +
        spreadHigh (l b) (v b) (p b) (u b) * φ (v b)) + ∫ x, φ x ∂ρ := by
  have hφb : ∀ b ∈ B, ConvexOn ℝ (Set.Icc (l b) (v b)) φ := fun b _ =>
    hφ.subset (Set.subset_univ _) (convex_Icc _ _)
  have hint : ∀ b ∈ B, Integrable φ (νb b) := fun b hb =>
    integrable_of_convexOn_Icc (hlv b hb) (hsupp b hb) (hφb b hb)
  rw [integral_add_measure (integrable_finsetSum_measure.2 hint) hρ,
    integral_finsetSum_measure hint]
  gcongr with b hb
  exact integral_le_spread (hlv b hb) (hsupp b hb) (hp b hb) (hu b hb) (hφb b hb)

variable {ι : Type*} [Fintype ι] {π y : ι → ℝ}

/-- Convex-order domination passes through the recursion: if the finite law `(π, y)`
dominates the law `ν`, concentrated on `[a, b]`, for every convex nondecreasing function,
then `F_m` of `ν` is at most `F_m` of `(π, y)` for every `m`. -/
theorem callLaw_le_callFin {ν : Measure ℝ} [IsFiniteMeasure ν] {a b : ℝ} (hab : a < b)
    (hsupp : ν (Set.Icc a b)ᶜ = 0) (hπ : ∀ k, 0 ≤ π k)
    (hdom : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Monotone φ →
      ∫ x, φ x ∂ν ≤ ∑ k, π k * φ (y k)) (m : ℕ) (t : ℝ) :
    callLaw ν m t ≤ callFin π y m t := by
  induction m generalizing t with
  | zero => exact le_rfl
  | succ m ih =>
    have hconv : ConvexOn ℝ Set.univ fun x => callFin π y m (t - x) :=
      convexOn_reflect (callFin_convexOn hπ m) t
    have hint : Integrable (fun x => callFin π y m (t - x)) ν :=
      integrable_of_convexOn_Icc hab hsupp (hconv.subset (Set.subset_univ _) (convex_Icc _ _))
    calc callLaw ν (m + 1) t = ∫ x, callLaw ν m (t - x) ∂ν := rfl
      _ ≤ ∫ x, callFin π y m (t - x) ∂ν :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => callLaw_nonneg ν m _)
            hint (Filter.Eventually.of_forall fun x => ih _)
      _ ≤ ∑ k, π k * callFin π y m (t - y k) :=
          hdom _ hconv fun x x' hxx' => callFin_antitone hπ m (by linarith)
      _ = callFin π y (m + 1) t := rfl

/-- The put version: domination for every convex nonincreasing function gives
`J_m` of `ν` at most `J_m` of `(π, y)`. -/
theorem putLaw_le_putFin {ν : Measure ℝ} [IsFiniteMeasure ν] {a b : ℝ} (hab : a < b)
    (hsupp : ν (Set.Icc a b)ᶜ = 0) (hπ : ∀ k, 0 ≤ π k)
    (hdom : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Antitone φ →
      ∫ x, φ x ∂ν ≤ ∑ k, π k * φ (y k)) (m : ℕ) (t : ℝ) :
    putLaw ν m t ≤ putFin π y m t := by
  induction m generalizing t with
  | zero => exact le_rfl
  | succ m ih =>
    have hconv : ConvexOn ℝ Set.univ fun x => putFin π y m (t - x) :=
      convexOn_reflect (putFin_convexOn hπ m) t
    have hint : Integrable (fun x => putFin π y m (t - x)) ν :=
      integrable_of_convexOn_Icc hab hsupp (hconv.subset (Set.subset_univ _) (convex_Icc _ _))
    calc putLaw ν (m + 1) t = ∫ x, putLaw ν m (t - x) ∂ν := rfl
      _ ≤ ∫ x, putFin π y m (t - x) ∂ν :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => putLaw_nonneg ν m _)
            hint (Filter.Eventually.of_forall fun x => ih _)
      _ ≤ ∑ k, π k * putFin π y m (t - y k) :=
          hdom _ hconv fun x x' hxx' => putFin_monotone hπ m (by linarith)
      _ = putFin π y (m + 1) t := rfl

/-- Soundness chain for the forward direction. The summand law `ν` on `[a, b]` is dominated
in convex order by the finite spread law `(πs, y)`; its masses are rounded down to `πd` and
the deficit is moved to the atom `ktop` of largest location; the node arrays `U` satisfy the
directed recursion of `callFin_le_nodes` for that forward law. Then `U m` dominates `F_m` of
`ν` at every node. -/
theorem callLaw_le_nodes [DecidableEq ι] {ν : Measure ℝ} [IsFiniteMeasure ν] {a b : ℝ}
    (hab : a < b) (hsupp : ν (Set.Icc a b)ᶜ = 0) {πs πd : ι → ℝ} (hs0 : ∀ k, 0 ≤ πs k)
    (hs1 : ∑ k, πs k = 1) (hy : ∀ k, 0 ≤ y k)
    (hdom : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∫ x, φ x ∂ν ≤ ∑ k, πs k * φ (y k))
    (hd0 : ∀ k, 0 ≤ πd k) (hds : ∀ k, πd k ≤ πs k) {ktop : ι} (htop : ∀ k, y k ≤ y ktop)
    {g : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    {πu : ι → ℝ} (hπu : ∀ k, relocate πd ktop k ≤ πu k) {μ : ℝ}
    (hμ : ∑ k, relocate πd ktop k * y k ≤ μ) (U : ℕ → ℕ → ℝ)
    (hbase : ∀ i ≤ N, callFin (relocate πd ktop) y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * forwardCont g N μ m (U m) (g i - y k) ≤ U (m + 1) i)
    (m : ℕ) : ∀ i ≤ N, callLaw ν m (g i) ≤ U m i := by
  obtain ⟨hf0, hf1⟩ := relocate_normalized hs1 hd0 hds ktop
  intro i hi
  calc callLaw ν m (g i) ≤ callFin πs y m (g i) :=
        callLaw_le_callFin hab hsupp hs0 (fun φ hφ _ => hdom φ hφ) m (g i)
    _ ≤ callFin (relocate πd ktop) y m (g i) := callFin_le_relocate_top hs0 hs1 hd0 hds htop m (g i)
    _ ≤ U m i := callFin_le_nodes hN hg0 hgs hf0 hf1 hy hπu hμ U hbase hstep m i hi

/-- Soundness chain for the reverse direction, with the deficit moved to the atom `kbot`
of smallest location. -/
theorem putLaw_le_nodes [DecidableEq ι] {ν : Measure ℝ} [IsFiniteMeasure ν] {a b : ℝ}
    (hab : a < b) (hsupp : ν (Set.Icc a b)ᶜ = 0) {πs πd : ι → ℝ} (hs0 : ∀ k, 0 ≤ πs k)
    (hs1 : ∑ k, πs k = 1) (hy : ∀ k, 0 ≤ y k)
    (hdom : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∫ x, φ x ∂ν ≤ ∑ k, πs k * φ (y k))
    (hd0 : ∀ k, 0 ≤ πd k) (hds : ∀ k, πd k ≤ πs k) {kbot : ι} (hbot : ∀ k, y kbot ≤ y k)
    {g : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    {πu : ι → ℝ} (hπu : ∀ k, relocate πd kbot k ≤ πu k) (U : ℕ → ℕ → ℝ)
    (hbase : ∀ i ≤ N, putFin (relocate πd kbot) y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * reverseCont g N (U m) (g i - y k) ≤ U (m + 1) i)
    (m : ℕ) : ∀ i ≤ N, putLaw ν m (g i) ≤ U m i := by
  have hr0 := (relocate_normalized hs1 hd0 hds kbot).1
  intro i hi
  calc putLaw ν m (g i) ≤ putFin πs y m (g i) :=
        putLaw_le_putFin hab hsupp hs0 (fun φ hφ _ => hdom φ hφ) m (g i)
    _ ≤ putFin (relocate πd kbot) y m (g i) := putFin_le_relocate_bot hs0 hs1 hd0 hds hbot m (g i)
    _ ≤ U m i := putFin_le_nodes hN hg0 hgs hr0 hy hπu U hbase hstep m i hi

end LawRecursion

/-! ## Tail correction -/

section Tail

variable {ι : Type*}

/-- Positive-part Lipschitz inequality for the call: if `y i ≤ x i`, then
`(∑ x - t)_+ ≤ (∑ y - t)_+ + ∑ (x i - y i)`. -/
theorem call_posPart_le (s : Finset ι) (x y : ι → ℝ) (t : ℝ) (h : ∀ i ∈ s, y i ≤ x i) :
    max (∑ i ∈ s, x i - t) 0 ≤ max (∑ i ∈ s, y i - t) 0 + ∑ i ∈ s, (x i - y i) := by
  have hd : 0 ≤ ∑ i ∈ s, (x i - y i) := Finset.sum_nonneg fun i hi => sub_nonneg.2 (h i hi)
  have hx : ∑ i ∈ s, x i = ∑ i ∈ s, y i + ∑ i ∈ s, (x i - y i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine max_le ?_ (by linarith [le_max_right (∑ i ∈ s, y i - t) 0])
  linarith [le_max_left (∑ i ∈ s, y i - t) 0]

/-- The put needs no correction: if `y i ≤ x i`, then `(t - ∑ x)_+ ≤ (t - ∑ y)_+`. -/
theorem put_posPart_le (s : Finset ι) (x y : ι → ℝ) (t : ℝ) (h : ∀ i ∈ s, y i ≤ x i) :
    max (t - ∑ i ∈ s, x i) 0 ≤ max (t - ∑ i ∈ s, y i) 0 := by
  have : ∑ i ∈ s, y i ≤ ∑ i ∈ s, x i := Finset.sum_le_sum h
  exact max_le_max (by linarith) le_rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

private theorem integrable_call (s : Finset ι) {X : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Integrable (X i) P) (t : ℝ) :
    Integrable (fun ω => max (∑ i ∈ s, X i ω - t) 0) P :=
  ((integrable_finsetSum s hX).sub (integrable_const t)).pos_part.congr
    (Filter.Eventually.of_forall fun ω => by simp)

private theorem integrable_put (s : Finset ι) {X : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Integrable (X i) P) (t : ℝ) :
    Integrable (fun ω => max (t - ∑ i ∈ s, X i ω) 0) P :=
  ((integrable_const t).sub (integrable_finsetSum s hX)).pos_part.congr
    (Filter.Eventually.of_forall fun ω => by simp)

/-- Expectation form of the tail correction (`eq:tau`): for integrable `Y i ≤ X i`,
`E(∑ X - t)_+ ≤ E(∑ Y - t)_+ + ∑ E(X i - Y i)`. -/
theorem call_tail_correction (s : Finset ι) (X Y : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) P) (hY : ∀ i ∈ s, Integrable (Y i) P)
    (hXY : ∀ i ∈ s, ∀ᵐ ω ∂P, Y i ω ≤ X i ω) (t : ℝ) :
    ∫ ω, max (∑ i ∈ s, X i ω - t) 0 ∂P ≤
      ∫ ω, max (∑ i ∈ s, Y i ω - t) 0 ∂P + ∑ i ∈ s, ∫ ω, (X i ω - Y i ω) ∂P := by
  have hD : ∀ i ∈ s, Integrable (fun ω => X i ω - Y i ω) P := fun i hi => (hX i hi).sub (hY i hi)
  rw [← integral_finsetSum s hD, ← integral_add (integrable_call s hY t)
    (integrable_finsetSum s hD)]
  refine integral_mono_ae (integrable_call s hX t)
    ((integrable_call s hY t).add (integrable_finsetSum s hD)) ?_
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ s, Y i ω ≤ X i ω := (ae_ball_iff s.countable_toSet).2 hXY
  filter_upwards [hall] with ω hω
  exact call_posPart_le s (fun i => X i ω) (fun i => Y i ω) t hω

/-- Expectation form of the put comparison: for integrable `Y i ≤ X i`,
`E(t - ∑ X)_+ ≤ E(t - ∑ Y)_+`. -/
theorem put_tail_correction (s : Finset ι) (X Y : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) P) (hY : ∀ i ∈ s, Integrable (Y i) P)
    (hXY : ∀ i ∈ s, ∀ᵐ ω ∂P, Y i ω ≤ X i ω) (t : ℝ) :
    ∫ ω, max (t - ∑ i ∈ s, X i ω) 0 ∂P ≤ ∫ ω, max (t - ∑ i ∈ s, Y i ω) 0 ∂P := by
  refine integral_mono_ae (integrable_put s hX t) (integrable_put s hY t) ?_
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ s, Y i ω ≤ X i ω := (ae_ball_iff s.countable_toSet).2 hXY
  filter_upwards [hall] with ω hω
  exact put_posPart_le s (fun i => X i ω) (fun i => Y i ω) t hω

/-- The forward correction `m τ` for `F_m` when every summand has `E(X_i - Y_i) = τ`. -/
theorem call_tail_correction_tau (m : ℕ) (X Y : ℕ → Ω → ℝ)
    (hX : ∀ i < m, Integrable (X i) P) (hY : ∀ i < m, Integrable (Y i) P)
    (hXY : ∀ i < m, ∀ᵐ ω ∂P, Y i ω ≤ X i ω) {τ : ℝ}
    (hτ : ∀ i < m, ∫ ω, (X i ω - Y i ω) ∂P = τ) (t : ℝ) :
    ∫ ω, max (∑ i ∈ Finset.range m, X i ω - t) 0 ∂P ≤
      ∫ ω, max (∑ i ∈ Finset.range m, Y i ω - t) 0 ∂P + m * τ := by
  have h := call_tail_correction (Finset.range m) X Y (fun i hi => hX i (Finset.mem_range.1 hi))
    (fun i hi => hY i (Finset.mem_range.1 hi)) (fun i hi => hXY i (Finset.mem_range.1 hi)) t
  rwa [Finset.sum_congr rfl fun i hi => hτ i (Finset.mem_range.1 hi), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at h

/-- After division by `m ≥ 1` the forward correction is `τ`. -/
theorem call_tail_correction_tau_div {m : ℕ} (hm : 0 < m) (X Y : ℕ → Ω → ℝ)
    (hX : ∀ i < m, Integrable (X i) P) (hY : ∀ i < m, Integrable (Y i) P)
    (hXY : ∀ i < m, ∀ᵐ ω ∂P, Y i ω ≤ X i ω) {τ : ℝ}
    (hτ : ∀ i < m, ∫ ω, (X i ω - Y i ω) ∂P = τ) (t : ℝ) :
    (∫ ω, max (∑ i ∈ Finset.range m, X i ω - t) 0 ∂P) / m ≤
      (∫ ω, max (∑ i ∈ Finset.range m, Y i ω - t) 0 ∂P) / m + τ := by
  have h := call_tail_correction_tau m X Y hX hY hXY hτ t
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [div_add' _ _ _ hm'.ne', div_le_div_iff_of_pos_right hm']
  linarith

end Tail

section Truncation

private theorem integral_coord (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {m : ℕ} (i : Fin m)
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g ρ) :
    ∫ x, g (x i) ∂(Measure.pi fun _ : Fin m => ρ) = ∫ y, g y ∂ρ := by
  have hmp := measurePreserving_eval (fun _ : Fin m => ρ) i
  have h1 : ∫ y, g y ∂ρ = ∫ y, g y ∂((Measure.pi fun _ : Fin m => ρ).map (Function.eval i)) := by
    rw [hmp.map_eq]
  rw [h1, integral_map (measurable_pi_apply i).aemeasurable (by rwa [hmp.map_eq])]

private theorem integrable_coord (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {m : ℕ} (i : Fin m)
    {g : ℝ → ℝ} (hg : Integrable g ρ) :
    Integrable (fun x : Fin m → ℝ => g (x i)) (Measure.pi fun _ : Fin m => ρ) :=
  ((measurePreserving_eval (fun _ : Fin m => ρ) i).integrable_comp hg.1).2 hg

/-- Tail correction `eq:tau` in the recursion: if the summand `X` has law `ρ` and
`Y = h(X) ≤ X`, then `F_m^X(t) ≤ F_m^Y(t) + m τ` with `τ = E(X - Y)`. -/
theorem callLaw_le_map_add (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x => x) ρ) {h : ℝ → ℝ} (hmeas : Measurable h) (hh : ∀ x, h x ≤ x)
    (hint : Integrable h ρ) (m : ℕ) (t : ℝ) :
    callLaw ρ m t ≤ callLaw (ρ.map h) m t + m * ∫ x, (x - h x) ∂ρ := by
  have hν : Integrable (fun y => y) (ρ.map h) :=
    (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).2 hint
  have hpi : Measure.pi (fun _ : Fin m => ρ.map h) =
      (Measure.pi fun _ : Fin m => ρ).map (fun x i => h (x i)) :=
    (Measure.pi_map_pi fun _ => hmeas.aemeasurable).symm
  have hmeasH : Measurable fun (x : Fin m → ℝ) (i : Fin m) => h (x i) :=
    by fun_prop
  rw [callLaw_eq_integral_pi ρ hρ, callLaw_eq_integral_pi (ρ.map h) hν, hpi,
    integral_map hmeasH.aemeasurable (by fun_prop)]
  have hc := call_tail_correction (P := Measure.pi fun _ : Fin m => ρ) Finset.univ
    (fun i x => x i) (fun i x => h (x i)) (fun i _ => integrable_coord ρ i hρ)
    (fun i _ => integrable_coord ρ i hint) (fun i _ => Filter.Eventually.of_forall fun x => hh _) t
  have hτ : ∀ i : Fin m, ∫ x, (x i - h (x i)) ∂(Measure.pi fun _ : Fin m => ρ) =
      ∫ x, (x - h x) ∂ρ := fun i =>
    integral_coord ρ i (g := fun x => x - h x) (hρ.sub hint).1
  simp only [hτ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
  exact hc

/-- Since `Y = h(X) ≤ X`, the put needs no correction: `J_m^X(t) ≤ J_m^Y(t)`. -/
theorem putLaw_le_map (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x => x) ρ) {h : ℝ → ℝ} (hmeas : Measurable h) (hh : ∀ x, h x ≤ x)
    (hint : Integrable h ρ) (m : ℕ) (t : ℝ) :
    putLaw ρ m t ≤ putLaw (ρ.map h) m t := by
  have hν : Integrable (fun y => y) (ρ.map h) :=
    (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).2 hint
  have hpi : Measure.pi (fun _ : Fin m => ρ.map h) =
      (Measure.pi fun _ : Fin m => ρ).map (fun x i => h (x i)) :=
    (Measure.pi_map_pi fun _ => hmeas.aemeasurable).symm
  have hmeasH : Measurable fun (x : Fin m → ℝ) (i : Fin m) => h (x i) :=
    by fun_prop
  rw [putLaw_eq_integral_pi ρ hρ, putLaw_eq_integral_pi (ρ.map h) hν, hpi,
    integral_map hmeasH.aemeasurable (by fun_prop)]
  exact put_tail_correction (P := Measure.pi fun _ : Fin m => ρ) Finset.univ
    (fun i x => x i) (fun i x => h (x i)) (fun i _ => integrable_coord ρ i hρ)
    (fun i _ => integrable_coord ρ i hint) (fun i _ => Filter.Eventually.of_forall fun x => hh _) t

end Truncation

/-! ## End-to-end soundness of the conditional call and put bounds -/

section Soundness

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {y : ι → ℝ}

/-- Soundness of the forward computation of `app:certificate`. The summand `X` has law `ρ`
with finite mean; `Y = h(X) ≤ X` has law `ρ.map h` on `[a, b]`, dominated in convex order
by the finite spread law `(πs, y)` (see `integral_le_spread_sum`); the spread masses are
rounded down to `πd` and the deficit is moved to the atom `ktop` of largest location; the
node arrays `U` satisfy the directed recursion of `callFin_le_nodes` on a grid reaching
`m · y ktop`. Then for every threshold `s`, `F_m^X(s)` is at most the stored continuation of
`U m` at `s` plus `m τ`. -/
theorem certificate_call_sound (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x => x) ρ) {h : ℝ → ℝ} (hmeas : Measurable h) (hh : ∀ x, h x ≤ x)
    (hint : Integrable h ρ) {a b : ℝ} (hab : a < b) (hsupp : (ρ.map h) (Set.Icc a b)ᶜ = 0)
    {πs πd : ι → ℝ} (hs0 : ∀ k, 0 ≤ πs k) (hs1 : ∑ k, πs k = 1) (hy : ∀ k, 0 ≤ y k)
    (hdom : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
      ∫ x, φ x ∂(ρ.map h) ≤ ∑ k, πs k * φ (y k))
    (hd0 : ∀ k, 0 ≤ πd k) (hds : ∀ k, πd k ≤ πs k) {ktop : ι} (htop : ∀ k, y k ≤ y ktop)
    {g : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    {πu : ι → ℝ} (hπu : ∀ k, relocate πd ktop k ≤ πu k) {μ : ℝ}
    (hμ : ∑ k, relocate πd ktop k * y k ≤ μ) (U : ℕ → ℕ → ℝ)
    (hbase : ∀ i ≤ N, callFin (relocate πd ktop) y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * forwardCont g N μ m (U m) (g i - y k) ≤ U (m + 1) i)
    {m : ℕ} (hcover : m * y ktop ≤ g N) (s : ℝ) :
    callLaw ρ m s ≤ forwardCont g N μ m (U m) s + m * ∫ x, (x - h x) ∂ρ := by
  obtain ⟨hf0, hf1⟩ := relocate_normalized hs1 hd0 hds ktop
  have h1 : callLaw (ρ.map h) m s ≤ callFin πs y m s :=
    callLaw_le_callFin hab hsupp hs0 (fun φ hφ _ => hdom φ hφ) m s
  have h2 : callFin πs y m s ≤ callFin (relocate πd ktop) y m s :=
    callFin_le_relocate_top hs0 hs1 hd0 hds htop m s
  have h3 : callFin (relocate πd ktop) y m s ≤ forwardCont g N μ m (U m) s :=
    callFin_le_eval hN hg0 hgs hf0 hf1 hy hπu hμ U hbase hstep htop hcover s
  have h4 := callLaw_le_map_add ρ hρ hmeas hh hint m s
  linarith

/-- Soundness of the reverse computation of `app:certificate`, with the deficit moved to
the atom `kbot` of smallest location, at every threshold `s` inside the grid. No tail
correction is needed. -/
theorem certificate_put_sound (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x => x) ρ) {h : ℝ → ℝ} (hmeas : Measurable h) (hh : ∀ x, h x ≤ x)
    (hint : Integrable h ρ) {a b : ℝ} (hab : a < b) (hsupp : (ρ.map h) (Set.Icc a b)ᶜ = 0)
    {πs πd : ι → ℝ} (hs0 : ∀ k, 0 ≤ πs k) (hs1 : ∑ k, πs k = 1) (hy : ∀ k, 0 ≤ y k)
    (hdom : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
      ∫ x, φ x ∂(ρ.map h) ≤ ∑ k, πs k * φ (y k))
    (hd0 : ∀ k, 0 ≤ πd k) (hds : ∀ k, πd k ≤ πs k) {kbot : ι} (hbot : ∀ k, y kbot ≤ y k)
    {g : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (hg0 : g 0 = 0) (hgs : ∀ j < N, g j < g (j + 1))
    {πu : ι → ℝ} (hπu : ∀ k, relocate πd kbot k ≤ πu k) (U : ℕ → ℕ → ℝ)
    (hbase : ∀ i ≤ N, putFin (relocate πd kbot) y 0 (g i) ≤ U 0 i)
    (hstep : ∀ m, ∀ i ≤ N, ∑ k, πu k * reverseCont g N (U m) (g i - y k) ≤ U (m + 1) i)
    (m : ℕ) {s : ℝ} (hs : s ≤ g N) :
    putLaw ρ m s ≤ reverseCont g N (U m) s := by
  have hr0 := (relocate_normalized hs1 hd0 hds kbot).1
  calc putLaw ρ m s ≤ putLaw (ρ.map h) m s := putLaw_le_map ρ hρ hmeas hh hint m s
    _ ≤ putFin πs y m s := putLaw_le_putFin hab hsupp hs0 (fun φ hφ _ => hdom φ hφ) m s
    _ ≤ putFin (relocate πd kbot) y m s := putFin_le_relocate_bot hs0 hs1 hd0 hds hbot m s
    _ ≤ reverseCont g N (U m) s := putFin_le_eval hN hg0 hgs hr0 hy hπu U hbase hstep m hs

end Soundness

/-! ## Privacy-loss profiles of finite pairs -/

section Profiles

variable {κ : Type*} [Fintype κ]

/-- The finite measure with masses `w i` on a finite type; on `Fin n` it is `finMeasure`. -/
noncomputable def discreteMeasure [MeasurableSpace κ] (w : κ → ℝ) : Measure κ :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

theorem finMeasure_eq_discreteMeasure {n : ℕ} (w : Fin n → ℝ) :
    finMeasure w = discreteMeasure w := rfl

variable [MeasurableSpace κ] [MeasurableSingletonClass κ]

theorem discreteMeasure_toReal (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (A : Set κ) :
    (discreteMeasure w A).toReal = ∑ i, A.indicator w i := by
  rw [discreteMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_sum fun i _ => by
      simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by by_cases h : i ∈ A <;> simp [Set.indicator, h])]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ∈ A <;> simp [Measure.dirac_apply, Set.indicator, h, hw i]

instance (w : κ → ℝ) : IsFiniteMeasure (discreteMeasure w) := by
  constructor
  simp only [discreteMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  exact ENNReal.sum_lt_top.2 fun i _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- The hockey-stick divergence of a finite pair is the sum of positive parts
`∑ i (R i - e^ε S i)_+`. -/
theorem hockeyStick_discreteMeasure (R S : κ → ℝ) (hR : ∀ i, 0 ≤ R i) (hS : ∀ i, 0 ≤ S i)
    (ε : ℝ) :
    hockeyStick (discreteMeasure R) (discreteMeasure S) ε =
      ∑ i, max (R i - Real.exp ε * S i) 0 := by
  refine le_antisymm (hockeyStick_le fun A _ => ?_) ?_
  · rw [discreteMeasure_toReal R hR, discreteMeasure_toReal S hS, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : i ∈ A <;> simp [Set.indicator, h]
  · set A : Set κ := {i | Real.exp ε * S i < R i}
    have hA : MeasurableSet A := A.toFinite.measurableSet
    refine le_trans (le_of_eq ?_) (le_hockeyStick ε hA)
    rw [discreteMeasure_toReal R hR, discreteMeasure_toReal S hS, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : Real.exp ε * S i < R i
    · simp [A, Set.indicator, h, h.le]
    · simp [A, Set.indicator, h, (not_lt.1 h)]

/-- `hockeyStick_discreteMeasure` for the finite measures `finMeasure` on `Fin n`. -/
theorem hockeyStick_finMeasure {n : ℕ} (R S : Fin n → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hS : ∀ i, 0 ≤ S i) (ε : ℝ) :
    hockeyStick (finMeasure R) (finMeasure S) ε = ∑ i, max (R i - Real.exp ε * S i) 0 :=
  hockeyStick_discreteMeasure R S hR hS ε

end Profiles

section ProfileBounds

variable {κ : Type*} [Fintype κ]

private theorem posPart_eq_sub_min (a b : ℝ) : max (a - b) 0 = a - min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]

/-- Upper profile `eq:upperpld`. Let `A` be the atoms of finite loss, with
`R i ≤ r^(n i) S i` on `A` (equality for the shuffled pair of `eq:atoms`; upward-rounded
losses also qualify), and let `0 ≤ w j ≤ ∑_{i ∈ A, n i = j} R i` be retained real-law masses
at loss `j log r`. Every mass outside the retained array, singular atoms included, is paid
at infinite loss, and each factor `e^ε r^(-j)` may be rounded down to `c j`. The reverse
direction is the same statement for `(S, R)` with indices `-n i`. -/
theorem posPart_sum_le_upperProfile (R S : κ → ℝ) (hR : ∀ i, 0 ≤ R i) (hS : ∀ i, 0 ≤ S i)
    (hR1 : ∑ i, R i ≤ 1) {r : ℝ} (hr : 0 < r) (A : Finset κ) (n : κ → ℤ)
    (hn : ∀ i ∈ A, R i ≤ r ^ n i * S i) (T : Finset ℤ) (w : ℤ → ℝ)
    (hw0 : ∀ j ∈ T, 0 ≤ w j) (hw : ∀ j ∈ T, w j ≤ ∑ i ∈ A with n i = j, R i) (ε : ℝ)
    (c : ℤ → ℝ) (hc : ∀ j ∈ T, c j ≤ Real.exp ε * r ^ (-j)) :
    ∑ i, max (R i - Real.exp ε * S i) 0 ≤ 1 - ∑ j ∈ T, w j * min 1 (c j) := by
  set m : ℤ → ℝ := fun j => min 1 (Real.exp ε * r ^ (-j)) with hm
  have hm0 : ∀ j, 0 ≤ m j := fun j =>
    le_min zero_le_one (mul_nonneg (Real.exp_pos ε).le (zpow_nonneg hr.le _))
  have hmin0 : ∀ i, 0 ≤ min (R i) (Real.exp ε * S i) := fun i =>
    le_min (hR i) (mul_nonneg (Real.exp_pos ε).le (hS i))
  -- On finite-loss atoms the overlap `min (R i) (e^ε S i)` is at least `R i * m (n i)`.
  have hA : ∀ i ∈ A, R i * m (n i) ≤ min (R i) (Real.exp ε * S i) := by
    intro i hi
    have hS' : r ^ (-n i) * R i ≤ S i := by
      have h := mul_le_mul_of_nonneg_left (hn i hi) (zpow_nonneg hr.le (-n i))
      rwa [← mul_assoc, ← zpow_add₀ hr.ne', neg_add_cancel, zpow_zero, one_mul] at h
    rw [hm, mul_min_of_nonneg _ _ (hR i), mul_one]
    refine min_le_min_left _ ?_
    have := mul_le_mul_of_nonneg_left hS' (Real.exp_pos ε).le
    linarith
  have hsum : ∑ i, max (R i - Real.exp ε * S i) 0 =
      ∑ i, R i - ∑ i, min (R i) (Real.exp ε * S i) := by
    simp_rw [posPart_eq_sub_min]
    exact Finset.sum_sub_distrib _ _
  have hcover : ∑ j ∈ T, w j * min 1 (c j) ≤ ∑ i ∈ A, R i * m (n i) := by
    calc ∑ j ∈ T, w j * min 1 (c j)
        ≤ ∑ j ∈ T, (∑ i ∈ A with n i = j, R i) * m j := by
          refine Finset.sum_le_sum fun j hj => ?_
          calc w j * min 1 (c j) ≤ w j * m j :=
                mul_le_mul_of_nonneg_left (min_le_min_left 1 (hc j hj)) (hw0 j hj)
            _ ≤ (∑ i ∈ A with n i = j, R i) * m j :=
                mul_le_mul_of_nonneg_right (hw j hj) (hm0 j)
      _ = ∑ j ∈ T, ∑ i ∈ A with n i = j, R i * m (n i) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.1 hi).2]
      _ = ∑ i ∈ A with n i ∈ T, R i * m (n i) := Finset.sum_fiberwise_eq_sum_filter _ _ _ _
      _ ≤ ∑ i ∈ A, R i * m (n i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun i _ _ => mul_nonneg (hR i) (hm0 _)
  have hAuniv : ∑ i ∈ A, R i * m (n i) ≤ ∑ i, min (R i) (Real.exp ε * S i) :=
    (Finset.sum_le_sum hA).trans (Finset.sum_le_univ_sum_of_nonneg hmin0)
  rw [hsum]
  linarith

/-- `ℓ ↦ (1 - e^(ε - ℓ))_+` is nondecreasing (subsection "Lower products from the maximum
statistic" of `app:certificate`). -/
theorem monotone_lowerFactor (ε : ℝ) : Monotone fun ℓ : ℝ => max (1 - Real.exp (ε - ℓ)) 0 :=
  fun a b hab => max_le_max (by linarith [Real.exp_le_exp.2 (show ε - b ≤ ε - a by linarith)])
    le_rfl

/-- Lower profile from downward-rounded losses. If every retained atom `i ∈ A` has loss
index `n i` with `r^(n i) S i ≤ R i`, and `w j ≤ ∑_{i ∈ A, n i = j} R i`, then
`∑ j w j (1 - e^ε r^(-j))_+` is at most `∑ i (R i - e^ε S i)_+`. Missing mass is discarded. -/
theorem lowerProfile_le_posPart_sum (R S : κ → ℝ) (hR : ∀ i, 0 ≤ R i)
    {r : ℝ} (hr : 0 < r) (A : Finset κ) (n : κ → ℤ) (hn : ∀ i ∈ A, r ^ n i * S i ≤ R i)
    (T : Finset ℤ) (w : ℤ → ℝ)
    (hw : ∀ j ∈ T, w j ≤ ∑ i ∈ A with n i = j, R i) (ε : ℝ) :
    ∑ j ∈ T, w j * max (1 - Real.exp ε * r ^ (-j)) 0 ≤ ∑ i, max (R i - Real.exp ε * S i) 0 := by
  set m : ℤ → ℝ := fun j => max (1 - Real.exp ε * r ^ (-j)) 0 with hm
  have hm0 : ∀ j, 0 ≤ m j := fun j => le_max_right _ _
  have hpos0 : ∀ i, 0 ≤ max (R i - Real.exp ε * S i) 0 := fun i => le_max_right _ _
  have hA : ∀ i ∈ A, R i * m (n i) ≤ max (R i - Real.exp ε * S i) 0 := by
    intro i hi
    have hS' : S i ≤ r ^ (-n i) * R i := by
      have h := mul_le_mul_of_nonneg_left (hn i hi) (zpow_nonneg hr.le (-n i))
      rwa [← mul_assoc, ← zpow_add₀ hr.ne', neg_add_cancel, zpow_zero, one_mul] at h
    rw [hm, mul_max_of_nonneg _ _ (hR i), mul_zero]
    refine max_le_max ?_ le_rfl
    have := mul_le_mul_of_nonneg_left hS' (Real.exp_pos ε).le
    nlinarith
  calc ∑ j ∈ T, w j * m j
      ≤ ∑ j ∈ T, (∑ i ∈ A with n i = j, R i) * m j :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hw j hj) (hm0 j)
    _ = ∑ j ∈ T, ∑ i ∈ A with n i = j, R i * m (n i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.1 hi).2]
    _ = ∑ i ∈ A with n i ∈ T, R i * m (n i) := Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ i ∈ A with n i ∈ T, max (R i - Real.exp ε * S i) 0 :=
        Finset.sum_le_sum fun i hi => hA i (Finset.mem_filter.1 hi).1
    _ ≤ ∑ i, max (R i - Real.exp ε * S i) 0 := Finset.sum_le_univ_sum_of_nonneg hpos0

/-- `lowerProfile_le_posPart_sum` stated with exact losses `ℓ i = log (R i / S i)` of a pair
with positive masses and loss indices rounded down, `n i log r ≤ ℓ i`. -/
theorem lowerProfile_le_posPart_sum_log (R S : κ → ℝ) (hR : ∀ i, 0 < R i) (hS : ∀ i, 0 < S i)
    {r : ℝ} (hr : 0 < r) (A : Finset κ) (n : κ → ℤ)
    (hn : ∀ i ∈ A, (n i : ℝ) * Real.log r ≤ Real.log (R i / S i))
    (T : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ j ∈ T, w j ≤ ∑ i ∈ A with n i = j, R i) (ε : ℝ) :
    ∑ j ∈ T, w j * max (1 - Real.exp ε * r ^ (-j)) 0 ≤ ∑ i, max (R i - Real.exp ε * S i) 0 := by
  refine lowerProfile_le_posPart_sum R S (fun i => (hR i).le) hr A n
    (fun i hi => ?_) T w hw ε
  have h1 : r ^ n i = Real.exp (n i * Real.log r) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hr, mul_comm]
  have h2 : r ^ n i ≤ R i / S i := by
    rw [h1, ← Real.exp_log (div_pos (hR i) (hS i))]
    exact Real.exp_le_exp.2 (hn i hi)
  rwa [le_div_iff₀ (hS i)] at h2

end ProfileBounds

/-! ## Products and lower submeasures -/

section Products

/-- Real-law mass of the finite-loss atoms `A` at loss index `j`. -/
def lossMass {α : Type*} (R : α → ℝ) (A : Finset α) (n : α → ℤ) (j : ℤ) : ℝ :=
  ∑ i ∈ A with n i = j, R i

/-- The array `w`, indexed by the finite set `T` of loss indices, is a lower submeasure
of the loss-index masses `M`. -/
def IsLowerSub (M : ℤ → ℝ) (T : Finset ℤ) (w : ℤ → ℝ) : Prop :=
  ∀ j ∈ T, 0 ≤ w j ∧ w j ≤ M j

/-- Exact convolution of arrays indexed by `T₁` and `T₂`. -/
def conv (T₁ : Finset ℤ) (w₁ : ℤ → ℝ) (T₂ : Finset ℤ) (w₂ : ℤ → ℝ) (j : ℤ) : ℝ :=
  ∑ p ∈ T₁ ×ˢ T₂ with p.1 + p.2 = j, w₁ p.1 * w₂ p.2

theorem lossMass_nonneg {α : Type*} {R : α → ℝ} {A : Finset α} (hR : ∀ i ∈ A, 0 ≤ R i)
    (n : α → ℤ) (j : ℤ) : 0 ≤ lossMass R A n j :=
  Finset.sum_nonneg fun i hi => hR i (Finset.mem_filter.1 hi).1

theorem conv_nonneg {T₁ T₂ : Finset ℤ} {w₁ w₂ : ℤ → ℝ} (h₁ : ∀ j ∈ T₁, 0 ≤ w₁ j)
    (h₂ : ∀ j ∈ T₂, 0 ≤ w₂ j) (j : ℤ) : 0 ≤ conv T₁ w₁ T₂ w₂ j := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp' := Finset.mem_product.1 (Finset.mem_filter.1 hp).1
  exact mul_nonneg (h₁ _ hp'.1) (h₂ _ hp'.2)

/-- The convolution of two loss-index mass functions, restricted to index sets `T₁`, `T₂`,
is the product-law mass of the atom pairs whose indices lie in `T₁ × T₂` and add to `j`. -/
theorem conv_lossMass {α β : Type*} (R₁ : α → ℝ) (A₁ : Finset α) (n₁ : α → ℤ) (R₂ : β → ℝ)
    (A₂ : Finset β) (n₂ : β → ℤ) (T₁ T₂ : Finset ℤ) (j : ℤ) :
    conv T₁ (lossMass R₁ A₁ n₁) T₂ (lossMass R₂ A₂ n₂) j =
      ∑ q ∈ A₁ ×ˢ A₂ with (n₁ q.1, n₂ q.2) ∈ (T₁ ×ˢ T₂).filter fun p => p.1 + p.2 = j,
        R₁ q.1 * R₂ q.2 := by
  have hfiber : ∀ p : ℤ × ℤ, lossMass R₁ A₁ n₁ p.1 * lossMass R₂ A₂ n₂ p.2 =
      ∑ q ∈ A₁ ×ˢ A₂ with (n₁ q.1, n₂ q.2) = p, R₁ q.1 * R₂ q.2 := by
    intro p
    rw [lossMass, lossMass, Finset.sum_mul_sum, ← Finset.sum_product']
    have hset : (A₁ ×ˢ A₂).filter (fun q => (n₁ q.1, n₂ q.2) = p) =
        (A₁.filter fun i => n₁ i = p.1) ×ˢ (A₂.filter fun i => n₂ i = p.2) := by
      rw [← Finset.filter_product]
      congr 1
      funext q
      simp [Prod.ext_iff]
    rw [hset]
  rw [conv, Finset.sum_congr rfl fun p _ => hfiber p]
  exact Finset.sum_fiberwise_eq_sum_filter _ _ _ _

/-- The loss-index masses of a product of two laws are the convolution of their loss-index
masses, when the index sets contain every finite-loss index. -/
theorem conv_lossMass_eq_prod {α β : Type*} (R₁ : α → ℝ) (A₁ : Finset α) (n₁ : α → ℤ)
    (R₂ : β → ℝ) (A₂ : Finset β) (n₂ : β → ℤ) {T₁ T₂ : Finset ℤ} (hT₁ : ∀ i ∈ A₁, n₁ i ∈ T₁)
    (hT₂ : ∀ i ∈ A₂, n₂ i ∈ T₂) (j : ℤ) :
    conv T₁ (lossMass R₁ A₁ n₁) T₂ (lossMass R₂ A₂ n₂) j =
      lossMass (fun q : α × β => R₁ q.1 * R₂ q.2) (A₁ ×ˢ A₂) (fun q => n₁ q.1 + n₂ q.2) j := by
  rw [conv_lossMass, lossMass]
  refine Finset.sum_congr (Finset.filter_congr fun q hq => ?_) fun _ _ => rfl
  have hq' := Finset.mem_product.1 hq
  simp [hT₁ _ hq'.1, hT₂ _ hq'.2]

/-- Convolution is monotone on nonnegative arrays: the convolution of lower submeasures of
two independent laws is dominated by the loss-index masses of the product law. -/
theorem conv_le_lossMass_prod {α β : Type*}
    {R₁ : α → ℝ} {A₁ : Finset α} {n₁ : α → ℤ} {R₂ : β → ℝ} {A₂ : Finset β} {n₂ : β → ℤ}
    (hR₁ : ∀ i ∈ A₁, 0 ≤ R₁ i) (hR₂ : ∀ i ∈ A₂, 0 ≤ R₂ i) {T₁ T₂ : Finset ℤ}
    {w₁ w₂ : ℤ → ℝ} (h₁ : IsLowerSub (lossMass R₁ A₁ n₁) T₁ w₁)
    (h₂ : IsLowerSub (lossMass R₂ A₂ n₂) T₂ w₂) (j : ℤ) :
    conv T₁ w₁ T₂ w₂ j ≤
      lossMass (fun q : α × β => R₁ q.1 * R₂ q.2) (A₁ ×ˢ A₂) (fun q => n₁ q.1 + n₂ q.2) j := by
  have hmono : conv T₁ w₁ T₂ w₂ j ≤ conv T₁ (lossMass R₁ A₁ n₁) T₂ (lossMass R₂ A₂ n₂) j := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := Finset.mem_product.1 (Finset.mem_filter.1 hp).1
    exact mul_le_mul (h₁ _ hp'.1).2 (h₂ _ hp'.2).2 (h₂ _ hp'.2).1 (lossMass_nonneg hR₁ n₁ _)
  refine hmono.trans ?_
  rw [conv_lossMass, lossMass]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ => ?_
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, (Finset.mem_filter.1 hq.2).2⟩
  · have hq' := Finset.mem_product.1 (Finset.mem_filter.1 hq).1
    exact mul_nonneg (hR₁ _ hq'.1) (hR₂ _ hq'.2)

variable {κ : Type*}

/-- Masses `∏ e, R (x e)` of the `E`-fold product law on `Fin E → κ`. -/
def prodMass (R : κ → ℝ) (E : ℕ) (x : Fin E → κ) : ℝ := ∏ e, R (x e)

/-- Total loss index `∑ e, n (x e)` of a product atom. -/
def prodIndex (n : κ → ℤ) (E : ℕ) (x : Fin E → κ) : ℤ := ∑ e, n (x e)

/-- Product atoms all of whose coordinates lie in the finite-loss set `A`. -/
def prodSet (A : Finset κ) (E : ℕ) : Finset (Fin E → κ) := Fintype.piFinset fun _ => A

theorem prodMass_nonneg {R : κ → ℝ} {A : Finset κ} (hR : ∀ i ∈ A, 0 ≤ R i) {E : ℕ}
    {x : Fin E → κ} (hx : x ∈ prodSet A E) : 0 ≤ prodMass R E x :=
  Finset.prod_nonneg fun e _ => hR _ (Fintype.mem_piFinset.1 hx e)

/-- The empty product is the point mass at loss index zero. -/
theorem lossMass_prod_zero [Fintype κ] (R : κ → ℝ) (A : Finset κ) (n : κ → ℤ) (j : ℤ) :
    lossMass (prodMass R 0) (prodSet A 0) (prodIndex n 0) j = if j = 0 then 1 else 0 := by
  have hset : prodSet A 0 = Finset.univ := by
    ext x
    simp [prodSet]
  rw [lossMass, hset]
  by_cases hj : j = 0
  · subst hj
    simp [prodMass, prodIndex]
  · have : ∀ x : Fin 0 → κ, prodIndex n 0 x ≠ j := fun x => by
      simpa [prodIndex] using Ne.symm hj
    simp [hj, this]

/-- The one-fold product has the loss-index masses of the original law. -/
theorem lossMass_prod_one (R : κ → ℝ) (A : Finset κ) (n : κ → ℤ) (j : ℤ) :
    lossMass (prodMass R 1) (prodSet A 1) (prodIndex n 1) j = lossMass R A n j := by
  refine Finset.sum_equiv (Equiv.funUnique (Fin 1) κ) (fun x => ?_) (fun x _ => ?_)
  · simp [prodSet, prodIndex, Fintype.mem_piFinset, Fin.forall_fin_one]
  · simp [prodMass]

/-- Splitting `Fin (E₁ + E₂)` identifies the `(E₁ + E₂)`-fold product with the product of
the `E₁`-fold and `E₂`-fold laws, loss indices adding. -/
theorem lossMass_prod_add (R : κ → ℝ) (A : Finset κ) (n : κ → ℤ) (E₁ E₂ : ℕ) (j : ℤ) :
    lossMass (prodMass R (E₁ + E₂)) (prodSet A (E₁ + E₂)) (prodIndex n (E₁ + E₂)) j =
      lossMass (fun q : (Fin E₁ → κ) × (Fin E₂ → κ) => prodMass R E₁ q.1 * prodMass R E₂ q.2)
        (prodSet A E₁ ×ˢ prodSet A E₂) (fun q => prodIndex n E₁ q.1 + prodIndex n E₂ q.2) j := by
  symm
  refine Finset.sum_equiv (Fin.appendEquiv E₁ E₂) (fun q => ?_) (fun q _ => ?_)
  · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
    simp only [prodSet, Fintype.mem_piFinset, prodIndex, Fin.appendEquiv_apply,
      Fin.forall_fin_add, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  · simp only [prodMass, Fin.appendEquiv_apply, Fin.prod_univ_add, Fin.append_left,
      Fin.append_right]

/-- The real-law mass of the `(E + 1)`-fold product at total loss index `j` is the
convolution of the `E`-fold masses with the one-step masses. -/
theorem lossMass_prod_succ (R : κ → ℝ) (A : Finset κ) (n : κ → ℤ) (E : ℕ) (j : ℤ) :
    lossMass (prodMass R (E + 1)) (prodSet A (E + 1)) (prodIndex n (E + 1)) j =
      conv ((prodSet A E).image (prodIndex n E))
        (lossMass (prodMass R E) (prodSet A E) (prodIndex n E)) (A.image n)
        (lossMass R A n) j := by
  have hset : (prodSet A 1).image (prodIndex n 1) = A.image n := by
    ext j
    simp only [Finset.mem_image, prodSet, Fintype.mem_piFinset, prodIndex,
      Finset.univ_unique, Finset.sum_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x default, hx default, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨fun _ => i, fun _ => hi, rfl⟩
  have hfun : lossMass (prodMass R 1) (prodSet A 1) (prodIndex n 1) = lossMass R A n :=
    funext (lossMass_prod_one R A n)
  rw [← hset, ← hfun, lossMass_prod_add, conv_lossMass_eq_prod _ _ _ _ _ _
    (fun x hx => Finset.mem_image_of_mem _ hx) (fun x hx => Finset.mem_image_of_mem _ hx)]

variable {R : κ → ℝ} {A : Finset κ} {n : κ → ℤ}

/-- The certificate's starting array, mass one at index zero, is a lower submeasure of the
empty product. -/
theorem isLowerSub_prod_zero [Fintype κ] :
    IsLowerSub (lossMass (prodMass R 0) (prodSet A 0) (prodIndex n 0)) {0}
      fun j => if j = 0 then 1 else 0 := by
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  simp [lossMass_prod_zero]

/-- A lower submeasure of the one-step law is a lower submeasure of the one-fold product. -/
theorem isLowerSub_prod_one {T : Finset ℤ} {w : ℤ → ℝ} (h : IsLowerSub (lossMass R A n) T w) :
    IsLowerSub (lossMass (prodMass R 1) (prodSet A 1) (prodIndex n 1)) T w := by
  intro j hj
  rw [lossMass_prod_one]
  exact h j hj

/-- Lower submeasures survive the certificate's convolution step: if `w₁`, `w₂` are lower
submeasures of the `E₁`-fold and `E₂`-fold products and `0 ≤ w j ≤ (w₁ * w₂)(j)` on `T`
(downward rounding of the exact convolution, followed by any cropping), then `w` is a lower
submeasure of the `(E₁ + E₂)`-fold product. -/
theorem isLowerSub_prod_add (hR : ∀ i ∈ A, 0 ≤ R i) {E₁ E₂ : ℕ} {T₁ T₂ T : Finset ℤ}
    {w₁ w₂ w : ℤ → ℝ}
    (h₁ : IsLowerSub (lossMass (prodMass R E₁) (prodSet A E₁) (prodIndex n E₁)) T₁ w₁)
    (h₂ : IsLowerSub (lossMass (prodMass R E₂) (prodSet A E₂) (prodIndex n E₂)) T₂ w₂)
    (h : ∀ j ∈ T, 0 ≤ w j ∧ w j ≤ conv T₁ w₁ T₂ w₂ j) :
    IsLowerSub (lossMass (prodMass R (E₁ + E₂)) (prodSet A (E₁ + E₂)) (prodIndex n (E₁ + E₂)))
      T w := by
  intro j hj
  refine ⟨(h j hj).1, (h j hj).2.trans ?_⟩
  rw [lossMass_prod_add]
  exact conv_le_lossMass_prod (fun x hx => prodMass_nonneg hR hx)
    (fun x hx => prodMass_nonneg hR hx) h₁ h₂ j

/-- Iterated form used by the epoch loop: starting from the point mass at zero and
convolving with a lower submeasure `w₁` of the one-step law, rounding down and cropping
after each step, gives a lower submeasure of every `E`-fold product. -/
theorem isLowerSub_prod_iterate [Fintype κ] (hR : ∀ i ∈ A, 0 ≤ R i) {T₁ : Finset ℤ} {w₁ : ℤ → ℝ}
    (h₁ : IsLowerSub (lossMass R A n) T₁ w₁) (T : ℕ → Finset ℤ) (w : ℕ → ℤ → ℝ)
    (h0 : T 0 = {0}) (hw0 : w 0 = fun j => if j = 0 then 1 else 0)
    (hstep : ∀ E, ∀ j ∈ T (E + 1), 0 ≤ w (E + 1) j ∧ w (E + 1) j ≤ conv (T E) (w E) T₁ w₁ j)
    (E : ℕ) : IsLowerSub (lossMass (prodMass R E) (prodSet A E) (prodIndex n E)) (T E) (w E) := by
  induction E with
  | zero => rw [h0, hw0]; exact isLowerSub_prod_zero
  | succ E ih => exact isLowerSub_prod_add hR ih (isLowerSub_prod_one h₁) (hstep E)

private theorem prod_zpow_eq {α : Type*} (s : Finset α) {r : ℝ} (hr : r ≠ 0) (m : α → ℤ) :
    ∏ e ∈ s, r ^ m e = r ^ (∑ e ∈ s, m e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hr, ih]

theorem sum_prodMass [Fintype κ] (R : κ → ℝ) (E : ℕ) : ∑ x, prodMass R E x = (∑ i, R i) ^ E := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  simp [prodMass, Fintype.piFinset_univ]

/-- Upper profile `eq:upperpld` for the `E`-fold product pair, with any lower submeasure `w`
of the product's real-law loss-index masses, for example the certificate's computed array. -/
theorem posPart_sum_prod_le_upperProfile [Fintype κ] (S : κ → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hS : ∀ i, 0 ≤ S i) (hR1 : ∑ i, R i ≤ 1) {r : ℝ} (hr : 0 < r)
    (hn : ∀ i ∈ A, R i ≤ r ^ n i * S i) (E : ℕ) {T : Finset ℤ} {w : ℤ → ℝ}
    (hw : IsLowerSub (lossMass (prodMass R E) (prodSet A E) (prodIndex n E)) T w) (ε : ℝ)
    (c : ℤ → ℝ) (hc : ∀ j ∈ T, c j ≤ Real.exp ε * r ^ (-j)) :
    ∑ x : Fin E → κ, max (prodMass R E x - Real.exp ε * prodMass S E x) 0 ≤
      1 - ∑ j ∈ T, w j * min 1 (c j) := by
  refine posPart_sum_le_upperProfile (prodMass R E) (prodMass S E)
    (fun x => Finset.prod_nonneg fun e _ => hR _) (fun x => Finset.prod_nonneg fun e _ => hS _)
    ?_ hr (prodSet A E) (prodIndex n E) (fun x hx => ?_) T w (fun j hj => (hw j hj).1)
    (fun j hj => (hw j hj).2) ε c hc
  · rw [sum_prodMass]
    exact pow_le_one₀ (Finset.sum_nonneg fun i _ => hR i) hR1
  · have hx' := Fintype.mem_piFinset.1 hx
    rw [prodMass, prodMass, prodIndex, ← prod_zpow_eq _ hr.ne', ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun e _ => hR _) fun e _ => hn _ (hx' e)

/-- Lower profile for the `E`-fold product pair: with loss indices rounded down on every
retained atom, any lower submeasure of the product's real-law loss-index masses gives a
lower bound on `∑ x (R^E x - e^ε S^E x)_+`. -/
theorem lowerProfile_prod_le_posPart_sum [Fintype κ] (S : κ → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hS : ∀ i, 0 ≤ S i) {r : ℝ} (hr : 0 < r) (hn : ∀ i ∈ A, r ^ n i * S i ≤ R i) (E : ℕ)
    {T : Finset ℤ}
    {w : ℤ → ℝ} (hw : IsLowerSub (lossMass (prodMass R E) (prodSet A E) (prodIndex n E)) T w)
    (ε : ℝ) :
    ∑ j ∈ T, w j * max (1 - Real.exp ε * r ^ (-j)) 0 ≤
      ∑ x : Fin E → κ, max (prodMass R E x - Real.exp ε * prodMass S E x) 0 := by
  refine lowerProfile_le_posPart_sum (prodMass R E) (prodMass S E)
    (fun x => Finset.prod_nonneg fun e _ => hR _) hr (prodSet A E) (prodIndex n E)
    (fun x hx => ?_) T w (fun j hj => (hw j hj).2) ε
  have hx' := Fintype.mem_piFinset.1 hx
  rw [prodMass, prodMass, prodIndex, ← prod_zpow_eq _ hr.ne', ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun e _ => mul_nonneg (zpow_nonneg hr.le _) (hS _))
    fun e _ => hn _ (hx' e)

section Measures

variable [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

theorem discreteMeasure_singleton (w : κ → ℝ) (a : κ) :
    discreteMeasure w {a} = ENNReal.ofReal (w a) := by
  rw [discreteMeasure, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Set.indicator, hb]
  · simp

/-- The `E`-fold product of a discrete law is the discrete law with masses `prodMass`. -/
theorem pi_discreteMeasure (R : κ → ℝ) (hR : ∀ i, 0 ≤ R i) (E : ℕ) :
    Measure.pi (fun _ : Fin E => discreteMeasure R) = discreteMeasure (prodMass R E) := by
  rw [Measure.ext_iff_singleton]
  intro x
  rw [← Set.univ_pi_singleton, Measure.pi_pi, Set.univ_pi_singleton, discreteMeasure_singleton,
    prodMass, ENNReal.ofReal_prod_of_nonneg fun e _ => hR _]
  simp only [discreteMeasure_singleton]

/-- `eq:upperpld` for the single pair, stated for its hockey-stick divergence. -/
theorem hockeyStick_le_upperProfile (S : κ → ℝ) (hR : ∀ i, 0 ≤ R i) (hS : ∀ i, 0 ≤ S i)
    (hR1 : ∑ i, R i ≤ 1) {r : ℝ} (hr : 0 < r) (hn : ∀ i ∈ A, R i ≤ r ^ n i * S i)
    {T : Finset ℤ} {w : ℤ → ℝ} (hw : IsLowerSub (lossMass R A n) T w) (ε : ℝ) (c : ℤ → ℝ)
    (hc : ∀ j ∈ T, c j ≤ Real.exp ε * r ^ (-j)) :
    hockeyStick (discreteMeasure R) (discreteMeasure S) ε ≤ 1 - ∑ j ∈ T, w j * min 1 (c j) := by
  rw [hockeyStick_discreteMeasure R S hR hS]
  exact posPart_sum_le_upperProfile R S hR hS hR1 hr A n hn T w (fun j hj => (hw j hj).1)
    (fun j hj => (hw j hj).2) ε c hc

/-- `eq:upperpld` for the `E`-fold product pair `(R^{⊗E}, S^{⊗E})`, with any lower submeasure
of the product's real-law loss-index masses, such as the array produced by
`isLowerSub_prod_iterate` or `isLowerSub_prod_add`. -/
theorem hockeyStick_pi_le_upperProfile (S : κ → ℝ) (hR : ∀ i, 0 ≤ R i) (hS : ∀ i, 0 ≤ S i)
    (hR1 : ∑ i, R i ≤ 1) {r : ℝ} (hr : 0 < r) (hn : ∀ i ∈ A, R i ≤ r ^ n i * S i) (E : ℕ)
    {T : Finset ℤ} {w : ℤ → ℝ}
    (hw : IsLowerSub (lossMass (prodMass R E) (prodSet A E) (prodIndex n E)) T w) (ε : ℝ)
    (c : ℤ → ℝ) (hc : ∀ j ∈ T, c j ≤ Real.exp ε * r ^ (-j)) :
    hockeyStick (Measure.pi fun _ : Fin E => discreteMeasure R)
        (Measure.pi fun _ : Fin E => discreteMeasure S) ε ≤
      1 - ∑ j ∈ T, w j * min 1 (c j) := by
  rw [pi_discreteMeasure R hR, pi_discreteMeasure S hS,
    hockeyStick_discreteMeasure (prodMass R E) (prodMass S E)
      (fun x => Finset.prod_nonneg fun e _ => hR _)
      (fun x => Finset.prod_nonneg fun e _ => hS _)]
  exact posPart_sum_prod_le_upperProfile S hR hS hR1 hr hn E hw ε c hc

/-- Lower profile of the `E`-fold product pair, stated for its hockey-stick divergence. -/
theorem lowerProfile_le_hockeyStick_pi (S : κ → ℝ) (hR : ∀ i, 0 ≤ R i) (hS : ∀ i, 0 ≤ S i)
    {r : ℝ} (hr : 0 < r) (hn : ∀ i ∈ A, r ^ n i * S i ≤ R i) (E : ℕ) {T : Finset ℤ}
    {w : ℤ → ℝ} (hw : IsLowerSub (lossMass (prodMass R E) (prodSet A E) (prodIndex n E)) T w)
    (ε : ℝ) :
    ∑ j ∈ T, w j * max (1 - Real.exp ε * r ^ (-j)) 0 ≤
      hockeyStick (Measure.pi fun _ : Fin E => discreteMeasure R)
        (Measure.pi fun _ : Fin E => discreteMeasure S) ε := by
  rw [pi_discreteMeasure R hR, pi_discreteMeasure S hS,
    hockeyStick_discreteMeasure (prodMass R E) (prodMass S E)
      (fun x => Finset.prod_nonneg fun e _ => hR _)
      (fun x => Finset.prod_nonneg fun e _ => hS _)]
  exact lowerProfile_prod_le_posPart_sum S hR hS hr hn E hw ε

end Measures

end Products

/-! ## Exact integer packing -/

section Packing

/-- Coefficient `k` of the exact convolution of natural-number arrays `a` and `b`. -/
def natConv {n m : ℕ} (a : Fin n → ℕ) (b : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin m, if (i : ℕ) + (j : ℕ) = k then a i * b j else 0

/-- The integer `∑ i, a i * B ^ i` packing the array `a` in base `B`. -/
def packNat {n : ℕ} (a : Fin n → ℕ) (B : ℕ) : ℕ := ∑ i, a i * B ^ (i : ℕ)

variable {n m : ℕ}

theorem natConv_le_mul_sum (a : Fin n → ℕ) (b : Fin m → ℕ) (k : ℕ) :
    natConv a b k ≤ (∑ i, a i) * ∑ j, b j := by
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by split_ifs <;> simp

/-- Arrays of total mass at most `2^56` have convolution coefficients at most `2^112`, below
the packing base `2^128` (subsection "Rational testing envelopes and upper products"). -/
theorem natConv_le_pow_56 (a : Fin n → ℕ) (b : Fin m → ℕ) (ha : ∑ i, a i ≤ 2 ^ 56)
    (hb : ∑ j, b j ≤ 2 ^ 56) (k : ℕ) : natConv a b k ≤ 2 ^ 112 ∧ natConv a b k < 2 ^ 128 := by
  have h : natConv a b k ≤ 2 ^ 112 :=
    (natConv_le_mul_sum a b k).trans ((Nat.mul_le_mul ha hb).trans (by norm_num))
  exact ⟨h, h.trans_lt (by norm_num)⟩

/-- Arrays of total mass at most `2^72` have convolution coefficients at most `2^144`, below
the packing base `2^192` (subsection "Lower products from the maximum statistic"). -/
theorem natConv_le_pow_72 (a : Fin n → ℕ) (b : Fin m → ℕ) (ha : ∑ i, a i ≤ 2 ^ 72)
    (hb : ∑ j, b j ≤ 2 ^ 72) (k : ℕ) : natConv a b k ≤ 2 ^ 144 ∧ natConv a b k < 2 ^ 192 := by
  have h : natConv a b k ≤ 2 ^ 144 :=
    (natConv_le_mul_sum a b k).trans ((Nat.mul_le_mul ha hb).trans (by norm_num))
  exact ⟨h, h.trans_lt (by norm_num)⟩

/-- The product of packed integers is the packed convolution. -/
theorem packNat_mul (a : Fin n → ℕ) (b : Fin m → ℕ) (B : ℕ) :
    packNat a B * packNat b B = ∑ k ∈ Finset.range (n + m), natConv a b k * B ^ k := by
  have h : ∀ (i : Fin n) (j : Fin m), a i * B ^ (i : ℕ) * (b j * B ^ (j : ℕ)) =
      ∑ k ∈ Finset.range (n + m), (if (i : ℕ) + (j : ℕ) = k then a i * b j else 0) * B ^ k := by
    intro i j
    have hij : (i : ℕ) + j ∈ Finset.range (n + m) := Finset.mem_range.2 (by omega)
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [hij, ite_true, pow_add]
    ring
  rw [packNat, packNat, Finset.sum_mul_sum]
  simp only [h, natConv, Finset.sum_mul]
  calc _ = ∑ x : Fin n, ∑ k ∈ Finset.range (n + m), ∑ y : Fin m,
        (if (x : ℕ) + (y : ℕ) = k then a x * b y else 0) * B ^ k :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The coefficient-sum identity checked after unpacking. -/
theorem sum_natConv (a : Fin n → ℕ) (b : Fin m → ℕ) :
    ∑ k ∈ Finset.range (n + m), natConv a b k = (∑ i, a i) * ∑ j, b j := by
  have h := packNat_mul a b 1
  simp only [packNat, one_pow, mul_one] at h
  exact h.symm

private theorem sum_digits_lt {B : ℕ} {c : ℕ → ℕ} {t : ℕ} (hc : ∀ k < t, c k < B) :
    ∑ k ∈ Finset.range t, c k * B ^ k < B ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih fun k hk => hc k (by omega)
    have h2 : c t + 1 ≤ B := hc t (by omega)
    calc ∑ k ∈ Finset.range t, c k * B ^ k + c t * B ^ t < B ^ t + c t * B ^ t := by omega
      _ = (c t + 1) * B ^ t := by ring
      _ ≤ B * B ^ t := Nat.mul_le_mul_right _ h2
      _ = B ^ t * B := by ring

/-- Base-`B` digits of `∑ k < N, c k B^k` are the `c k` when every `c k < B`. -/
theorem digit_sum_pow {B N : ℕ} {c : ℕ → ℕ} (hc : ∀ k < N, c k < B) (t : ℕ) :
    (∑ k ∈ Finset.range N, c k * B ^ k) / B ^ t % B = if t < N then c t else 0 := by
  have hB : 0 < B ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inr h
    · exact Or.inl (lt_of_le_of_lt (Nat.zero_le _) (hc 0 h))
  rcases hB with hB | hN
  swap
  · subst hN
    simp
  split_ifs with ht
  · obtain ⟨d, rfl⟩ : ∃ d, N = t + (d + 1) := ⟨N - t - 1, by omega⟩
    rw [Finset.sum_range_add, Finset.sum_range_succ']
    have hlow := sum_digits_lt (B := B) (c := c) (t := t) fun k hk => hc k (by omega)
    have hsplit : ∑ k ∈ Finset.range d, c (t + (k + 1)) * B ^ (t + (k + 1)) +
        c (t + 0) * B ^ (t + 0) =
        B ^ t * (c t + B * ∑ k ∈ Finset.range d, c (t + (k + 1)) * B ^ k) := by
      have h1 : ∀ k, c (t + (k + 1)) * B ^ (t + (k + 1)) =
          B ^ t * (B * (c (t + (k + 1)) * B ^ k)) := fun k => by
        rw [pow_add, pow_succ]
        ring
      simp only [h1, ← Finset.mul_sum, add_zero]
      ring
    rw [hsplit, Nat.add_mul_div_left _ _ (pow_pos hB t), Nat.div_eq_of_lt hlow, zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc t (by omega))]
  · have hlt := sum_digits_lt (B := B) (c := c) (t := N) hc
    have hle : B ^ N ≤ B ^ t := Nat.pow_le_pow_right hB (not_lt.1 ht)
    rw [Nat.div_eq_of_lt (hlt.trans_le hle), Nat.zero_mod]

/-- No-carry unpacking: if every convolution coefficient is below the base `B`, the base-`B`
digits of the product of the packed integers are exactly the convolution coefficients. -/
theorem packNat_mul_digit (a : Fin n → ℕ) (b : Fin m → ℕ) {B : ℕ}
    (hB : ∀ k, natConv a b k < B) (t : ℕ) :
    packNat a B * packNat b B / B ^ t % B = natConv a b t := by
  rw [packNat_mul, digit_sum_pow fun k _ => hB k]
  split_ifs with ht
  · rfl
  · symm
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have : (i : ℕ) + (j : ℕ) ≠ t := by omega
    simp [this]

/-- Packing in base `2^128` is exact for arrays of total mass at most `2^56`. -/
theorem pack128_digit (a : Fin n → ℕ) (b : Fin m → ℕ) (ha : ∑ i, a i ≤ 2 ^ 56)
    (hb : ∑ j, b j ≤ 2 ^ 56) (t : ℕ) :
    packNat a (2 ^ 128) * packNat b (2 ^ 128) / (2 ^ 128) ^ t % 2 ^ 128 = natConv a b t :=
  packNat_mul_digit a b (fun k => (natConv_le_pow_56 a b ha hb k).2) t

/-- Packing in base `2^192` is exact for arrays of total mass at most `2^72`. -/
theorem pack192_digit (a : Fin n → ℕ) (b : Fin m → ℕ) (ha : ∑ i, a i ≤ 2 ^ 72)
    (hb : ∑ j, b j ≤ 2 ^ 72) (t : ℕ) :
    packNat a (2 ^ 192) * packNat b (2 ^ 192) / (2 ^ 192) ^ t % 2 ^ 192 = natConv a b t :=
  packNat_mul_digit a b (fun k => (natConv_le_pow_72 a b ha hb k).2) t

/-- Dividing an exact coefficient downward by `2^s` keeps the real value below the exact
product: `⌊c / 2^s⌋ / 2^s ≤ c / 2^(2s)`. -/
theorem floor_shift_le (c s : ℕ) :
    ((c / 2 ^ s : ℕ) : ℝ) / 2 ^ s ≤ (c : ℝ) / (2 ^ s * 2 ^ s) := by
  rw [← div_div]
  have h : ((c / 2 ^ s : ℕ) : ℝ) ≤ (c : ℝ) / 2 ^ s := by
    have := Nat.cast_div_le (α := ℝ) (m := c) (n := 2 ^ s)
    simpa using this
  exact div_le_div_of_nonneg_right h (by positivity)

end Packing

/-! ## Decimal ratios -/

section Decimals

/-- The ratio checks quoted in the introduction and in `sec:evaluation` (subsections on the
matched Poisson comparison and on how much of the bracket closes), and the endpoint
certificates `eq:numeric-cert` and those of the product-pair lower bound, compared with
`δ = 10^-8`. -/
theorem decimal_claims :
    (6.423 : ℝ) / 0.507 > 12.6 ∧ (0.338 : ℝ) / 0.182 > 1.85 ∧
    (5.64 : ℝ) / 5.106 < 1.105 ∧ (6.49 : ℝ) / 5.538 < 1.172 ∧
    (7.97 : ℝ) / 6.423 < 1.241 ∧ (0.71 : ℝ) / 0.338 < 2.101 ∧
    ((9.21 : ℝ) - 7.97) / (9.21 - 6.423) > 0.444 ∧
    ((0.83 : ℝ) - 0.71) / (0.83 - 0.338) > 0.243 ∧
    (9856064 : ℝ) / 10 ^ 15 < 10 ^ (-8 : ℤ) ∧ (3805278 : ℝ) / 10 ^ 15 < 10 ^ (-8 : ℤ) ∧
    (8525892 : ℝ) / 10 ^ 15 < 10 ^ (-8 : ℤ) ∧ (5244378 : ℝ) / 10 ^ 15 < 10 ^ (-8 : ℤ) ∧
    (10011846 : ℝ) / 10 ^ 15 > 10 ^ (-8 : ℤ) ∧ (10201901 : ℝ) / 10 ^ 15 > 10 ^ (-8 : ℤ) := by
  norm_num

end Decimals

end ASGA
