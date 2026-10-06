import ASGA.Gaussian
import ASGA.Certificate

/-!
# The candidate-count functions and the certificate recursion

`Gaussian.callF` and `Gaussian.putJ` are the expectations `F_m` and `J_m` of `eq:recurrences`
for the lognormal likelihood ratio of `lem:clone`. They coincide with the recursions `callLaw`
and `putLaw` of `Certificate.lean` for the law `Gaussian.lrLaw σ`. The soundness theorems
`certificate_call_sound` and `certificate_put_sound` therefore bound the same functions that
enter Proposition `prop:counts`.
-/

open MeasureTheory ProbabilityTheory

namespace ASGA

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {σ : ℝ}
  {X : ℕ → Ω → ℝ}

theorem callF_eq_callLaw (hX : Gaussian.IsLRSequence P σ X) (hσ : σ ≠ 0) (m : ℕ) :
    Gaussian.callF P X m = callLaw (Gaussian.lrLaw σ) m := by
  induction m with
  | zero => funext t; simp [Gaussian.callF_zero, callLaw]
  | succ m ih => funext t; rw [Gaussian.callF_succ hX hσ, ih, callLaw]

theorem putJ_eq_putLaw (hX : Gaussian.IsLRSequence P σ X) (hσ : σ ≠ 0) (m : ℕ) :
    Gaussian.putJ P X m = putLaw (Gaussian.lrLaw σ) m := by
  induction m with
  | zero => funext t; simp [Gaussian.putJ_zero, putLaw]
  | succ m ih => funext t; rw [Gaussian.putJ_succ hX hσ, ih, putLaw]

end ASGA
