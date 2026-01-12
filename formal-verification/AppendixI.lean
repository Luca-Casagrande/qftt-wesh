/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

Formalization of Appendix I: Consistency selection of the quadratic dissipator.

This module defines the necessary concepts and the main proposition from Appendix I.
It includes:
- `LocalChannel`: A predicate for local channel functionals represented as power series.
- `CPTEven`: A constraint ensuring the functional contains only even powers.
- `CollectiveStability`: A constraint fixing the scaling exponent to 2.
- `LocalNormalForm`: The leading monomial of the functional.
- `quadratic_local_normal_form`: The main theorem stating that under the given constraints,
  the local normal form is uniquely quadratic.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open PowerSeries

variable {R : Type*} [Field R]

/-- A local channel functional F represented as a power series.
    It must be non-zero and vanish at 0 (no constant term). -/
def LocalChannel (F : PowerSeries R) : Prop :=
  F ≠ 0 ∧ coeff 0 F = 0

/-- CPT-evenness constraint: F contains only even powers. -/
def CPTEven (F : PowerSeries R) : Prop :=
  ∀ n, Odd n → coeff n F = 0

/-- The scaling exponent associated with a channel F.
    Based on the text: F(T) ~ T^(2n) => tau ~ N^(2n).
    So the exponent is the order of F.
    We use pattern matching to extract the value, defaulting to 0 if F=0 (order is top). -/
noncomputable def scalingExponent (F : PowerSeries R) : ℕ :=
  match order F with
  | ⊤ => 0
  | (n : ℕ) => n

/-- Collective stability constraint: The scaling exponent must be 2. -/
def CollectiveStability (F : PowerSeries R) : Prop :=
  scalingExponent F = 2

/-- The local normal form is the leading monomial. -/
noncomputable def LocalNormalForm (F : PowerSeries R) : Polynomial R :=
  Polynomial.monomial (scalingExponent F) (coeff (scalingExponent F) F)

/-- Proposition I.1: Quadratic local normal form.
    Under (i)–(iii), the admissible local normal form is uniquely quadratic. -/
theorem quadratic_local_normal_form (F : PowerSeries R)
    (h_local : LocalChannel F)
    (h_cpt : CPTEven F)
    (h_stab : CollectiveStability F) :
    ∃ a ≠ 0, LocalNormalForm F = Polynomial.monomial 2 a := by
  simp +zetaDelta at *
  unfold LocalNormalForm CollectiveStability at *
  refine ⟨PowerSeries.coeff 2 F, ?_, ?_⟩
  · -- Show coeff 2 F ≠ 0
    contrapose! h_stab
    -- If coeff 2 F = 0, then order F > 2, so scalingExponent ≠ 2
    have h_order_gt_2 : PowerSeries.order F > 2 := by
      have h_coeff_zero : ∀ n, n < 3 → coeff n F = 0 := by
        intro n hn
        interval_cases n <;> simp_all +decide [LocalChannel]
        exact h_cpt 1 (by decide)
      simp_all +decide [PowerSeries.order]
      split_ifs <;> simp_all +decide
      exact fun m hm => h_coeff_zero m (Nat.lt_succ_of_le hm)
    unfold scalingExponent
    cases h : PowerSeries.order F <;> aesop
  · -- Show LocalNormalForm F = monomial 2 (coeff 2 F)
    rw [h_stab]

end
