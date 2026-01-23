import Mathlib

/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-!
# Appendix I — Quadratic dissipator selection (α = 2)

Lean 4 / Mathlib formalization of Appendix I of the QFTT-WESH paper.

## Modular dependencies (conceptual, not imported)
- **Appendix G**: establishes WESH-Noether constraint on local channels
- **Section 1**: derives collective stability criterion τ_coh ∝ N² from bootstrap closure

## Selection argument formalized here
1. CPT symmetry ⇒ F is even (odd coefficients vanish)
2. No constant term + nontriviality ⇒ leading exponent ≥ 2
3. CPT-even ⇒ leading exponent = 2n for some n ≥ 1
4. Collective stability (Section 1) selects n = 1, hence leading exponent = 2

Main result: under these hypotheses, the local normal form is quadratic.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace QFTT.WESH.AppendixI

/-- CPT-evenness: all odd coefficients vanish. -/
def CPTEven (F : PowerSeries ℝ) : Prop :=
  ∀ k : ℕ, PowerSeries.coeff (2 * k + 1) F = 0

/-- A local channel profile with the hypotheses from Appendix I. -/
structure LocalChannel where
  F : PowerSeries ℝ
  noConst : PowerSeries.coeff 0 F = 0
  cpt_even : CPTEven F
  nontrivial : ∃ n : ℕ, PowerSeries.coeff n F ≠ 0

/-- The scaling exponent is the least index with nonzero coefficient. -/
def scalingExponent (C : LocalChannel) : ℕ :=
  Nat.find C.nontrivial

/-- The coefficient at scalingExponent is nonzero. -/
lemma coeff_scalingExponent_ne_zero (C : LocalChannel) :
    PowerSeries.coeff (scalingExponent C) C.F ≠ 0 :=
  Nat.find_spec C.nontrivial

/-- Coefficients below the leading exponent are zero. -/
lemma coeff_eq_zero_of_lt_scalingExponent (C : LocalChannel)
    {m : ℕ} (hm : m < scalingExponent C) :
    PowerSeries.coeff m C.F = 0 := by
  by_contra h
  exact Nat.find_min C.nontrivial hm h

/-- CPT-evenness implies coeff 1 = 0. -/
lemma coeff_one_eq_zero (C : LocalChannel) : PowerSeries.coeff 1 C.F = 0 := by
  have h := C.cpt_even 0
  simp at h
  exact h

/-- The leading index cannot be 0. -/
lemma scalingExponent_ne_zero (C : LocalChannel) : scalingExponent C ≠ 0 := by
  intro h0
  have hspec := coeff_scalingExponent_ne_zero C
  rw [h0] at hspec
  exact hspec C.noConst

/-- The leading index cannot be 1. -/
lemma scalingExponent_ne_one (C : LocalChannel) : scalingExponent C ≠ 1 := by
  intro h1
  have hspec := coeff_scalingExponent_ne_zero C
  rw [h1] at hspec
  exact hspec (coeff_one_eq_zero C)

/-- The leading index is at least 2. -/
lemma two_le_scalingExponent (C : LocalChannel) : 2 ≤ scalingExponent C := by
  have h0 := scalingExponent_ne_zero C
  have h1 := scalingExponent_ne_one C
  omega

/-- CPT-evenness forces the leading exponent to be even. -/
lemma even_scalingExponent (C : LocalChannel) : Even (scalingExponent C) := by
  by_contra hEven
  rw [Nat.not_even_iff_odd] at hEven
  obtain ⟨k, hk⟩ := hEven
  have hspec := coeff_scalingExponent_ne_zero C
  rw [hk] at hspec
  exact hspec (C.cpt_even k)

/-- The "2n statement" from the paper: leading exponent = 2n with n ≥ 1.
    This is the form before collective stability selects n = 1. -/
theorem cpt_even_forces_2n_form (C : LocalChannel) :
    ∃ n : ℕ, scalingExponent C = 2 * n ∧ 1 ≤ n := by
  obtain ⟨k, hk⟩ := even_scalingExponent C
  have hne0 := scalingExponent_ne_zero C
  have k_ne0 : k ≠ 0 := by
    intro hk0
    apply hne0
    simp [hk, hk0]
  refine ⟨k, ?_, Nat.one_le_iff_ne_zero.mpr k_ne0⟩
  omega

/-- The local normal form: the leading monomial of the dissipator. -/
noncomputable def LocalNormalForm (C : LocalChannel) : Polynomial ℝ :=
  Polynomial.monomial (scalingExponent C) (PowerSeries.coeff (scalingExponent C) C.F)

/-- Collective stability (Section 1): the scaling exponent equals 2. -/
def CollectiveStability (C : LocalChannel) : Prop :=
  scalingExponent C = 2

/-- Quadratic normal form: the quadratic coefficient is nonzero. -/
def QuadraticNormalForm (C : LocalChannel) : Prop :=
  ∃ a2 : ℝ, a2 ≠ 0 ∧ PowerSeries.coeff 2 C.F = a2

/-- **Proposition I.1 (Quadratic local normal form).**

Under collective stability, the local normal form is the quadratic monomial a₂z². -/
theorem Proposition_I_quadratic_selection
    (C : LocalChannel) (hStab : CollectiveStability C) :
    QuadraticNormalForm C := by
  have hspec := coeff_scalingExponent_ne_zero C
  rw [hStab] at hspec
  exact ⟨PowerSeries.coeff 2 C.F, hspec, rfl⟩

/-- Explicit form: LocalNormalForm = monomial 2 a₂ with a₂ ≠ 0. -/
theorem LocalNormalForm_eq_quadratic
    (C : LocalChannel) (hStab : CollectiveStability C) :
    ∃ a : ℝ, a ≠ 0 ∧ LocalNormalForm C = Polynomial.monomial 2 a := by
  have hspec := coeff_scalingExponent_ne_zero C
  rw [hStab] at hspec
  refine ⟨PowerSeries.coeff 2 C.F, hspec, ?_⟩
  unfold LocalNormalForm CollectiveStability at *
  rw [hStab]

end QFTT.WESH.AppendixI
