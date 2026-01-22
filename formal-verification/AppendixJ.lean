import Mathlib

/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-!
# Appendix J — Eigentime shot-noise and cosmological constant selection

Lean 4 / Mathlib formalization of Appendix J of the QFTT-WESH paper.

## Contents
1. Regional count scaling: E[N(R)] = V₄(R)/V_ξ
2. CLT scaling: Var[N] = α_N · E[N], hence δN ~ √N
3. Hubble-scale payoff: if V₄ = H⁻⁴ then 1/√V₄ = H²
4. λ-constant selection from unit-cell normalization

## References (background)
- Doob (1953), *Stochastic Processes*
- Daley–Vere-Jones (2003), *An Introduction to the Theory of Point Processes*
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real ENNReal

namespace QFTT.WESH.AppendixJ

/-! ## 1. Setup and definitions -/

variable {M : Type*} [MeasurableSpace M] [MeasureSpace M]
variable {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω]
variable (V_xi : ℝ≥0∞)

noncomputable section

/-- 4-volume of a region. -/
def V4 (R : Set M) : ℝ≥0∞ := volume R

/-- Expected count in region `R`. -/
def ExpectedCount (N : Set M → Ω → ℝ) (R : Set M) : ℝ := ∫ ω, N R ω

/-- Intensity law: `E[N(R)] = ∫_R λ(x) dV4`. -/
def IsIntensity (N : Set M → Ω → ℝ) (lambda : M → ℝ) : Prop :=
  ∀ R : Set M, MeasurableSet R →
    ExpectedCount N R = ∫ x in R, lambda x ∂volume

/-- λ is constant with value `c`. -/
def IsConstant (lambda : M → ℝ) (c : ℝ) : Prop :=
  ∀ x : M, lambda x = c

/-- IR selection target: `λ(x) = 1 / V_ξ`. -/
def IsConstantLambda (lambda : M → ℝ) (V_xi : ℝ≥0∞) : Prop :=
  ∀ x : M, lambda x = 1 / V_xi.toReal

/-- CLT scaling: `Var[N(R)] = α_N · E[N(R)]`. -/
def HasCLTScaling (N : Set M → Ω → ℝ) (alpha_N : ℝ) : Prop :=
  ∀ R : Set M, MeasurableSet R →
    variance (N R) (@volume Ω _) = alpha_N * ExpectedCount N R


/-! ## 2. Helper lemmas -/

/-- Nonnegativity of `ExpectedCount` from pointwise nonnegativity. -/
lemma ExpectedCount_nonneg
    (N : Set M → Ω → ℝ) (hN_nonneg : ∀ R ω, 0 ≤ N R ω) (R : Set M) :
    0 ≤ ExpectedCount N R :=
  integral_nonneg (hN_nonneg R)

/-- Integral of a constant over a measurable set. -/
lemma integral_const_on_region
    (R : Set M) (c : ℝ) :
    (∫ _x in R, c ∂volume) = (volume R).toReal * c := by
  simp only [integral_const, smul_eq_mul]
  congr 1
  simp only [Measure.real, Measure.restrict_apply_univ]


/-! ## 3. J.1 — Regional count scaling -/

/-- **J.1 (Regional count scaling).** If intensity is constant `λ = 1/V_ξ`,
    then `E[N(R)] = V₄(R)/V_ξ`. -/
theorem J1_RegionalCount_Scaling
    (N : Set M → Ω → ℝ) (lambda : M → ℝ)
    (h_intensity : IsIntensity N lambda)
    (h_const : IsConstantLambda lambda V_xi)
    (R : Set M) (hR : MeasurableSet R) :
    ExpectedCount N R = (V4 R).toReal / V_xi.toReal := by
  have hEN : ExpectedCount N R = ∫ x in R, lambda x ∂volume := h_intensity R hR
  have hlambda : ∀ x, lambda x = 1 / V_xi.toReal := h_const
  have hIntEq : (∫ x in R, lambda x ∂volume) = ∫ x in R, (1 / V_xi.toReal) ∂volume := by
    congr 1; ext x; exact hlambda x
  calc ExpectedCount N R
      = ∫ x in R, lambda x ∂volume := hEN
    _ = ∫ x in R, (1 / V_xi.toReal) ∂volume := hIntEq
    _ = (volume R).toReal * (1 / V_xi.toReal) := integral_const_on_region R _
    _ = (V4 R).toReal / V_xi.toReal := by simp only [V4]; ring


/-! ## 4. J.2 — CLT scaling -/

/-- **J.2 (CLT square-root scaling).** If `Var[N(R)] = α_N · E[N(R)]`,
    then `√Var = √α_N · √E[N]`. -/
theorem J2_CLT_Scaling
    (N : Set M → Ω → ℝ) (alpha_N : ℝ)
    (h_scaling : HasCLTScaling N alpha_N)
    (hN_nonneg : ∀ R ω, 0 ≤ N R ω)
    (R : Set M) (hR : MeasurableSet R)
    (h_alpha_nonneg : 0 ≤ alpha_N) :
    Real.sqrt (variance (N R) (@volume Ω _)) =
      Real.sqrt alpha_N * Real.sqrt (ExpectedCount N R) := by
  have hvar : variance (N R) (@volume Ω _) = alpha_N * ExpectedCount N R := h_scaling R hR
  have hEN_nonneg : 0 ≤ ExpectedCount N R := ExpectedCount_nonneg N hN_nonneg R
  rw [hvar]
  exact Real.sqrt_mul h_alpha_nonneg _


/-! ## 5. J.3–J.4 — Shot-noise propagation to Λ -/

/-- Effective cosmological constant in region `R` (dimensionless scaling form). -/
def Lambda_eff (S_Lambda : Set M → Ω → ℝ) (G : ℝ) (R : Set M) (ω : Ω) : ℝ :=
  - (8 * Real.pi * G / (V4 R).toReal) * S_Lambda R ω

/-- Variance scales quadratically under scalar multiplication.
    This is a standard Mathlib lemma (`ProbabilityTheory.variance_const_mul`). -/
lemma variance_const_mul (X : Ω → ℝ) (c : ℝ) :
    variance (fun ω => c * X ω) (@volume Ω _) = 
    c ^ 2 * variance X (@volume Ω _) :=
  ProbabilityTheory.variance_const_mul c X (@volume Ω _)

/-- **J.3 (Shot-noise variance).** If `S_Λ = N`, then `Var[S_Λ]` follows CLT scaling. -/
theorem J3_ShotNoise_Var
    (N : Set M → Ω → ℝ) (S_Lambda : Set M → Ω → ℝ) (alpha_N : ℝ)
    (h_scaling : HasCLTScaling N alpha_N)
    (R : Set M) (hR : MeasurableSet R)
    (h_SN : S_Lambda R = N R) :
    variance (S_Lambda R) (@volume Ω _) = alpha_N * ExpectedCount N R := by
  have hvar := h_scaling R hR
  simp only [h_SN, hvar]

/-- **J.4 (Λ variance scaling).** Under CLT scaling for shot-noise,
    `Var[Λ_eff] = (8πG/V₄)² · α_N · E[N(R)]`.
    This gives `δΛ ~ 1/√V₄` when combined with J.1. -/
theorem J4_VarLambdaEff_Scaling
    (N : Set M → Ω → ℝ) (S_Lambda : Set M → Ω → ℝ) (G : ℝ) (alpha_N : ℝ)
    (h_scaling : HasCLTScaling N alpha_N)
    (R : Set M) (hR : MeasurableSet R)
    (h_SN : S_Lambda R = N R) :
    variance (Lambda_eff S_Lambda G R) (@volume Ω _) =
      ((8 * Real.pi * G) / (V4 R).toReal)^2 * alpha_N * ExpectedCount N R := by
  -- Λ_eff is a scalar multiple of S_Lambda
  let c := -(8 * Real.pi * G / (V4 R).toReal)
  have hLambda : Lambda_eff S_Lambda G R = fun ω => c * S_Lambda R ω := rfl
  -- Apply variance scaling
  have hvar1 : variance (Lambda_eff S_Lambda G R) (@volume Ω _) = 
      c ^ 2 * variance (S_Lambda R) (@volume Ω _) := by
    simp only [hLambda]
    exact variance_const_mul (S_Lambda R) c
  -- Use J3
  have hvarSN : variance (S_Lambda R) (@volume Ω _) = alpha_N * ExpectedCount N R :=
    J3_ShotNoise_Var N S_Lambda alpha_N h_scaling R hR h_SN
  -- Combine and simplify
  calc variance (Lambda_eff S_Lambda G R) (@volume Ω _)
      = c ^ 2 * variance (S_Lambda R) (@volume Ω _) := hvar1
    _ = c ^ 2 * (alpha_N * ExpectedCount N R) := by rw [hvarSN]
    _ = ((8 * Real.pi * G) / (V4 R).toReal)^2 * alpha_N * ExpectedCount N R := by
        simp only [c]; ring


/-! ## 6. J.4b — Hubble-scale numerical payoff -/

/-- **J.4b (Hubble payoff).** If `V₄ = H⁻⁴` (Hubble-scale coarse-graining),
    then `1/√V₄ = H²`. This connects the general `δΛ ~ 1/√V₄` scaling
    to the cosmologically relevant `δΛ ~ H²` form.

    Pure algebra: no physics assumptions. -/
theorem J4b_Hubble_Payoff (H : ℝ) (hH : 0 < H) (V4_val : ℝ)
    (hV4 : V4_val = H ^ (-4 : ℤ)) :
    1 / Real.sqrt V4_val = H ^ (2 : ℕ) := by
  have hHnn : 0 ≤ H := hH.le
  rw [hV4, zpow_neg]
  rw [Real.sqrt_inv (H ^ (4 : ℤ))]
  simp only [one_div, inv_inv]
  have h4 : (4 : ℤ) = (4 : ℕ) := rfl
  simp only [h4, zpow_natCast]
  conv_lhs => rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact Real.sqrt_sq (pow_nonneg hHnn 2)


/-! ## 7. λ-constant selection from unit-cell normalization -/

/-- **λ selection principle.** If λ is constant and a reference cell R₀
    has `E[N(R₀)] = 1`, then `λ = 1/V₄(R₀)`.

    This is the clean closure: λ is fixed by a normalization condition,
    not inserted by hand. -/
theorem lambda_value_from_unit_cell
    (N : Set M → Ω → ℝ) (lambda : M → ℝ) (c : ℝ)
    (h_intensity : IsIntensity N lambda)
    (h_const : IsConstant lambda c)
    (R0 : Set M) (hR0 : MeasurableSet R0)
    (hV0_ne0 : (V4 R0).toReal ≠ 0)
    (hEN1 : ExpectedCount N R0 = 1) :
    c = 1 / (V4 R0).toReal := by
  have hEN : ExpectedCount N R0 = ∫ x in R0, lambda x ∂volume := h_intensity R0 hR0
  have hIntEq : (∫ x in R0, lambda x ∂volume) = ∫ x in R0, c ∂volume := by
    congr 1; ext x; exact h_const x
  have hEN' : ExpectedCount N R0 = ∫ x in R0, c ∂volume := hEN.trans hIntEq
  have hInt : (∫ _x in R0, c ∂volume) = (volume R0).toReal * c := integral_const_on_region R0 c
  have hc_mul : c * (V4 R0).toReal = 1 := by
    have h1 : (volume R0).toReal * c = 1 := by
      calc (volume R0).toReal * c
          = ∫ _x in R0, c ∂volume := hInt.symm
        _ = ExpectedCount N R0 := hEN'.symm
        _ = 1 := hEN1
    simp only [V4, mul_comm] at h1 ⊢
    exact h1
  exact (eq_div_iff hV0_ne0).mpr hc_mul

/-- **Corollary.** If the reference cell has volume `V_ξ`, then `λ = 1/V_ξ`. -/
theorem IsConstantLambda_of_unit_cell
    (N : Set M → Ω → ℝ) (lambda : M → ℝ) (c : ℝ)
    (h_intensity : IsIntensity N lambda)
    (h_const : IsConstant lambda c)
    (R0 : Set M) (hR0 : MeasurableSet R0)
    (hV0_ne0 : (V4 R0).toReal ≠ 0)
    (hV0 : V4 R0 = V_xi)
    (hEN1 : ExpectedCount N R0 = 1) :
    IsConstantLambda lambda V_xi := by
  have hc : c = 1 / (V4 R0).toReal :=
    lambda_value_from_unit_cell N lambda c h_intensity h_const R0 hR0 hV0_ne0 hEN1
  intro x
  calc lambda x = c := h_const x
    _ = 1 / (V4 R0).toReal := hc
    _ = 1 / V_xi.toReal := by rw [hV0]

end

end QFTT.WESH.AppendixJ
