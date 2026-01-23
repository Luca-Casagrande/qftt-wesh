import Mathlib

/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-!
# Section 6 (Part II) — Spectral structure, concentration bounds, and chronogenesis

Lean 4 / Mathlib formalization of Section 6 (Part II) of the QFTT-WESH paper.

Contents:
- Spectral definitions (s_boson, W_HH, s_bar)
- Kerr extension (corotating frame)
- IR concentration bound (Proposition 6.1)
- EFT kernel stability scaling
- Subleading corrections (replica method)
- Chronogenesis holographic bound
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open scoped BigOperators

noncomputable section

namespace QFTT.WESH.Section6.Part2

/-! ## Spectral definitions -/

/-- Entropy function for a bosonic mode with energy x (in units of temperature). -/
def s_boson (x : ℝ) : ℝ :=
  if 0 < x then x / (Real.exp x - 1) - Real.log (1 - Real.exp (-x)) else 0

/-- The Hartle-Hawking weight function. -/
def W_HH (p : ℝ) (F : ℝ → ℝ) (xi beta_H : ℝ) (omega : ℝ) : ℝ :=
  omega^(2 + p) * F (omega * xi) * (Real.exp (-beta_H * omega) / (1 - Real.exp (-beta_H * omega)))

/-- The spectral average s_bar (discrete/block approximation). -/
def s_bar_block {ι : Type*} [Fintype ι] (W : ι → ℝ) (x : ι → ℝ) (beta_H : ℝ) : ℝ :=
  (∑ i, W i * s_boson (beta_H * x i)) / (∑ i, W i)

/-! ## Kerr extension (corotating frame) -/

/-- Corotating frequency for Kerr: ω̃ = ω - m·Ω_H. -/
def omega_tilde (omega m Omega_H : ℝ) : ℝ := omega - m * Omega_H

/-- Kerr KMS Bose factor in corotating frame. -/
def bose_kerr (beta_H omega m Omega_H : ℝ) : ℝ :=
  let w := omega_tilde omega m Omega_H
  Real.exp (-beta_H * w) / (1 - Real.exp (-beta_H * w))

/-- The corotating sector condition: ω̃ > 0 (excludes superradiant modes). -/
def CorotatingSector (omega m Omega_H : ℝ) : Prop := 0 < omega_tilde omega m Omega_H

/-! ## EFT kernel stability scaling -/

/-- Locality/moment control package for a short-range kernel. -/
structure KernelMoment (ξ L : ℝ) where
  ξ_nonneg : 0 ≤ ξ
  L_pos : 0 < L
  moment2 : ℝ
  moment2_bound : moment2 ≤ ξ / L
  locality_error : ℝ
  locality_error_bound : locality_error ≤ ξ / L

theorem eft_kernel_stability_scaling {ξ L : ℝ} (hμ : KernelMoment ξ L) :
    hμ.moment2 + hμ.locality_error ≤ 2 * (ξ / L) := by
  have hm : hμ.moment2 ≤ ξ / L := hμ.moment2_bound
  have he : hμ.locality_error ≤ ξ / L := hμ.locality_error_bound
  nlinarith

/-! ## IR concentration bound (Proposition 6.1) -/

section IRConcentration

variable {ι : Type*} [Fintype ι]

def wSum (W : ι → ℝ) : ℝ := ∑ i, W i

def weightedAvg (W : ι → ℝ) (f : ℝ → ℝ) (x : ι → ℝ) : ℝ := ∑ i, W i * f (x i)

def wVar (W : ι → ℝ) (xstar : ℝ) (x : ι → ℝ) : ℝ := ∑ i, W i * (x i - xstar) ^ 2

structure WeightData (W : ι → ℝ) : Prop where
  w_nonneg : ∀ i, 0 ≤ W i
  sum_w : wSum (ι := ι) W = 1

structure TaylorBound (f : ℝ → ℝ) (xstar M1 M2 : ℝ) : Prop where
  M1_nonneg : 0 ≤ M1
  M2_nonneg : 0 ≤ M2
  bound : ∀ s, |f s - f xstar| ≤ M1 * |s - xstar| + (M2 / 2) * (s - xstar) ^ 2

/-- Weighted Cauchy-Schwarz: for normalized weights, ∑W|d| ≤ √(∑Wd²). -/
theorem weighted_mean_abs_le_sqrt_var
    (W : ι → ℝ) (xstar : ℝ) (x : ι → ℝ) (hW : WeightData (ι := ι) W) :
    (∑ i, W i * |x i - xstar|) ≤ Real.sqrt (wVar (ι := ι) W xstar x) := by
  set d : ι → ℝ := fun i => |x i - xstar|
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (W i)) (fun i => Real.sqrt (W i) * d i)
  have ha : ∀ i, Real.sqrt (W i) ^ 2 = W i := fun i => Real.sq_sqrt (hW.w_nonneg i)
  have hb : ∀ i, (Real.sqrt (W i) * d i) ^ 2 = W i * d i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hW.w_nonneg i)]
  have hab : ∀ i, Real.sqrt (W i) * (Real.sqrt (W i) * d i) = W i * d i := fun i => by
    rw [← mul_assoc, ← sq, ha i]
  simp_rw [ha, hb, hab] at hCS
  have hsum_eq : (∑ i : ι, W i) = 1 := by simpa [wSum] using hW.sum_w
  rw [hsum_eq, one_mul] at hCS
  have hd2 : ∀ i, d i ^ 2 = (x i - xstar) ^ 2 := fun i => sq_abs _
  simp_rw [hd2] at hCS
  have hvar : (∑ i : ι, W i * (x i - xstar) ^ 2) = wVar (ι := ι) W xstar x := rfl
  rw [hvar] at hCS
  have hnn : 0 ≤ ∑ i : ι, W i * d i := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hW.w_nonneg i) (abs_nonneg _)
  have hvar_nn : 0 ≤ wVar (ι := ι) W xstar x := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hW.w_nonneg i) (sq_nonneg _)
  rw [Real.le_sqrt hnn hvar_nn]
  exact hCS

/-- Proposition 6.1: Concentration of weighted averages. -/
theorem Proposition_6_1_concentration
    (W : ι → ℝ) (x : ι → ℝ) (f : ℝ → ℝ) (xstar M1 M2 : ℝ)
    (hW : WeightData (ι := ι) W) (hT : TaylorBound f xstar M1 M2) :
    |weightedAvg (ι := ι) W f x - f xstar|
      ≤ M1 * Real.sqrt (wVar (ι := ι) W xstar x) + (M2 / 2) * (wVar (ι := ι) W xstar x) := by
  classical
  set V : ℝ := wVar (ι := ι) W xstar x
  have hsum : (∑ i, W i) = 1 := by simpa [wSum] using hW.sum_w
  have hdiff : weightedAvg (ι := ι) W f x - f xstar = ∑ i, W i * (f (x i) - f xstar) := by
    calc weightedAvg (ι := ι) W f x - f xstar
        = (∑ i, W i * f (x i)) - (1 : ℝ) * f xstar := by simp [weightedAvg]
      _ = (∑ i, W i * f (x i)) - (∑ i, W i) * f xstar := by simp [hsum]
      _ = (∑ i, W i * f (x i)) - (∑ i, W i * f xstar) := by simp [Finset.sum_mul]
      _ = ∑ i, (W i * f (x i) - W i * f xstar) := by simp [Finset.sum_sub_distrib]
      _ = ∑ i, W i * (f (x i) - f xstar) := by
          refine Finset.sum_congr rfl ?_; intro i _hi; ring
  have hterm : ∀ i, |W i * (f (x i) - f xstar)|
      ≤ W i * (M1 * |x i - xstar| + (M2 / 2) * (x i - xstar) ^ 2) := by
    intro i
    have hWi : 0 ≤ W i := hW.w_nonneg i
    have hTaylor := hT.bound (x i)
    have hTaylor_mul : W i * |f (x i) - f xstar|
        ≤ W i * (M1 * |x i - xstar| + (M2 / 2) * (x i - xstar) ^ 2) :=
      mul_le_mul_of_nonneg_left hTaylor hWi
    have habs : |W i * (f (x i) - f xstar)| = W i * |f (x i) - f xstar| := by
      simp [abs_mul, abs_of_nonneg hWi]
    simpa [habs] using hTaylor_mul
  have hsum_bound : |∑ i, W i * (f (x i) - f xstar)|
      ≤ M1 * (∑ i, W i * |x i - xstar|) + (M2 / 2) * V := by
    have htriangle : |∑ i, W i * (f (x i) - f xstar)| ≤ ∑ i, |W i * (f (x i) - f xstar)| :=
      Finset.abs_sum_le_sum_abs (f := fun i => W i * (f (x i) - f xstar)) Finset.univ
    calc |∑ i, W i * (f (x i) - f xstar)|
        ≤ ∑ i, |W i * (f (x i) - f xstar)| := htriangle
      _ ≤ ∑ i, W i * (M1 * |x i - xstar| + (M2 / 2) * (x i - xstar) ^ 2) := by
          refine Finset.sum_le_sum ?_; intro i _hi; exact hterm i
      _ = M1 * (∑ i, W i * |x i - xstar|) + (M2 / 2) * (∑ i, W i * (x i - xstar) ^ 2) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_assoc, mul_left_comm, mul_comm]
      _ = M1 * (∑ i, W i * |x i - xstar|) + (M2 / 2) * V := by simp [V, wVar]
  have hCS : (∑ i, W i * |x i - xstar|) ≤ Real.sqrt V := by
    simp only [V]; exact weighted_mean_abs_le_sqrt_var (ι := ι) W xstar x hW
  calc |weightedAvg (ι := ι) W f x - f xstar|
      = |∑ i, W i * (f (x i) - f xstar)| := by simp [hdiff]
    _ ≤ M1 * (∑ i, W i * |x i - xstar|) + (M2 / 2) * V := hsum_bound
    _ ≤ M1 * Real.sqrt V + (M2 / 2) * V := by
        have hM1 := hT.M1_nonneg
        have h1 : M1 * (∑ i, W i * |x i - xstar|) ≤ M1 * Real.sqrt V :=
          mul_le_mul_of_nonneg_left hCS hM1
        linarith
    _ = M1 * Real.sqrt (wVar (ι := ι) W xstar x) + (M2 / 2) * (wVar (ι := ι) W xstar x) := by
        simp only [V]

end IRConcentration

/-! ## Subleading corrections (replica method) -/

/-- Purely conical part of a₂: a₂_cone(α) := a₂(α) - α·a₂(1). -/
def a2_cone (a_2 : ℝ → ℝ) (alpha : ℝ) : ℝ := a_2 alpha - alpha * a_2 1

lemma a2_cone_one (a_2 : ℝ → ℝ) : a2_cone a_2 1 = 0 := by simp [a2_cone]

/-- Logarithmic coefficient γ from replicas: γ = (1/2)·∂_α a₂_cone |_{α=1}. -/
def gamma_replica (a_2 : ℝ → ℝ) : ℝ := (1/2) * (deriv (a2_cone a_2) 1)

theorem thm_Hessian_entropy_gamma_formula
    (a_2 : ℝ → ℝ) (_h_diff : DifferentiableAt ℝ (a2_cone a_2) 1) :
    gamma_replica a_2 = (1/2) * (deriv (a2_cone a_2) 1) := rfl

/-! ## Bekenstein-Hawking entropy -/

/-- S_BH = A/(4L_P²) + γ·ln(A/L_P²) + k₀ -/
def S_BH (A L_P : ℝ) (gamma k_0 : ℝ) : ℝ :=
  A / (4 * L_P^2) + gamma * Real.log (A / L_P^2) + k_0

/-! ## Chronogenesis holographic bound -/

/-- Γ split: Γ = Γ_loc - Γ_cost. -/
structure GammaSplit where
  Γ : ℝ → ℝ
  Γ_loc : ℝ → ℝ
  Γ_cost : ℝ → ℝ
  split : ∀ s, Γ s = Γ_loc s - Γ_cost s

/-- Assumptions for chronogenesis bound. -/
structure ChronogenesisAssumptions (G : GammaSplit) (Entropy S_bound : ℝ → ℝ) : Prop where
  Γ_nonneg : ∀ s, 0 ≤ G.Γ s
  cost_nonneg : ∀ s, 0 ≤ G.Γ_cost s
  entropy_le_cost : ∀ s, Entropy s ≤ G.Γ_cost s
  loc_le_bound : ∀ s, G.Γ_loc s ≤ S_bound s

/-- Holographic bound from chronogenesis: Entropy ≤ S_bound. -/
theorem holographic_bound_from_chronogenesis
    (G : GammaSplit) (Entropy S_bound : ℝ → ℝ)
    (h : ChronogenesisAssumptions G Entropy S_bound) (s : ℝ) :
    Entropy s ≤ S_bound s := by
  have hsplit := G.split s
  have hΓ_nn := h.Γ_nonneg s
  have h_cost_le_loc : G.Γ_cost s ≤ G.Γ_loc s := by
    have : 0 ≤ G.Γ_loc s - G.Γ_cost s := by rw [← hsplit]; exact hΓ_nn
    linarith
  calc Entropy s
      ≤ G.Γ_cost s := h.entropy_le_cost s
    _ ≤ G.Γ_loc s := h_cost_le_loc
    _ ≤ S_bound s := h.loc_le_bound s

/-- The chronogenetic cone: {s | Γ(s) ≥ 0}. -/
def ChronogeneticCone (Γ : ℝ → ℝ) : Set ℝ := {s | 0 ≤ Γ s}

theorem holographic_bound_on_cone
    (G : GammaSplit) (Entropy : ℝ → ℝ) (A L_P gamma k_0 : ℝ)
    (h : ChronogenesisAssumptions G Entropy (fun _ => S_BH A L_P gamma k_0)) :
    ∀ s ∈ ChronogeneticCone G.Γ, Entropy s ≤ S_BH A L_P gamma k_0 := by
  intro s _hs
  exact holographic_bound_from_chronogenesis G Entropy (fun _ => S_BH A L_P gamma k_0) h s

end QFTT.WESH.Section6.Part2
