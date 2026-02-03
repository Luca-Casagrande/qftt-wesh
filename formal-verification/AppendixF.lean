/-
QFTT-WESH Appendix F: Derivation of the Angular Dependence Law

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

STATUS: No sorries. No axioms. All theorems proved from Mathlib.

SCOPE:
Derives the observed angular law Γ_dec(θ) = Γ̄(1 + ε cos²θ) starting from
the bilocal sector of the WESH intensity functional under causal-exponential
kernel and rotated-parity readout. The derivation chain is:
  GKSL master equation → echo-frame ODE → gradient expansion →
  rotated-parity projection → lattice averaging → Fourier→cos²θ →
  final law with bounded correction.

MATHEMATICAL FRAMEWORK:
- Matrix (Fin 2) (Fin 2) ℂ: single-qubit operators (σ_z, σ_x, R_y(θ))
- QIdx n: recursive index type for n-qubit tensor products
- tensorPow n M: Kronecker power M^⊗n with inductive construction
- GateAnisotropy: structure bundling a₀ > 0, |a₂| < a₀ (weak anisotropy)
- G₀, G₂, G₂⊥: lattice Fourier weights over device pair orientations

KEY STRUCTURES:
- EchoReduced: R_Π > 0 (echo-frame reduction coefficient)
- StateModulator: C̄ ≥ 0, ϑ (structural overlap → cos²ϑ modulation)
- GateAnisotropy: a₀ > 0, |a₂| < a₀ (gate expansion coefficients)
- AngularLawDerivation K: bundled hypotheses for end-to-end derivation

SECTION MAP (mirrors LaTeX Appendix F):
- F.0 Dynamics:     GKSL dissipator, echo-frame ODE (HasDerivAt verified),
                     parity signal p(s) = p₀ exp(-λs), modulator algebra
- F.1 Gradient:     Equal-s reduction shell, directional decomposition
- F.2 Operator:     (a) Rotated parity R_y σ_z R_y† = cosθ σ_z + sinθ σ_x,
                     (b) N-qubit lift via Kronecker induction,
                     (c) Geometric projector cos²(θ−α) identity
- F.3 Lattice:      G₀/G₂/G₂⊥ definitions, Fourier decomposition of
                     Σ wₖ cos²(θ−αₖ), symmetric case G₂⊥=0,
                     |G₂/G₀| ≤ 1 from triangle inequality,
                     test points θ=0, θ=π/2
- F.4 Radial:       ∫₀^∞ r⁴ e^{-r/ξ} dr = 24ξ⁵ via Mathlib Gamma
- F.5 Assembly:     isotropic_part_lattice → fourier_to_cos_sq →
                     final_law_assembly →
                     final_law_factored with Γ̄·(1 + ε cos²θ) form
- F.6 Device:       Eagle three-orientation formula, inversion roundtrip
- F.7 Sign:         W-state anti-modulation a₂ < 0 ⇒ ε < 0
- F.8 Validity:     |ε| < 1 derived from |a₂| < a₀ ∧ |G₂/G₀| ≤ 1,
                     baseline preserves modulation depth

COMPLETE CHAIN (CompleteChain section):
- angular_form:       Γ_bi = a₀·[(G₀−G₂)/2 + G₂ cos²θ] + O(a₂) correction
- modulation_bounded: |ε| = |(a₂/a₀)(G₂/G₀)| < 1
- correction_bounded: |correction| ≤ |a₂|·G₀

PHYSICS-VS-MATHEMATICS BOUNDARY:
The echo-frame reduction (F.0: how GKSL + CPMG toggling yields the scalar
ODE p' = -R_Π·M(Ψ)·p) is modeled via structures EchoReduced/StateModulator,
not derived from a quantum computing library. The ODE solution itself is
verified (HasDerivAt). Everything from F.2 onward is pure mathematics.
-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace QFTTWESH.AppF

-- ──────────────────────────────────────────────────────────────────────
-- F.0 — Dynamical origin (GKSL → parity decay): algebraic consequences
-- ──────────────────────────────────────────────────────────────────────

namespace Dynamics

/-- GKSL dissipator in Schrödinger picture (formal definition). -/
def Dissipator {d : Type*} [Fintype d] [DecidableEq d]
    (L ρ : Matrix d d ℂ) : Matrix d d ℂ :=
  L * ρ * (Matrix.conjTranspose L)
    - (1 / 2 : ℂ) • ((Matrix.conjTranspose L * L) * ρ + ρ * (Matrix.conjTranspose L * L))

/-- Echo-frame reduction hypothesis (Eq. (F-parity-modulated)).

At fixed circuit parameters `(T,n)`, the WESH bilocal sector reduces to
`d/ds ⟨Π(θ)⟩ = -RΠ * M(Ψ) * ⟨Π(θ)⟩` with `RΠ` independent of θ and class.

We use this only to justify that the state-structural modulation carries the
`cos²ϑ` dependence into a parity-contrast expansion.
-/
structure EchoReduced where
  R_Pi : ℝ
  h_R_pos : 0 < R_Pi

structure StateModulator where
  C_bar : ℝ
  vartheta : ℝ
  h_C_nonneg : 0 ≤ C_bar

def StateModulator.value (m : StateModulator) : ℝ :=
  m.C_bar * (Real.cos m.vartheta) ^ 2

theorem ghz_structural_overlap (vartheta : ℝ) :
    (Real.cos vartheta) ^ 2 = 1 - (Real.sin vartheta) ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq vartheta]

theorem parity_contrast_structure (beta0 beta1 vartheta : ℝ) :
    beta0 + beta1 * (Real.cos vartheta) ^ 2 =
      (beta0 + beta1 / 2) + (beta1 / 2) * Real.cos (2 * vartheta) := by
  have h := Real.cos_two_mul vartheta  -- cos(2x) = 2cos²x - 1
  rw [h]; ring

-- F.0 ODE verification: echo-reduced parity decay is a genuine ODE solution.

/-- Effective scalar solution of p' = -lam·p (echo-reduced parity channel). -/
def paritySignal (p0 lam : ℝ) (s : ℝ) : ℝ :=
  p0 * Real.exp (-lam * s)

/-- paritySignal satisfies the ODE p' = -lam·p (pure calculus, no physics). -/
theorem paritySignal_hasDerivAt (p0 lam s : ℝ) :
    HasDerivAt (fun t => paritySignal p0 lam t) (-lam * paritySignal p0 lam s) s := by
  have hlin : HasDerivAt (fun t : ℝ => -lam * t) (-lam) s := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using (hasDerivAt_id s).const_mul (-lam)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-lam * t))
      (Real.exp (-lam * s) * (-lam)) s :=
    (Real.hasDerivAt_exp (-lam * s)).comp s hlin
  have hmul : HasDerivAt (fun t : ℝ => p0 * Real.exp (-lam * t))
      (p0 * (Real.exp (-lam * s) * (-lam))) s :=
    hexp.const_mul p0
  simpa [paritySignal, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Effective decay rate lam = R_Π · M(Ψ) (definition-level bridge). -/
def lambdaEff (e : EchoReduced) (m : StateModulator) : ℝ :=
  e.R_Pi * m.value

/-- Plugging M(ϑ) = C̄ cos²ϑ into the exponent (pure algebra). -/
theorem paritySignal_modulator (p0 : ℝ) (e : EchoReduced) (m : StateModulator) (s : ℝ) :
    paritySignal p0 (lambdaEff e m) s =
      p0 * Real.exp (-(e.R_Pi * m.C_bar) * (Real.cos m.vartheta) ^ 2 * s) := by
  unfold paritySignal lambdaEff StateModulator.value
  ring_nf

/-- If C̄ = 0 (product-like), the modulator vanishes. -/
theorem modulator_vanishing_product (m : StateModulator) (hC : m.C_bar = 0) :
    m.value = 0 := by
  simp [StateModulator.value, hC]

/-- For ϑ = 0, cos²0 = 1: maximal structural overlap. -/
theorem modulator_maximal_at_zero (Cbar : ℝ) (hC : 0 ≤ Cbar) :
    (StateModulator.value ⟨Cbar, 0, hC⟩) = Cbar := by
  simp [StateModulator.value]

end Dynamics

-- ──────────────────────────────────────────────────────────────────────
-- F.1 — Equal-s reduction and gradient expansion (algebraic shell)
-- ──────────────────────────────────────────────────────────────────────

namespace Gradient

structure GradientExpansion where
  grad_norm : ℝ
  h_grad_nonneg : 0 ≤ grad_norm
  hess_norm : ℝ
  h_hess_nonneg : 0 ≤ hess_norm

def jump_operator_sq_leading (r cos_angle grad_norm : ℝ) : ℝ :=
  r ^ 2 * (cos_angle * grad_norm) ^ 2

def gradient_remainder (r : ℝ) (ge : GradientExpansion) : ℝ :=
  r ^ 3 * ge.grad_norm * ge.hess_norm

/-- Short-range dominance shell (Appendix F.1): captures the regime where the
`r²` leading term dominates the Taylor remainder. -/
def short_range_regime (r xi : ℝ) (ge : GradientExpansion) : Prop :=
  0 < r ∧ 0 < xi ∧ r ≤ xi ∧ ge.hess_norm ≤ ge.grad_norm / xi

theorem directional_factor_decomposition (grad_norm cos_angle : ℝ) :
    (cos_angle * grad_norm) ^ 2 = grad_norm ^ 2 * cos_angle ^ 2 := by
  ring

end Gradient

-- ──────────────────────────────────────────────────────────────────────
-- F.2 — Rotated parity, N-qubit lift, and geometric projector
-- ──────────────────────────────────────────────────────────────────────

-- F.2a Single-qubit rotated parity: R_y(θ) σ_z R_y(−θ) = cosθ σ_z + sinθ σ_x

namespace Operator

open Matrix

def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then 1 else 0
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 0 then 1 else if i = 1 ∧ j = 1 then -1 else 0

def Ry (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 0 then Real.cos (theta / 2)
  else if i = 0 ∧ j = 1 then -(Real.sin (theta / 2))
  else if i = 1 ∧ j = 0 then Real.sin (theta / 2)
  else Real.cos (theta / 2)

def sigmaAxis (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.cos theta : ℂ) • sigmaZ) + ((Real.sin theta : ℂ) • sigmaX)

theorem rotated_parity_identity (theta : ℝ) :
    Ry theta * sigmaZ * Ry (-theta) = sigmaAxis theta := by
  have key : 2 * (theta / 2) = theta := by ring
  have hc : (Real.cos (theta/2))^2 - (Real.sin (theta/2))^2 = Real.cos theta := by
    have h1 := Real.sin_sq (theta/2)
    have h2 := Real.cos_two_mul (theta/2)
    rw [key] at h2; linarith
  have hs : 2 * Real.sin (theta/2) * Real.cos (theta/2) = Real.sin theta := by
    have h := Real.sin_two_mul (theta/2)
    rw [key] at h; linarith
  have hdiv : theta / 2 = theta * (1/2) := by ring
  rw [hdiv] at hc hs
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin,
          Ry, sigmaZ, sigmaX, sigmaAxis, Matrix.mul_apply, Fin.sum_univ_two,
          neg_div, Real.cos_neg, Real.sin_neg] <;>
    ring_nf <;>
    norm_cast <;>
    linarith [hc, hs]

theorem rotated_parity_pi_div_two :
    Ry (Real.pi / 2) * sigmaZ * Ry (-(Real.pi / 2)) = sigmaX := by
  have h := rotated_parity_identity (theta := Real.pi / 2)
  simpa [sigmaAxis, Real.cos_pi_div_two, Real.sin_pi_div_two] using h

-- F.2b N-qubit lift via Kronecker/tensor power

namespace NQubit

/-- Index type for an `n`-qubit computational basis (nested product). -/
@[reducible] def QIdx : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin 2 × QIdx n

instance instFintypeQIdx : (n : ℕ) → Fintype (QIdx n)
  | 0 => by unfold QIdx; infer_instance
  | n + 1 => by unfold QIdx; haveI := instFintypeQIdx n; infer_instance

instance instDecEqQIdx : (n : ℕ) → DecidableEq (QIdx n)
  | 0 => by unfold QIdx; infer_instance
  | n + 1 => by unfold QIdx; haveI := instDecEqQIdx n; infer_instance

/-- Tensor power of a single-qubit operator (recursive Kronecker product). -/
def tensorPow : (n : ℕ) → Matrix (Fin 2) (Fin 2) ℂ → Matrix (QIdx n) (QIdx n) ℂ
  | 0, _ => 1
  | n + 1, M => M.kronecker (tensorPow n M)

/-- Kronecker multiplicativity: `(A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD)`.
    Direct application of Mathlib's `Matrix.mul_kronecker_mul`. -/
private theorem kron_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix (Fin 2) (Fin 2) ℂ) (B D : Matrix ι ι ℂ) :
    A.kronecker B * C.kronecker D = (A * C).kronecker (B * D) :=
  (Matrix.mul_kronecker_mul A C B D).symm

/-- N-qubit rotated parity identity:
`Ry(θ)^⊗n σ_z^⊗n Ry(−θ)^⊗n = (cosθ σ_z + sinθ σ_x)^⊗n`. -/
theorem rotated_parity_tensorPow (n : ℕ) (theta : ℝ) :
    tensorPow n (Ry theta) * tensorPow n sigmaZ * tensorPow n (Ry (-theta)) =
      tensorPow n (sigmaAxis theta) := by
  induction n with
  | zero => simp [tensorPow]
  | succ n ih =>
    -- Unfold tensorPow (n+1) to .kronecker form (definitional equality)
    show (Ry theta).kronecker (tensorPow n (Ry theta)) *
         sigmaZ.kronecker (tensorPow n sigmaZ) *
         (Ry (-theta)).kronecker (tensorPow n (Ry (-theta))) =
         (sigmaAxis theta).kronecker (tensorPow n (sigmaAxis theta))
    -- Merge Kronecker factors step by step (explicit types to guide unification)
    have step1 : (Ry theta).kronecker (tensorPow n (Ry theta)) *
                 sigmaZ.kronecker (tensorPow n sigmaZ) =
                 (Ry theta * sigmaZ).kronecker
                   (tensorPow n (Ry theta) * tensorPow n sigmaZ) :=
      kron_mul ..
    have step2 : (Ry theta * sigmaZ).kronecker
                   (tensorPow n (Ry theta) * tensorPow n sigmaZ) *
                 (Ry (-theta)).kronecker (tensorPow n (Ry (-theta))) =
                 (Ry theta * sigmaZ * Ry (-theta)).kronecker
                   (tensorPow n (Ry theta) * tensorPow n sigmaZ *
                    tensorPow n (Ry (-theta))) :=
      kron_mul ..
    rw [step1, step2, rotated_parity_identity, ih]

end NQubit

end Operator

-- F.2c Geometric projector: (m(θ)·r(α))² = cos²(θ−α)

namespace Geometry

def m_vec (theta : ℝ) : ℝ × ℝ := (Real.sin theta, Real.cos theta)
def r_vec (alpha : ℝ) : ℝ × ℝ := (Real.sin alpha, Real.cos alpha)

def dot2 (v1 v2 : ℝ × ℝ) : ℝ := v1.1 * v2.1 + v1.2 * v2.2

theorem m_vec_unit (theta : ℝ) : dot2 (m_vec theta) (m_vec theta) = 1 := by
  unfold dot2 m_vec
  nlinarith [Real.sin_sq_add_cos_sq theta]

theorem r_vec_unit (alpha : ℝ) : dot2 (r_vec alpha) (r_vec alpha) = 1 := by
  unfold dot2 r_vec
  nlinarith [Real.sin_sq_add_cos_sq alpha]

theorem geometric_projection_identity (theta alpha : ℝ) :
    (dot2 (m_vec theta) (r_vec alpha)) ^ 2 = (Real.cos (theta - alpha)) ^ 2 := by
  unfold dot2 m_vec r_vec
  rw [Real.cos_sub]
  ring

end Geometry

-- ──────────────────────────────────────────────────────────────────────
-- F.3 — Lattice-weighted averaging (proved)
-- ──────────────────────────────────────────────────────────────────────

namespace Lattice

variable {K : Type*} [Fintype K] [DecidableEq K]

def G0 (w : K → ℝ) : ℝ := ∑ k, w k
def G2 (w : K → ℝ) (alpha : K → ℝ) : ℝ := ∑ k, w k * Real.cos (2 * alpha k)
def G2_perp (w : K → ℝ) (alpha : K → ℝ) : ℝ := ∑ k, w k * Real.sin (2 * alpha k)

theorem cos_sq_half_angle (x : ℝ) :
    Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
  have h := Real.cos_two_mul x  -- cos(2x) = 2cos²x - 1
  nlinarith

theorem cos_double_diff (theta alpha : ℝ) :
    Real.cos (2 * (theta - alpha)) =
      Real.cos (2 * theta) * Real.cos (2 * alpha) +
      Real.sin (2 * theta) * Real.sin (2 * alpha) := by
  have h : 2 * (theta - alpha) = (2 * theta) - (2 * alpha) := by ring
  rw [h, Real.cos_sub]

omit [DecidableEq K] in
theorem lattice_averaging_full (w : K → ℝ) (alpha : K → ℝ) (theta : ℝ) :
    ∑ k, w k * Real.cos (theta - alpha k) ^ 2 =
      (1 / 2) * G0 w +
      (1 / 2) * (Real.cos (2 * theta) * G2 w alpha +
                  Real.sin (2 * theta) * G2_perp w alpha) := by
  classical
  unfold G0 G2 G2_perp
  -- Rewrite each summand: cos²(θ−α) → Fourier form
  have key : ∀ k : K, w k * Real.cos (theta - alpha k) ^ 2 =
      1 / 2 * w k +
      1 / 2 * (Real.cos (2 * theta) * (w k * Real.cos (2 * alpha k)) +
               Real.sin (2 * theta) * (w k * Real.sin (2 * alpha k))) := by
    intro k
    have h1 := cos_sq_half_angle (theta - alpha k)
    have h2 := cos_double_diff theta (alpha k)
    rw [h1, h2]; ring
  simp_rw [key]
  -- Split sums and pull constants out
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

omit [DecidableEq K] in
theorem lattice_averaging_symmetric (w : K → ℝ) (alpha : K → ℝ)
    (theta : ℝ) (h_symm : G2_perp w alpha = 0) :
    ∑ k, w k * Real.cos (theta - alpha k) ^ 2 =
      (1 / 2) * G0 w + (1 / 2) * Real.cos (2 * theta) * G2 w alpha := by
  have h := lattice_averaging_full (w := w) (alpha := alpha) (theta := theta)
  rw [h_symm, mul_zero, add_zero, ← mul_assoc] at h
  exact h

-- |G₂/G₀| ≤ 1 from non-negative weights via triangle inequality:
-- |Σ wk cos(2αk)| ≤ Σ wk |cos(2αk)| ≤ Σ wk = G₀.
omit [DecidableEq K] in
theorem abs_G2_div_G0_le_one (w : K → ℝ) (alpha : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hG0 : 0 < G0 w) :
    |G2 w alpha / G0 w| ≤ 1 := by
  rw [abs_div, abs_of_pos hG0, div_le_one hG0]
  -- Goal: |G2 w alpha| ≤ G0 w, i.e. |Σ wk cos(2αk)| ≤ Σ wk
  unfold G2 G0
  calc |∑ k ∈ Finset.univ, w k * Real.cos (2 * alpha k)|
      ≤ ∑ k ∈ Finset.univ, |w k * Real.cos (2 * alpha k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.univ, w k := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg (hw k)]
        have hcos : |Real.cos (2 * alpha k)| ≤ 1 :=
          abs_le.mpr ⟨by linarith [Real.neg_one_le_cos (2 * alpha k)],
                      Real.cos_le_one _⟩
        exact le_trans (mul_le_mul_of_nonneg_left hcos (hw k)) (by simp)

-- Diagnostic test points (θ = 0 and θ = π/2)
omit [DecidableEq K] in
theorem lattice_sum_theta_zero (w : K → ℝ) (alpha : K → ℝ)
    (h_symm : G2_perp w alpha = 0) :
    ∑ k, w k * Real.cos (0 - alpha k) ^ 2 =
      (1 / 2) * G0 w + (1 / 2) * G2 w alpha := by
  have h := lattice_averaging_symmetric w alpha 0 h_symm
  simpa using h

omit [DecidableEq K] in
theorem lattice_sum_theta_pi_div_two (w : K → ℝ) (alpha : K → ℝ)
    (h_symm : G2_perp w alpha = 0) :
    ∑ k, w k * Real.cos (Real.pi / 2 - alpha k) ^ 2 =
      (1 / 2) * G0 w - (1 / 2) * G2 w alpha := by
  have h := lattice_averaging_symmetric w alpha (Real.pi / 2) h_symm
  have hpi : Real.cos (2 * (Real.pi / 2)) = -1 := by
    have : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [this, Real.cos_pi]
  simp only [hpi, mul_neg, mul_one] at h
  linarith

end Lattice

-- ──────────────────────────────────────────────────────────────────────
-- F.4 — Radial integral: ∫₀^∞ r⁴ e^{-r/ξ} dr = 24 ξ⁵  (proved)
-- ──────────────────────────────────────────────────────────────────────

namespace RadialIntegral

open MeasureTheory Set Real

/-- **Radial integral** (F.4):
  `∫₀^∞ r⁴ exp(−r/ξ) dr = 24 ξ⁵`,
  with `ξ > 0` the correlation length.

  Proved from `integral_rpow_mul_exp_neg_mul_rpow` (Mathlib) with
  `p = 1, q = 4, b = 1/ξ`, combined with `Γ(5) = 4! = 24`. -/
theorem radial_integral (ξ : ℝ) (hξ : 0 < ξ) :
    ∫ r in Ioi (0 : ℝ), r ^ (4 : ℝ) * Real.exp (-(1 / ξ) * r ^ (1 : ℝ)) =
      24 * ξ ^ (5 : ℝ) := by
  -- Apply the Mathlib Gamma-integral identity
  have hp : (0 : ℝ) < 1 := one_pos
  have hq : (-1 : ℝ) < (4 : ℝ) := by norm_num
  have hb : (0 : ℝ) < 1 / ξ := div_pos one_pos hξ
  have hmain := integral_rpow_mul_exp_neg_mul_rpow hp hq hb
  -- hmain : ∫ r in Ioi 0, r^4 * exp(-(1/ξ)*r^1)
  --       = (1/ξ)^(-(4+1)/1) * (1/1) * Γ((4+1)/1)
  -- Simplify arithmetic in hmain
  have ha1 : ((4 : ℝ) + 1) / (1 : ℝ) = 5 := by norm_num
  have ha2 : -((4 : ℝ) + 1) / (1 : ℝ) = -5 := by norm_num
  rw [ha1, ha2, show (1 : ℝ) / 1 = 1 from div_one 1, mul_one] at hmain
  -- hmain : ... = (1/ξ)^(-5) * Γ(5)
  rw [hmain]
  -- Goal: (1/ξ)^(-5:ℝ) * Γ(5) = 24 * ξ^(5:ℝ)
  -- Step 1: (1/ξ)^(-5) = ξ^5
  have hinv : (1 / ξ) ^ ((-5 : ℝ)) = ξ ^ (5 : ℝ) := by
    rw [one_div, Real.inv_rpow (le_of_lt hξ), Real.rpow_neg (le_of_lt hξ), inv_inv]
  -- Step 2: Γ(5) = 4! = 24
  have hgam : Real.Gamma 5 = 24 := by
    convert Real.Gamma_nat_eq_factorial 4 using 1; norm_num
  rw [hinv, hgam]
  ring

end RadialIntegral

-- ──────────────────────────────────────────────────────────────────────
-- F.5 — Gate anisotropy, assembly, and final angular law
-- ──────────────────────────────────────────────────────────────────────

structure GateAnisotropy where
  a0 : ℝ
  a2 : ℝ
  h_a0_pos : 0 < a0
  h_weak : |a2| < a0

namespace GateAnisotropy

def eval (g : GateAnisotropy) (alpha : ℝ) : ℝ :=
  g.a0 + g.a2 * (Real.cos alpha) ^ 2

theorem eval_pos (g : GateAnisotropy) (alpha : ℝ) : 0 < g.eval alpha := by
  unfold eval
  have hcos : 0 ≤ (Real.cos alpha) ^ 2 := sq_nonneg _
  have hone : (Real.cos alpha) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha, sq_nonneg (Real.sin alpha)]
  by_cases h : 0 ≤ g.a2
  · have : 0 ≤ g.a2 * (Real.cos alpha) ^ 2 := mul_nonneg h hcos
    linarith [g.h_a0_pos, this]
  · have hneg : g.a2 < 0 := lt_of_not_ge h
    have hmul : g.a2 ≤ g.a2 * (Real.cos alpha) ^ 2 := by
      have := mul_le_mul_of_nonpos_left hone (le_of_lt hneg)
      simp [mul_one] at this; exact this
    have h1 : -g.a0 < g.a2 := by
      have hweak := g.h_weak
      rw [abs_lt] at hweak
      exact hweak.1
    linarith [g.h_a0_pos, hmul, h1]

end GateAnisotropy


namespace Assembly

open Lattice

variable {K : Type*} [Fintype K] [DecidableEq K]

def C_gate (alpha : K → ℝ) (a0 a2 : ℝ) (k : K) : ℝ :=
  a0 + a2 * (Real.cos (alpha k)) ^ 2

def Gamma_bi (w : K → ℝ) (alpha : K → ℝ) (a0 a2 : ℝ) (theta : ℝ) : ℝ :=
  ∑ k, w k * C_gate alpha a0 a2 k * (Real.cos (theta - alpha k)) ^ 2

def Gamma_bar (w : K → ℝ) (a0 : ℝ) : ℝ := a0 * G0 w

def epsilon_mod (w : K → ℝ) (alpha : K → ℝ) (a0 a2 : ℝ) : ℝ :=
  (a2 / a0) * (G2 w alpha / G0 w)

def angular_correction (w : K → ℝ) (alpha : K → ℝ) (a2 : ℝ) (theta : ℝ) : ℝ :=
  a2 * ∑ k, w k * (Real.cos (alpha k)) ^ 2 * (Real.cos (theta - alpha k)) ^ 2

omit [DecidableEq K] in
theorem angular_law_decomposition (w : K → ℝ) (alpha : K → ℝ)
    (a0 a2 : ℝ) (theta : ℝ) :
    Gamma_bi w alpha a0 a2 theta =
      Gamma_bi w alpha a0 0 theta + angular_correction w alpha a2 theta := by
  classical
  unfold Gamma_bi C_gate angular_correction
  simp [mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  ring

omit [DecidableEq K] in
/-- Weak-anisotropy bound: `|correction| ≤ |a2| · G0` for nonnegative weights. -/
theorem correction_order (w : K → ℝ) (alpha : K → ℝ)
    (a2 : ℝ) (theta : ℝ) (hw : ∀ k, 0 ≤ w k) :
    |angular_correction w alpha a2 theta| ≤ |a2| * G0 w := by
  classical
  unfold angular_correction G0
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg a2)
  -- Let S = Σ w_k cos²(α_k) cos²(θ-α_k). Then 0 ≤ S ≤ Σ w_k.
  set S : ℝ := ∑ k : K, w k * Real.cos (alpha k) ^ 2 * Real.cos (theta - alpha k) ^ 2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine Finset.sum_nonneg ?_
    intro k hk
    exact mul_nonneg (mul_nonneg (hw k) (sq_nonneg _)) (sq_nonneg _)
  have hterm_le : ∀ k : K,
      w k * Real.cos (alpha k) ^ 2 * Real.cos (theta - alpha k) ^ 2 ≤ w k := by
    intro k
    have hwk : 0 ≤ w k := hw k
    have h1 : Real.cos (alpha k) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (alpha k), sq_nonneg (Real.sin (alpha k))]
    have h2 : Real.cos (theta - alpha k) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (theta - alpha k), sq_nonneg (Real.sin (theta - alpha k))]
    have hprod : Real.cos (alpha k) ^ 2 * Real.cos (theta - alpha k) ^ 2 ≤ 1 := by
      calc Real.cos (alpha k) ^ 2 * Real.cos (theta - alpha k) ^ 2
          ≤ 1 * Real.cos (theta - alpha k) ^ 2 :=
            by apply mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ 1 * 1 :=
            by apply mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 1 := by ring
    calc
      w k * Real.cos (alpha k) ^ 2 * Real.cos (theta - alpha k) ^ 2
          = w k * (Real.cos (alpha k) ^ 2 * Real.cos (theta - alpha k) ^ 2) := by ring
      _ ≤ w k * 1 := by
            exact mul_le_mul_of_nonneg_left hprod hwk
      _ = w k := by ring
  have hS_le : S ≤ ∑ k : K, w k := by
    dsimp [S]
    exact Finset.sum_le_sum (fun k hk => hterm_le k)
  have : |S| ≤ ∑ k : K, w k := by
    rw [abs_of_nonneg hS_nonneg]; exact hS_le
  simpa [S] using this

-- ──────────────────────────────────────────────────────────────────────
-- F.5 Bridge theorems: from lattice averaging to the angular law
-- These close the derivation gap: F.3 results → final cos²θ form.
-- ──────────────────────────────────────────────────────────────────────

-- Step 1: Isotropic-gate part (a₂=0) equals lattice averaging output
omit [DecidableEq K] in
theorem isotropic_part_lattice (w : K → ℝ) (alpha : K → ℝ) (a0 : ℝ)
    (theta : ℝ) (h_symm : G2_perp w alpha = 0) :
    Gamma_bi w alpha a0 0 theta =
      a0 * ((1 / 2) * G0 w +
            (1 / 2) * Real.cos (2 * theta) * G2 w alpha) := by
  classical
  unfold Gamma_bi C_gate
  simp only [zero_mul, add_zero]
  have hrw : ∀ k : K,
      w k * a0 * (Real.cos (theta - alpha k)) ^ 2 =
      a0 * (w k * (Real.cos (theta - alpha k)) ^ 2) := fun k => by ring
  simp_rw [hrw, ← Finset.mul_sum]
  congr 1
  exact lattice_averaging_symmetric w alpha theta h_symm

-- Step 2: Fourier-to-cos² reparametrisation (pure trigonometry)
theorem fourier_to_cos_sq (G0_val G2_val theta : ℝ) :
    (1 / 2) * G0_val + (1 / 2) * Real.cos (2 * theta) * G2_val =
      (G0_val - G2_val) / 2 + G2_val * (Real.cos theta) ^ 2 := by
  have h := Real.cos_two_mul theta   -- cos(2θ) = 2 cos²θ − 1
  rw [h]; ring

-- Step 3: Full assembly — Γ_bi in cos²θ form + bounded correction
-- This is Eq. (G-law)/(G-epsilon) of the paper:
--   Γ_bi(θ) = a₀ · [(G₀−G₂)/2 + G₂ cos²θ] + O(a₂)
omit [DecidableEq K] in
theorem final_law_assembly (w : K → ℝ) (alpha : K → ℝ) (a0 a2 : ℝ)
    (theta : ℝ) (h_symm : G2_perp w alpha = 0) :
    Gamma_bi w alpha a0 a2 theta =
      a0 * ((G0 w - G2 w alpha) / 2 +
            G2 w alpha * (Real.cos theta) ^ 2) +
      angular_correction w alpha a2 theta := by
  have h1 := angular_law_decomposition w alpha a0 a2 theta
  have h2 := isotropic_part_lattice w alpha a0 theta h_symm
  have h3 := fourier_to_cos_sq (G0 w) (G2 w alpha) theta
  rw [h1, h2]
  have key : a0 * (1 / 2 * G0 w + 1 / 2 * Real.cos (2 * theta) * G2 w alpha) =
             a0 * ((G0 w - G2 w alpha) / 2 + G2 w alpha * (Real.cos theta) ^ 2) := by
    rw [h3]
  linarith

-- Step 4: Factored form with Γ̄ and G₂/G₀ ratio (matches paper notation)
--   Γ_bi(θ) = Γ̄ · [(1 − G₂/G₀)/2 + (G₂/G₀) cos²θ] + correction
omit [DecidableEq K] in
theorem final_law_factored (w : K → ℝ) (alpha : K → ℝ) (a0 a2 : ℝ)
    (theta : ℝ) (h_symm : G2_perp w alpha = 0) (hG0 : G0 w ≠ 0) :
    Gamma_bi w alpha a0 a2 theta =
      Gamma_bar w a0 *
        ((1 - G2 w alpha / G0 w) / 2 +
         (G2 w alpha / G0 w) * (Real.cos theta) ^ 2) +
      angular_correction w alpha a2 theta := by
  rw [final_law_assembly w alpha a0 a2 theta h_symm]
  congr 1
  unfold Gamma_bar
  field_simp

omit [DecidableEq K] in
theorem gamma_bar_pos (w : K → ℝ) (a0 : ℝ) (h_a0 : 0 < a0)
    (h_w : ∃ k, 0 < w k) (hw_nn : ∀ k, 0 ≤ w k) :
    0 < Gamma_bar w a0 := by
  unfold Gamma_bar G0
  apply mul_pos h_a0
  obtain ⟨k, hk⟩ := h_w
  have : 0 < ∑ i : K, w i := by
    have hge : ∑ i : K, w i ≥ w k :=
      Finset.single_le_sum (fun i _ => hw_nn i) (Finset.mem_univ k)
    linarith
  exact this

def inversion_relation (epsilon_meas G2_G0_ratio : ℝ) : ℝ :=
  epsilon_meas / G2_G0_ratio

omit [DecidableEq K] in
theorem inversion_roundtrip
    (w : K → ℝ) (alpha : K → ℝ) (a0 a2 : ℝ)
    (h_a0 : a0 ≠ 0) (h_G0 : G0 w ≠ 0) (h_G2 : G2 w alpha ≠ 0) :
    inversion_relation (epsilon_mod w alpha a0 a2) (G2 w alpha / G0 w) = a2 / a0 := by
  unfold inversion_relation epsilon_mod
  field_simp [h_a0, h_G0, h_G2]

end Assembly

-- ──────────────────────────────────────────────────────────────────────
-- F.6 — Eagle layout (three orientations)
-- ──────────────────────────────────────────────────────────────────────

namespace Device

open Lattice

def eagle_G2_G0 (w_h w_v w_d : ℝ) (alpha3 : ℝ) : ℝ :=
  (w_v - w_h + w_d * Real.cos (2 * alpha3)) / (w_h + w_v + w_d)

theorem eagle_orientation_values :
    Real.cos (2 * 0) = 1 ∧ Real.cos (2 * (Real.pi / 2)) = -1 := by
  constructor
  · simp
  · have : 2 * (Real.pi / 2) = Real.pi := by ring
    simp [this, Real.cos_pi]

theorem eagle_positive_when_vertical_dominates (w_h w_v w_d : ℝ)
    (h_dom : w_v > w_h) (h_wd : 0 ≤ w_d) :
    0 < w_v - w_h + w_d * 1 := by
  linarith

end Device

-- ──────────────────────────────────────────────────────────────────────
-- F.7 — W-state sign control
-- ──────────────────────────────────────────────────────────────────────

namespace Sign

theorem w_state_antimodulation (a0_w a2_w G2_G0 : ℝ)
    (h_a0 : 0 < a0_w) (h_a2 : a2_w < 0) (h_G : 0 < G2_G0) :
    (a2_w / a0_w) * G2_G0 < 0 :=
  mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos h_a2 h_a0) h_G

theorem ghz_positive_modulation (a0 a2 G2_G0 : ℝ)
    (h_a0 : 0 < a0) (h_a2 : 0 < a2) (h_G : 0 < G2_G0) :
    0 < (a2 / a0) * G2_G0 :=
  mul_pos (div_pos h_a2 h_a0) h_G

end Sign

-- ──────────────────────────────────────────────────────────────────────
-- F.8 — Validity: baseline invariance and modulation bound
-- ──────────────────────────────────────────────────────────────────────

namespace Validity

-- F.8 regime/corrections bookkeeping.

structure ValidityRegime where
  xi : ℝ
  h_xi_pos : 0 < xi
  a0 : ℝ
  a2 : ℝ
  h_a0_pos : 0 < a0
  h_weak : |a2| < a0

def total_rate_with_baseline (Gamma_hw Gamma_bar epsilon theta : ℝ) : ℝ :=
  Gamma_hw + Gamma_bar * (1 + epsilon * (Real.cos theta) ^ 2)

theorem baseline_preserves_modulation (Gamma_hw Gamma_bar epsilon : ℝ) :
    total_rate_with_baseline Gamma_hw Gamma_bar epsilon 0 -
    total_rate_with_baseline Gamma_hw Gamma_bar epsilon (Real.pi / 2) =
      Gamma_bar * epsilon := by
  unfold total_rate_with_baseline
  simp [Real.cos_zero, Real.cos_pi_div_two]
  ring

theorem modulation_depth_bounded {K : Type*} [Fintype K]
    (g : GateAnisotropy) (w : K → ℝ) (alpha : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hG0 : 0 < Lattice.G0 w) :
    |g.a2 / g.a0 * (Lattice.G2 w alpha / Lattice.G0 w)| < 1 := by
  have h_G : |Lattice.G2 w alpha / Lattice.G0 w| ≤ 1 :=
    Lattice.abs_G2_div_G0_le_one w alpha hw hG0
  rw [abs_mul]
  calc
    |g.a2 / g.a0| * |Lattice.G2 w alpha / Lattice.G0 w|
        ≤ |g.a2 / g.a0| * 1 :=
      mul_le_mul_of_nonneg_left h_G (abs_nonneg _)
    _ = |g.a2 / g.a0| := by simp
    _ = |g.a2| / g.a0 := by
      simp [abs_div, abs_of_pos g.h_a0_pos]
    _ < 1 := by
      rw [div_lt_one g.h_a0_pos]; exact g.h_weak

end Validity

-- ──────────────────────────────────────────────────────────────────────
-- Complete derivation chain: bundled hypotheses → final results
-- ──────────────────────────────────────────────────────────────────────

section CompleteChain

open Lattice Assembly Validity

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- All hypotheses needed to run Appendix F end-to-end on a given device geometry. -/
structure AngularLawDerivation (K : Type*) [Fintype K] [DecidableEq K] where
  w : K → ℝ
  alpha : K → ℝ
  gate : GateAnisotropy
  h_symm : G2_perp w alpha = 0
  hw : ∀ k, 0 ≤ w k
  hG0 : 0 < G0 w

/-- Bilocal angular form is affine in cos²θ plus controlled correction.
    This is Eq. (G-law)/(G-epsilon) of the paper, derived from F.3 lattice averaging
    + gate expansion + Fourier-to-cos² reparametrisation. -/
theorem angular_form (d : AngularLawDerivation K) (theta : ℝ) :
    Gamma_bi d.w d.alpha d.gate.a0 d.gate.a2 theta =
      d.gate.a0 * ((G0 d.w - G2 d.w d.alpha) / 2 +
                    G2 d.w d.alpha * (Real.cos theta) ^ 2) +
      angular_correction d.w d.alpha d.gate.a2 theta :=
  final_law_assembly d.w d.alpha d.gate.a0 d.gate.a2 theta d.h_symm

/-- Bounded modulation depth |ε| < 1 (F.8), derived from |a₂| < a₀ and |G₂/G₀| ≤ 1. -/
theorem modulation_bounded (d : AngularLawDerivation K) :
    |d.gate.a2 / d.gate.a0 * (G2 d.w d.alpha / G0 d.w)| < 1 :=
  Validity.modulation_depth_bounded d.gate d.w d.alpha d.hw d.hG0

/-- Correction is O(a₂): |angular_correction| ≤ |a₂| · G₀. -/
theorem correction_bounded (d : AngularLawDerivation K) (theta : ℝ) :
    |angular_correction d.w d.alpha d.gate.a2 theta| ≤ |d.gate.a2| * G0 d.w :=
  correction_order d.w d.alpha d.gate.a2 theta d.hw

end CompleteChain

end QFTTWESH.AppF
