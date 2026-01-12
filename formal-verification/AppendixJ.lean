import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-
J.0 Doob-Meyer Decomposition: The eigentime counting process N_Eig(s) decomposes as ∫₀ˢ Γ[Ψ(u)]du + M(s), where M(s) is a martingale.
-/
open MeasureTheory ProbabilityTheory


-- We define a structure to hold the context and assumptions of the Eigentime process
structure EigentimeSetup (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  State : Type*
  Γ : State → ℝ
  Ψ : ℝ → State
  N_Eig : ℝ → Ω → ℝ
  ℱ : Filtration ℝ ‹MeasurableSpace Ω›
  -- Assumptions
  Γ_integrable : ∀ s, IntegrableOn (fun u => Γ (Ψ u)) (Set.Ioc 0 s) volume
  N_adapted : Adapted ℱ N_Eig
  N_integrable : ∀ s, Integrable (N_Eig s) μ
  -- Counting process semantics (paper-faithful: N_Eig is a count, not arbitrary ℝ)
  N_nonneg : ∀ s ω, 0 ≤ N_Eig s ω
  N_mono : ∀ ω, Monotone (fun s => N_Eig s ω)
  N_zero : ∀ ω, N_Eig 0 ω = 0
  -- J.0: The Doob-Meyer decomposition assumption
  -- M(s) = N_Eig(s) - ∫₀ˢ Γ[Ψ(u)]du is a martingale
  martingale_M : Martingale (fun s ω => N_Eig s ω - ∫ u in Set.Ioc 0 s, Γ (Ψ u)) ℱ μ

-- J.0: Doob-Meyer Decomposition
-- This theorem extracts the result from the setup.
theorem J0_DoobMeyer (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
  (S : EigentimeSetup Ω μ) :
  let Compensator := fun s => ∫ u in Set.Ioc 0 s, S.Γ (S.Ψ u)
  let M := fun s ω => S.N_Eig s ω - Compensator s
  Martingale M S.ℱ μ := by
  intros Compensator M
  exact S.martingale_M

/-
J.1 Regional Count: For spacetime region R with 4-volume V₄, E[N(R)] ≃ V₄/V_ξ where V_ξ ~ ξ⁴ is the correlation volume.
-/
open MeasureTheory ProbabilityTheory


-- We assume a spacetime manifold M equipped with a measure V4 (volume form)
variable {M : Type*} [MeasurableSpace M] (V4 : Measure M)

-- Hazard function λ(x)
variable (lambda : M → ℝ)

-- Correlation volume V_xi (a constant)
variable (V_xi : ℝ)

-- Regional count N(R) is a random variable depending on the region R
-- We model it as a function from Set M to a random variable on Ω
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
variable (N : Set M → Ω → ℝ)

-- J.1: Regional Count Expectation
-- The claim is E[N(R)] = ∫_R λ(x) dV4(x)
-- And for large regions, this is approx V4(R) / V_xi
-- We will formalize the exact relation as a definition/axiom of the process intensity.

def ExpectedCount (R : Set M) : ℝ := ∫ ω, N R ω

-- The hypothesis that N is an inhomogeneous Poisson process with intensity λ
-- implies E[N(R)] = ∫_R λ dV4
def IsIntensity (N : Set M → Ω → ℝ) (lambda : M → ℝ) (V4 : Measure M) : Prop :=
  ∀ R, MeasurableSet R → (∫ ω, N R ω) = ∫ x in R, lambda x ∂V4

-- The definition of V_xi in terms of average lambda
-- The text says "bar_lambda * V4(R) = V4(R)/V_xi", so bar_lambda = 1/V_xi.
-- We can define V_xi as 1/bar_lambda if bar_lambda is constant, or just state the scaling.
-- The text says "V_xi is the correlation 4-volume ... and V_xi ~ xi^4".
-- It treats V_xi as a parameter.

omit [IsProbabilityMeasure (volume : Measure Ω)] in
theorem J1_RegionalCount_Scaling
  (h_intensity : IsIntensity N lambda V4)
  (h_const_lambda : ∀ x, lambda x = 1 / V_xi)
  (R : Set M) (hR : MeasurableSet R)
  (_hV4_finite : V4 R ≠ ⊤) :
  ExpectedCount N R = (V4 R).toReal / V_xi := by
  unfold IsIntensity at h_intensity; aesop

/-
J.2 CLT Scaling: For regions L >> ξ, Var[N(R)] = α_N · E[N(R)], hence δN ~ √N.
-/
open MeasureTheory ProbabilityTheory


-- We continue with the context from J.1
variable {M : Type*} [MeasurableSpace M] (V4 : Measure M)
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
variable (N : Set M → Ω → ℝ)

-- J.2: CLT Scaling
-- "For regions L >> ξ (finite-range mixing), Var[N(R)] = α_N · E[N(R)]"
-- We introduce alpha_N as a parameter.
variable (alpha_N : ℝ)

-- We define the variance of the regional count
-- We use the `variance` definition from Mathlib (which is `(evariance X).toReal`)
-- But we need to make sure N(R) is a random variable (measurable).
-- We assume N(R) is measurable for all measurable R.
variable (h_N_measurable : ∀ R, MeasurableSet R → Measurable (N R))

-- The CLT scaling relation
-- We state it as an asymptotic relation or just an equality for "large regions" as per the text.
-- The text says "yields central-limit scaling ... Var[N(R)] = alpha_N * E[N(R)]".
-- We will state it as an equality for the purpose of the derivation, or perhaps as a property of the process.

def HasCLTScaling (N : Set M → Ω → ℝ) (alpha_N : ℝ) : Prop :=
  ∀ R, MeasurableSet R → variance (N R) volume = alpha_N * (∫ ω, N R ω)

-- J.2 Claim: δN ~ √N
-- This follows immediately from the variance scaling.
-- δN is defined as sqrt(Var[N(R)]).
-- We prove that if the scaling holds, then δN = sqrt(alpha_N) * sqrt(E[N(R)]).

omit [IsProbabilityMeasure (volume : Measure Ω)] in
theorem J2_CLT_Scaling
  (h_scaling : HasCLTScaling N alpha_N)
  (R : Set M) (hR : MeasurableSet R)
  (h_alpha_pos : 0 ≤ alpha_N) :
  Real.sqrt (variance (N R) volume) = Real.sqrt alpha_N * Real.sqrt (∫ ω, N R ω) := by
    have := @h_scaling;
    unfold HasCLTScaling at this; aesop;

/-
J.3-J.4 Shot Noise to Λ: Propagating fluctuations yields δΛ_typ ~ 1/√V₄.
-/
open MeasureTheory ProbabilityTheory


-- Context
variable {M : Type*} [MeasurableSpace M] (V4 : Measure M)
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

-- Constants
variable (G : ℝ) -- Newton's constant
variable (xi : ℝ) -- Correlation length
variable (sigma_Lambda : ℝ) -- Variance of action per cell

-- Regional count N(R)
variable (N : Set M → Ω → ℝ)

-- Action fluctuation S_Lambda(R)
variable (S_Lambda : Set M → Ω → ℝ)

-- J.3: Definition of Lambda_eff
-- Lambda_eff = - (8 * pi * G / V4(R)) * S_Lambda(R)
def Lambda_eff (R : Set M) (ω : Ω) : ℝ :=
  - (8 * Real.pi * G / (V4 R).toReal) * S_Lambda R ω

-- Assumption: Variance of S_Lambda scales with N(R)
-- Var[S_Lambda(R)] = sigma_Lambda^2 * E[N(R)]
-- (Assuming mean 0 for S_Lambda, or just variance scaling)
def HasActionScaling (S_Lambda : Set M → Ω → ℝ) (N : Set M → Ω → ℝ) (sigma_Lambda : ℝ) : Prop :=
  ∀ R, MeasurableSet R → variance (S_Lambda R) volume = sigma_Lambda^2 * (∫ ω, N R ω)

-- Assumption: N(R) scales with V4(R) / xi^4 (from J.1)
-- E[N(R)] = V4(R) / xi^4
def HasVolumeScaling (N : Set M → Ω → ℝ) (V4 : Measure M) (xi : ℝ) : Prop :=
  ∀ R, MeasurableSet R → (∫ ω, N R ω) = (V4 R).toReal / xi^4

-- J.4: Shot Noise to Lambda
-- Claim: delta_Lambda_typ ~ 1 / sqrt(V4)
-- delta_Lambda_typ = sqrt(Var[Lambda_eff])
-- We prove: sqrt(Var[Lambda_eff]) = (8 * pi * G * sigma_Lambda / xi^2) * (1 / sqrt(V4))

omit [IsProbabilityMeasure (volume : Measure Ω)] in
theorem J4_Lambda_Fluctuation_Scaling
  (h_action_scaling : HasActionScaling S_Lambda N sigma_Lambda)
  (h_vol_scaling : HasVolumeScaling N V4 xi)
  (R : Set M) (hR : MeasurableSet R)
  (h_V4_pos : 0 < (V4 R).toReal)
  (h_xi_pos : 0 < xi)
  (h_sigma_pos : 0 ≤ sigma_Lambda)
  (h_G_pos : 0 ≤ G) :
  Real.sqrt (variance (Lambda_eff V4 G S_Lambda R) volume) =
  (8 * Real.pi * G * sigma_Lambda / xi^2) * (1 / Real.sqrt ((V4 R).toReal)) := by
  -- Apply the variance formula for scaling
  have h_var : variance (Lambda_eff V4 G S_Lambda R) ℙ = (8 * Real.pi * G) ^ 2 * variance (S_Lambda R) ℙ / ((V4 R).toReal) ^ 2 := by
    unfold Lambda_eff;
    rw [ ProbabilityTheory.variance_const_mul ];
    ring_nf;
  rw [ h_var, h_action_scaling ];
  · rw [ h_vol_scaling R hR, Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> try positivity;
    -- Simplify the expression using algebraic manipulation.
    field_simp
    ring_nf;
    rw [ Real.sq_sqrt h_V4_pos.le ];
  · exact hR

/-
J.4b Numerical Payoff: δΛ ~ H² when V₄ ~ H⁻⁴.
For a Hubble-scale coarse-graining window, V₄ ~ H⁻⁴, hence 1/√V₄ ~ H².
This is not fitting: ξ ≃ L_P is fixed internally, H is set by cosmology.
-/

/-- Hubble-scale payoff: if V₄ = H⁻⁴ then 1/√V₄ = H². -/
theorem J4b_Hubble_Payoff (H : ℝ) (hH : 0 < H) (V4_val : ℝ)
    (hV4 : V4_val = H ^ (-4 : ℤ)) :
    1 / Real.sqrt V4_val = H ^ (2 : ℕ) := by
  have hHnn : 0 ≤ H := hH.le
  rw [hV4, zpow_neg]
  -- Goal: 1 / √(H ^ 4)⁻¹ = H ^ 2
  rw [Real.sqrt_inv (H ^ (4 : ℤ))]
  -- Goal: 1 / (√(H ^ 4))⁻¹ = H ^ 2
  simp only [one_div, inv_inv]
  -- Goal: √(H ^ 4) = H ^ 2
  have h4 : (4 : ℤ) = (4 : ℕ) := rfl
  simp only [h4, zpow_natCast]
  conv_lhs => rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact Real.sqrt_sq (pow_nonneg hHnn 2)

/-- The α_Λ prefactor (O(1) in natural units). -/
def alphaLambda (G xi sigma_Lambda : ℝ) : ℝ :=
  8 * Real.pi * G * sigma_Lambda / xi ^ 2

/-- Combined result: δΛ_typ = α_Λ · H² at Hubble scale. -/
theorem J4c_DeltaLambda_H2 (G xi sigma_Lambda H : ℝ)
    (_hH : 0 < H) (_hxi : 0 < xi) :
    alphaLambda G xi sigma_Lambda * H ^ (2 : ℕ) =
    (8 * Real.pi * G * sigma_Lambda / xi ^ 2) * H ^ (2 : ℕ) := by
  rfl

/-
J.5 Two Channels Theorem: Same eigentime substrate yields Tensor channel δg ~ N^{-1/4} and Scalar channel δΛ ~ N^{-1/2}.
-/
open MeasureTheory ProbabilityTheory


-- Context
variable {M : Type*} [MeasurableSpace M] (V4 : Measure M)
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

-- Regional count N(R)
variable (N : Set M → Ω → ℝ)

-- Tensor fluctuation delta_g(R)
-- We model this as a scalar quantity representing the magnitude of metric fluctuations in region R
variable (delta_g : Set M → ℝ)

-- Scalar fluctuation delta_Lambda(R)
-- We use the one derived/defined previously, or just a variable for the scaling
variable (delta_Lambda : Set M → ℝ)

-- Scaling definitions
def IsTensorScaling (delta_g : Set M → ℝ) (N : Set M → Ω → ℝ) : Prop :=
  ∀ R, MeasurableSet R → ∃ C > 0, delta_g R = C * (∫ ω, N R ω) ^ (-1/4 : ℝ)

def IsScalarScaling (delta_Lambda : Set M → ℝ) (N : Set M → Ω → ℝ) : Prop :=
  ∀ R, MeasurableSet R → ∃ C > 0, delta_Lambda R = C * (∫ ω, N R ω) ^ (-1/2 : ℝ)

-- J.5: Two Channels Theorem
-- "Same eigentime substrate yields: Tensor ~ N^-1/4, Scalar ~ N^-1/2"
-- We state this as the existence of such scalings given the process N.

omit [IsProbabilityMeasure (volume : Measure Ω)] in
theorem J5_TwoChannels
  (h_tensor : IsTensorScaling delta_g N)
  (h_scalar : IsScalarScaling delta_Lambda N)
  (R : Set M) (hR : MeasurableSet R) :
  (∃ C_g > 0, delta_g R = C_g * (∫ ω, N R ω) ^ (-1/4 : ℝ)) ∧
  (∃ C_L > 0, delta_Lambda R = C_L * (∫ ω, N R ω) ^ (-1/2 : ℝ)) := by
  constructor
  · exact h_tensor R hR
  · exact h_scalar R hR