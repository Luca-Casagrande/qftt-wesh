/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-
Formalization of Appendix B of the QFTT-WESH paper. This module defines the auxiliary parameter $s$, the time-production functional $\Gamma[\Psi]$, and the emergence of physical time $t$. It includes the definitions of the QFTT context, the gamma kernel, and the survival probability. Key theorems proven include the positivity of $\Gamma$ under non-degeneracy (Lemma B.1), the activation of Eigentime events on chronogenetic segments (Lemma B.2), and the algebraic limit of the Law of Large Numbers relating physical time to Eigentime counts.
-/

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
Definition of the Heaviside step function and the gamma kernel in QFTT-WESH. The kernel is given by $\gamma(x,y)=\frac{\gamma_0}{N^2}\,e^{-d(x,y)/\xi}\,\Theta[\mathrm{causal}(x,y)]$.
-/
noncomputable def Heaviside (x : Real) : Real := if x >= 0 then 1 else 0

structure QFTT_Parameters where
  gamma_0 : Real
  N : Real
  xi : Real
  d : (x y : ℝ × ℝ × ℝ × ℝ) → Real -- Assuming 4D spacetime points
  causal : (x y : ℝ × ℝ × ℝ × ℝ) → Real -- Causal separation or indicator

noncomputable def gamma_kernel (params : QFTT_Parameters) (x y : ℝ × ℝ × ℝ × ℝ) : Real :=
  (params.gamma_0 / params.N^2) * Real.exp (- (params.d x y) / params.xi) * Heaviside (params.causal x y)

/-
Definitions of the QFTT context, the time-production functional $\Gamma[\Psi]$, the physical time evolution condition, and the Eigentime count $N_{\rm Eig}$.
-/
open Real ContinuousLinearMap Filter Topology MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure QFTT_Context (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  tau_Eig : ℝ
  nu : ℝ
  gamma_0 : ℝ
  N : ℝ
  xi : ℝ
  d : (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) → ℝ
  causal : (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) → ℝ
  integral_x : ((ℝ × ℝ × ℝ × ℝ) → ℝ) → ℝ
  integral_xy : ((ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) → ℝ) → ℝ
  T_tilde : (ℝ × ℝ × ℝ × ℝ) → (H →L[ℂ] H)
  L : (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) → (H →L[ℂ] H)
  Tr : (H →L[ℂ] H) → ℝ
  C : (H →L[ℂ] H) → (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) → ℝ

noncomputable def Gamma_functional (ctx : QFTT_Context H) (rho : H →L[ℂ] H) : ℝ :=
  ctx.tau_Eig * (
    ctx.nu * ctx.integral_x (fun x => ctx.Tr ((ctx.T_tilde x) ^ 2 * rho * (ctx.T_tilde x) ^ 2)) +
    ctx.integral_xy (fun x y =>
      (ctx.gamma_0 / ctx.N^2) * Real.exp (- (ctx.d x y) / ctx.xi) * Heaviside (ctx.causal x y) *
      ctx.C rho x y *
      ctx.Tr ((ctx.L x y).adjoint * (ctx.L x y) * rho)
    )
  )

def physical_time_evolution (ctx : QFTT_Context H) (rho : ℝ → (H →L[ℂ] H)) (t : ℝ → ℝ) : Prop :=
  ∀ s, deriv t s = Gamma_functional ctx (rho s)

noncomputable def N_Eig (ctx : QFTT_Context H) (rho : ℝ → (H →L[ℂ] H)) (M : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ u in Set.Icc 0 s, Gamma_functional ctx (rho u) / ctx.tau_Eig) + M s

/-
Helper lemma: if $f(s) \to 0$ as $s \to \infty$, then $1/(1+f(s)) \to 1$.
-/
lemma limit_inv_one_plus_zero {f : ℝ → ℝ} (hf : Tendsto f atTop (nhds 0)) :
  Tendsto (fun s => 1 / (1 + f s)) atTop (nhds 1) := by
    simpa using Filter.Tendsto.inv₀ ( hf.const_add 1 ) ( by norm_num )

/-
Algebraic version of the Law of Large Numbers: if $M(s)/t(s) \to 0$ and $t(s) \to \infty$, then $t(s) / (\tau_{\rm Eig} N_{\rm Eig}(s)) \to 1$.
-/
theorem LLN_algebraic_limit (ctx : QFTT_Context H) (rho : ℝ → (H →L[ℂ] H)) (M : ℝ → ℝ) (t : ℝ → ℝ)
  (_h_t_def : ∀ s, t s = ∫ u in Set.Icc 0 s, Gamma_functional ctx (rho u))
  (h_N_def : ∀ s, N_Eig ctx rho M s = (t s / ctx.tau_Eig) + M s)
  (h_M_negligible : Tendsto (fun s => M s / t s) atTop (nhds 0))
  (h_t_large : Tendsto t atTop atTop)
  (h_tau_ne_zero : ctx.tau_Eig ≠ 0) :
  Tendsto (fun s => t s / (ctx.tau_Eig * N_Eig ctx rho M s)) atTop (nhds 1) := by
    -- Simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun s => 1 / (1 + ctx.tau_Eig * M s / t s)) Filter.atTop (𝓝 1) by
      refine' h_simplify.congr' _;
      filter_upwards [ h_t_large.eventually_gt_atTop 0 ] with s hs;
      grind;
    simpa [ mul_div_assoc ] using Filter.Tendsto.inv₀ ( h_M_negligible.const_mul ctx.tau_Eig |> Filter.Tendsto.const_add 1 ) ( by simp +decide )

/-
Under the non-degeneracy condition (ND), the time-production functional $\Gamma[\Psi]$ is strictly positive, ensuring a strictly increasing physical time $t(s)$.
-/
def NonDegenerate (ctx : QFTT_Context H) (rho : H →L[ℂ] H) : Prop :=
  ctx.nu > 0 ∧ ctx.integral_x (fun x => ctx.Tr ((ctx.T_tilde x) ^ 2 * rho * (ctx.T_tilde x) ^ 2)) > 0

theorem Gamma_positive (ctx : QFTT_Context H) (rho : H →L[ℂ] H)
  (h_nd : NonDegenerate ctx rho)
  (h_tau : ctx.tau_Eig > 0)
  (h_gamma_nonneg : ∀ x y, (ctx.gamma_0 / ctx.N^2) * Real.exp (- (ctx.d x y) / ctx.xi) * Heaviside (ctx.causal x y) * ctx.C rho x y * ctx.Tr ((ctx.L x y).adjoint * (ctx.L x y) * rho) ≥ 0)
  (h_int_nonneg : ∀ f, (∀ x y, f x y ≥ 0) → ctx.integral_xy f ≥ 0) :
  Gamma_functional ctx rho > 0 := by
    exact mul_pos h_tau ( add_pos_of_pos_of_nonneg ( mul_pos h_nd.1 h_nd.2 ) ( h_int_nonneg _ h_gamma_nonneg ) )

/-
Helper lemma: The integral of a continuous function that is strictly positive on an interval $(a, b]$ with $a < b$ is strictly positive.
-/
lemma integral_pos_of_pos_on_interval {f : ℝ → ℝ} {a b : ℝ} (h_lt : a < b)
  (h_cont : ContinuousOn f (Set.Icc a b))
  (h_pos : ∀ x ∈ Set.Ioc a b, f x > 0) :
  ∫ x in Set.Ioc a b, f x > 0 := by
    field_simp;
    rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
    · simp +decide [ Function.support ];
      exact lt_of_lt_of_le ( by aesop ) ( MeasureTheory.measure_mono ( show { x : ℝ | ¬f x = 0 } ∩ Set.Ioc a b ⊇ Set.Ioc a b from fun x hx => ⟨ ne_of_gt ( h_pos x hx ), hx ⟩ ) );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using le_of_lt ( h_pos x hx );
    · exact h_cont.integrableOn_Icc.mono_set <| Set.Ioc_subset_Icc_self

/-
Helper lemma: if $\int f > 0$, then $e^{-\int f} < 1$.
-/
lemma exp_neg_integral_lt_one {f : ℝ → ℝ} {s : Set ℝ} (h_int_pos : ∫ x in s, f x > 0) :
  Real.exp (- ∫ x in s, f x) < 1 := by
    aesop

/-
Definition of the survival probability $S_{s_0}(\delta) = \exp(-\int_{s_0}^{s_0+\delta} \Gamma[\rho(s)] ds)$.
-/
noncomputable def SurvivalProbability (ctx : QFTT_Context H) (rho : ℝ → (H →L[ℂ] H)) (s0 delta : ℝ) : ℝ :=
  Real.exp (- ∫ s in Set.Ioc s0 (s0 + delta), Gamma_functional ctx (rho s))

/-
On a chronogenetic segment (where $\Gamma > 0$), the survival probability is strictly less than 1. Proof uses helper lemmas: integral of positive function is positive, and $e^{-x} < 1$ for $x > 0$.
-/
theorem Eigentime_activation (ctx : QFTT_Context H) (rho : ℝ → (H →L[ℂ] H)) (s0 delta : ℝ)
  (h_delta : delta > 0)
  (h_cont : ContinuousOn (fun s => Gamma_functional ctx (rho s)) (Set.Icc s0 (s0 + delta)))
  (h_chronogenetic : ∀ s ∈ Set.Ioc s0 (s0 + delta), Gamma_functional ctx (rho s) > 0) :
  SurvivalProbability ctx rho s0 delta < 1 := by
    unfold SurvivalProbability
    have h_int_pos : ∫ s in Set.Ioc s0 (s0 + delta), Gamma_functional ctx (rho s) > 0 := by
      apply integral_pos_of_pos_on_interval
      · linarith
      · exact h_cont
      · exact h_chronogenetic
    apply exp_neg_integral_lt_one h_int_pos

/-
Framework comparison table (B.3): QFTT-WESH vs other approaches to the problem of time.
-/

/-- Treatment of time in various frameworks. -/
inductive TimeStatus
  | Relational   -- Page-Wootters: static, no flow
  | External     -- GRW/CSL, Penrose: external parameter
  | Emergent     -- QFTT-WESH: emerges from dynamics

/-- Arrow of time status. -/
inductive ArrowStatus
  | Absent   -- Page-Wootters
  | Assumed  -- GRW/CSL, Penrose
  | Intrinsic -- QFTT-WESH: each eigentime orients

/-- Framework comparison structure. -/
structure Framework where
  name : String
  timeStatus : TimeStatus
  arrowStatus : ArrowStatus

def PageWootters : Framework := ⟨"Page-Wootters", .Relational, .Absent⟩
def GRW_CSL : Framework := ⟨"GRW/CSL", .External, .Assumed⟩
def PenroseOR : Framework := ⟨"Penrose OR", .External, .Assumed⟩
def QFTT_WESH_Framework : Framework := ⟨"QFTT-WESH", .Emergent, .Intrinsic⟩

/-
B.4: The auxiliary parameter s leaves no footprint in observables.
Emergent observables are DEFINED as functions of physical time t,
so s-independence is by construction.
-/

/-- An emergent observable is defined as a function of physical time t.
    s-independence is BY CONSTRUCTION: O(s) = f(t(s)). -/
structure EmergentObservable where
  f : ℝ → ℝ

/-- Evaluate an emergent observable. -/
def EmergentObservable.eval (O : EmergentObservable) (t : ℝ → ℝ) (s : ℝ) : ℝ :=
  O.f (t s)

/-- s-independence is automatic: the observable only sees t(s), not s directly. -/
theorem EmergentObservable.s_independent (O : EmergentObservable) (t : ℝ → ℝ) :
    ∃ f : ℝ → ℝ, ∀ s, O.eval t s = f (t s) :=
  ⟨O.f, fun _ => rfl⟩