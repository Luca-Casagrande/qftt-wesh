/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-
We have formally verified the WESH conservation law and related identities as requested.
1. **T-neutrality & commutators**: We proved `t_neutrality_commutators`, showing that if $[\hat T(x), \hat Q_{\rm tot}] = 0$, then $[\hat T^2(x), \hat Q_{\rm tot}] = 0$ and $[L_{xy}, \hat Q_{\rm tot}] = 0$.
2. **WESH--Noether (atemporal)**: We proved `wesh_conservation`, confirming that the local and bilocal source terms $S_{\mathrm{loc}}(x)$ and $S_{\mathrm{bi}}(x,y)$ vanish under the T-neutrality condition.
3. **No s-footprint**: We proved `no_s_footprint` using the chain rule, showing that conservation in $s$ implies conservation in $t$.
4. **GKSL identity**: We proved `gksl_identity`, $\Tr(A \mathcal{D}[L] \rho) = \frac{1}{2} \langle L^\dagger [A, L] + [L^\dagger, A] L \rangle$, using helper lemmas for trace cyclicity (`trace_cyclic_3`, `trace_cyclic_4`).
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
Lemma (T-neutrality & commutators). If the time field is T-neutral, $[\hat T(x), \hat Q_{\rm tot}] = 0$ for all $x$, then for any conserved charge $\hat Q_{\rm tot}$: $[\hat T^{2}(x), \hat Q_{\rm tot}] = 0$ and $[L_{xy}, \hat Q_{\rm tot}] = 0$, where $L_{xy} \equiv \hat T^2(x) - \hat T^2(y)$.
-/
theorem t_neutrality_commutators {R : Type*} [Ring R] {X : Type*} (T : X → R) (Q : R)
  (h : ∀ x, Commute (T x) Q) :
  (∀ x, Commute (T x ^ 2) Q) ∧
  (∀ x y, Commute (T x ^ 2 - T y ^ 2) Q) := by
  -- By T-neutrality, we have that $[\hat T(x), \hat Q] = 0$ for all $x$.
  have h_comm : ∀ x, Commute (T x) Q := by
    assumption;
  simp_all +decide [ sq, h_comm _ ]

/-
WESH conservation law: If $[\hat T(x), \hat Q_{\rm tot}] = 0$, then the local and bilocal source terms $S_{\mathrm{loc}}(x)$ and $S_{\mathrm{bi}}(x,y)$ vanish.
-/
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {X : Type*}
variable (T : X → R) (Q : R)

def L_op (x y : X) : R := T x ^ 2 - T y ^ 2

def S_loc_op (x : X) : R :=
  (1/2 : ℂ) • (T x ^ 2 * (Q * T x ^ 2 - T x ^ 2 * Q) + (T x ^ 2 * Q - Q * T x ^ 2) * T x ^ 2)

def S_bi_op (x y : X) : R :=
  (1/2 : ℂ) • (L_op T x y * (Q * L_op T x y - L_op T x y * Q) + (L_op T x y * Q - Q * L_op T x y) * L_op T x y)

theorem wesh_conservation (h : ∀ x, Commute (T x) Q) :
  (∀ x, S_loc_op T Q x = 0) ∧ (∀ x y, S_bi_op T Q x y = 0) := by
  -- By T-neutrality (C.1), $[\hat T^2(x),\hat Q_{\rm tot}]=0$ and $[L_{xy},\hat Q_{\rm tot}]=0$.
  have h_neutral : ∀ x, Commute (T x ^ 2) Q ∧ ∀ x y, Commute (T x ^ 2 - T y ^ 2) Q := by
    aesop;
  simp_all +decide [ Commute ];
  simp_all +decide [ SemiconjBy, S_loc_op, S_bi_op ];
  simp_all +decide [ sub_mul, mul_sub, L_op ]

/-
No s-footprint in observables: If the expectation value is conserved with respect to $s$, it is conserved with respect to $t$, by the chain rule.
-/
variable (Q_s : ℝ → ℝ) (s_t : ℝ → ℝ)
variable (t : ℝ)

theorem no_s_footprint
  (hQ : DifferentiableAt ℝ Q_s (s_t t))
  (hs : DifferentiableAt ℝ s_t t)
  (h_conserved : deriv Q_s (s_t t) = 0) :
  deriv (Q_s ∘ s_t) t = 0 := by
  rw [ deriv_comp ] <;> aesop

/-
Definition of the Lindblad dissipator $\mathcal{D}[L]\rho = L \rho L^\dagger - \frac{1}{2} \{L^\dagger L, \rho\}$.
-/
variable {H : Type*} [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H]

def Dissipator (L : H) (ρ : H) : H :=
  L * ρ * star L - (1/2 : ℂ) • (star L * L * ρ + ρ * star L * L)

/-
Cyclicity of trace for 3 operators.
-/
variable {H : Type*} [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H]

omit [StarRing H] [Algebra ℂ H] [StarModule ℂ H] in
lemma trace_cyclic_3 (Trace : H → ℂ) (h_cyclic : ∀ (a b : H), Trace (a * b) = Trace (b * a)) (a b c : H) :
  Trace (a * b * c) = Trace (c * a * b) := by
  grind

/-
Cyclicity of trace for 4 operators.
-/
variable {H : Type*} [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H]

omit [StarRing H] [Algebra ℂ H] [StarModule ℂ H] in
lemma trace_cyclic_4 (Trace : H → ℂ) (h_cyclic : ∀ (a b : H), Trace (a * b) = Trace (b * a)) (a b c d : H) :
  Trace (a * b * c * d) = Trace (d * a * b * c) := by
  grind

/-
GKSL identity: $\Tr(A \mathcal{D}[L] \rho) = \frac{1}{2} \langle L^\dagger [A, L] + [L^\dagger, A] L \rangle$.
-/
variable {H : Type*} [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H]

omit [StarModule ℂ H] in
theorem gksl_identity (Trace : H → ℂ)
  (h_cyclic : ∀ (a b : H), Trace (a * b) = Trace (b * a))
  (h_linear : ∀ (c : ℂ) (a b : H), Trace (c • a + b) = c * Trace a + Trace b)
  (A L ρ : H) :
  Trace (A * Dissipator L ρ) =
  (1/2 : ℂ) * Trace ((star L * (A * L - L * A) + (star L * A - A * star L) * L) * ρ) := by
  have h_expansion : A * Dissipator L ρ = A * L * ρ * star L - (1 / 2 : ℂ) • (A * star L * L * ρ + A * ρ * star L * L) := by
    unfold Dissipator; simp +decide [ mul_assoc, mul_sub ] ;
    simp +decide [ mul_add ];
  simp_all +decide [ mul_assoc, sub_mul, mul_sub, add_mul ];
  have h_trace : ∀ (a b : H), Trace (a - b) = Trace a - Trace b := by
    intro a b; have := h_linear ( -1 ) a b; simp_all +decide [ sub_eq_add_neg ] ;
    have := h_linear ( -1 ) b a; simp_all +decide [ add_comm ] ;
  have h_trace : ∀ (a b : H), Trace (a + b) = Trace a + Trace b := by
    intro a b; specialize h_linear 1 a b; aesop;
  simp_all +decide [ ← mul_assoc, ← h_cyclic ];
  ring

/-
Complete WESH-Noether structure combining all elements of Appendix C.
-/

/-- T-neutrality condition: [T(x), Q] = 0 for all x. -/
def TNeutrality {R : Type*} [Ring R] {X : Type*} (T : X → R) (Q : R) : Prop :=
  ∀ x, Commute (T x) Q

/-- Full commutant conditions derived from T-neutrality. -/
structure CommutantConditions {R : Type*} [Ring R] {X : Type*} (T : X → R) (Q : R) where
  /-- T² commutes with Q -/
  Tsq_comm : ∀ x, Commute (T x ^ 2) Q
  /-- L_xy commutes with Q -/
  Lxy_comm : ∀ x y, Commute (T x ^ 2 - T y ^ 2) Q

/-- Derive commutant conditions from T-neutrality. -/
def CommutantConditions.ofTNeutrality {R : Type*} [Ring R] {X : Type*} 
    (T : X → R) (Q : R) (hTN : TNeutrality T Q) : CommutantConditions T Q :=
  let ⟨h1, h2⟩ := t_neutrality_commutators T Q hTN
  ⟨h1, h2⟩

/-- WESH-Noether conservation: all source terms vanish. -/
structure WESHConservation {R : Type*} [Ring R] [Algebra ℂ R] {X : Type*} 
    (T : X → R) (Q : R) where
  /-- Local source term vanishes -/
  S_loc_zero : ∀ x, S_loc_op T Q x = 0
  /-- Bilocal source term vanishes -/
  S_bi_zero : ∀ x y, S_bi_op T Q x y = 0

/-- Derive WESH conservation from T-neutrality. -/
def WESHConservation.ofTNeutrality {R : Type*} [Ring R] [Algebra ℂ R] {X : Type*}
    (T : X → R) (Q : R) (hTN : TNeutrality T Q) : WESHConservation T Q :=
  let ⟨h1, h2⟩ := wesh_conservation T Q hTN
  ⟨h1, h2⟩

/-- Complete WESH-Noether theorem structure. -/
structure WESHNoetherTheorem {R : Type*} [Ring R] [Algebra ℂ R] {X : Type*} 
    (T : X → R) (Q : R) where
  /-- T-neutrality holds -/
  T_neutral : TNeutrality T Q
  /-- Commutant conditions -/
  commutant : CommutantConditions T Q := CommutantConditions.ofTNeutrality T Q T_neutral
  /-- Conservation (source terms vanish) -/
  conservation : WESHConservation T Q := WESHConservation.ofTNeutrality T Q T_neutral

/-- Master theorem: T-neutrality implies full WESH-Noether conservation. -/
theorem WESHNoether_of_TNeutrality {R : Type*} [Ring R] [Algebra ℂ R] {X : Type*}
    (T : X → R) (Q : R) (hTN : TNeutrality T Q) : WESHNoetherTheorem T Q :=
  { T_neutral := hTN
    commutant := CommutantConditions.ofTNeutrality T Q hTN
    conservation := WESHConservation.ofTNeutrality T Q hTN }

/-
Chain rule formulation: conservation in s implies conservation in t.
This follows directly from no_s_footprint.
-/

/-- Chronogenetic interval: region where Γ > 0. -/
structure ChronogeneticInterval where
  Γ : ℝ
  pos : 0 < Γ

/-- Conservation is preserved under time reparametrization. -/
theorem conservation_reparametrization (Q_s : ℝ → ℝ) (s_t : ℝ → ℝ) (t : ℝ)
    (hQ : DifferentiableAt ℝ Q_s (s_t t))
    (hs : DifferentiableAt ℝ s_t t)
    (h_conserved_s : deriv Q_s (s_t t) = 0) :
    deriv (Q_s ∘ s_t) t = 0 :=
  no_s_footprint Q_s s_t t hQ hs h_conserved_s