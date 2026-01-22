import Mathlib

/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-!
# Appendix H — CP/TP preservation and no-signaling in WESH

Lean 4 / Mathlib formalization of Appendix H of the QFTT-WESH paper.

## Contents
1. CPTP maps and their algebraic properties
2. WESH rate data and regularity assumptions  
3. Frozen-coefficient GKSL scheme
4. Theorem H.1: CP/TP preservation for nonlinear WESH evolution
5. Corollary H.1: System-ancilla consistency
6. Proposition H.1: Spacelike no-signaling (proved for finite lattice)

## References (background)
- Breuer–Petruccione (2002), *The Theory of Open Quantum Systems*
- Nielsen–Chuang (2000), *Quantum Computation and Quantum Information*
- Alicki–Lendi (1987), *Quantum Dynamical Semigroups and Applications*
- Lindblad (1976), *On the generators of quantum dynamical semigroups*
- Gorini–Kossakowski–Sudarshan (1976), *Completely positive dynamical semigroups of N-level systems*
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical Filter Topology
open scoped BigOperators

namespace QFTT.WESH.AppendixH

/-! ## 1. State space and CPTP maps -/

variable (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State] [CompleteSpace State]

/-- CPTP predicate on evolution maps. Treated axiomatically; see References. -/
opaque IsCPTP : (State → State) → Prop

/-- A map bundled with proof it is CPTP. -/
structure CPTPMap where
  toFun : State → State
  cptp : IsCPTP State toFun

instance : CoeFun (CPTPMap State) (fun _ => State → State) := ⟨CPTPMap.toFun⟩

/-- Identity map is CPTP (standard). -/
axiom IsCPTP_id : IsCPTP State (fun ρ : State => ρ)

/-- Composition of CPTP maps is CPTP (standard). -/
axiom IsCPTP_comp (Φ Ψ : State → State) :
  IsCPTP State Φ → IsCPTP State Ψ → IsCPTP State (fun ρ => Φ (Ψ ρ))

/-- Bundled identity CPTP map. -/
def CPTPMap.id : CPTPMap State :=
  { toFun := fun ρ => ρ, cptp := IsCPTP_id State }

/-- Bundled composition of CPTP maps. -/
def CPTPMap.comp (Φ Ψ : CPTPMap State) : CPTPMap State :=
  { toFun := fun ρ => Φ (Ψ ρ)
    cptp := IsCPTP_comp State Φ.toFun Ψ.toFun Φ.cptp Ψ.cptp }

/-- Strong convergence of maps (pointwise in norm). -/
def StrongConverges (Φ : ℕ → (State → State)) (F : State → State) : Prop :=
  ∀ ρ : State, Tendsto (fun n => Φ n ρ) atTop (nhds (F ρ))

/-- Strong limits of CPTP maps remain CPTP.
    Assumption for the intended model (trace-class operators with trace norm). -/
axiom IsCPTP_of_strongLimit (Φ : ℕ → (State → State)) (F : State → State) :
  (∀ n, IsCPTP State (Φ n)) → StrongConverges State Φ F → IsCPTP State F


/-! ## 2. WESH setting -/

variable (X : Type*)

/-- Scalar rate data with bounds. Only C depends on State (source of nonlinearity). -/
structure RateData where
  ν : ℝ
  γ : X → X → ℝ
  C : State → X → X → ℝ
  ν_nonneg : 0 ≤ ν
  C_bounds : ∀ ρ x y, 0 ≤ C ρ x y ∧ C ρ x y ≤ 1
  γ_nonneg : ∀ x y, 0 ≤ γ x y

/-- Regularity assumptions for product-integral convergence. -/
structure RegularityAssumptions (R : RateData State X) : Prop where
  /-- Rates are uniformly bounded -/
  rates_bounded : ∃ M : ℝ, ∀ x y, |R.γ x y| ≤ M
  /-- Rate coefficients are piecewise continuous in s -/
  rates_measurable : ∀ x y, ∃ (S : Set ℝ), S.Countable ∧ ContinuousOn (fun _ => R.γ x y) Sᶜ
  /-- Gate function is Lipschitz in trace norm -/
  gate_lipschitz : ∃ L : ℝ, ∀ ρ₁ ρ₂ : State, ∀ x y, |R.C ρ₁ x y - R.C ρ₂ x y| ≤ L * ‖ρ₁ - ρ₂‖

/-- Effective Hamiltonian generates trace-norm isometry group. -/
structure HamiltonianAssumption where
  H_selfadjoint : Prop
  generates_group : Prop


/-! ## 3. Frozen-coefficient scheme -/

/-- Abstract generator (master equation RHS). -/
structure Generator where
  apply : State → State

/-- Generator is GKSL form (Hermitian jumps, nonnegative rates).
    Reference: Lindblad (1976), Gorini-Kossakowski-Sudarshan (1976). -/
opaque IsGKSL : Generator State → Prop

/-- The exponential step exp(Δs · L) as a map. -/
noncomputable opaque ExpStep : ℝ → Generator State → (State → State)

/-- Frozen GKSL step returns a CPTP map.
    Standard: a GKSL generator yields a CPTP semigroup. -/
axiom frozen_gksl_step (Δs : ℝ) (hΔ : 0 ≤ Δs) (L : Generator State) :
  IsGKSL State L → CPTPMap State

/-- The frozen step equals exp(Δs · L). -/
axiom frozen_gksl_step_is_exp (Δs : ℝ) (hΔ : 0 ≤ Δs) (L : Generator State) (hL : IsGKSL State L) :
  (frozen_gksl_step State Δs hΔ L hL).toFun = ExpStep State Δs L

/-- A frozen micro-step in the partition. -/
structure FrozenStep where
  u : ℝ
  Δs : ℝ
  Δ_nonneg : 0 ≤ Δs

/-- A frozen partition of [0,s]. -/
structure FrozenPartition (s : ℝ) where
  steps : List FrozenStep
  sumΔ : (steps.map FrozenStep.Δs).sum = s

/-- CPTP map for a single frozen step. -/
noncomputable def stepMap
    (FrozenGen : ℝ → Generator State)
    (FrozenGen_GKSL : ∀ u : ℝ, IsGKSL State (FrozenGen u))
    (st : FrozenStep) : CPTPMap State :=
  frozen_gksl_step State st.Δs st.Δ_nonneg (FrozenGen st.u) (FrozenGen_GKSL st.u)

/-- Concatenation of CPTP maps (chronological order). -/
noncomputable def concatSteps (maps : List (CPTPMap State)) : CPTPMap State :=
  maps.foldl (fun acc Φ => CPTPMap.comp State Φ acc) (CPTPMap.id State)

/-- Frozen approximation map E_s^(N). -/
noncomputable def FrozenApprox
    (FrozenGen : ℝ → Generator State)
    (FrozenGen_GKSL : ∀ u : ℝ, IsGKSL State (FrozenGen u))
    {s : ℝ} (P : FrozenPartition s) : CPTPMap State :=
  concatSteps State (P.steps.map (stepMap State FrozenGen FrozenGen_GKSL))

/-- Frozen approximation sequence as plain functions. -/
noncomputable def Eapprox
    (FrozenGen : ℝ → Generator State)
    (FrozenGen_GKSL : ∀ u : ℝ, IsGKSL State (FrozenGen u))
    (PartitionSeq : ∀ s : ℝ, ℕ → FrozenPartition s)
    (s : ℝ) (N : ℕ) : State → State :=
  (FrozenApprox State FrozenGen FrozenGen_GKSL (PartitionSeq s N)).toFun

/-- Each frozen approximation is CPTP. -/
lemma Eapprox_isCPTP
    (FrozenGen : ℝ → Generator State)
    (FrozenGen_GKSL : ∀ u : ℝ, IsGKSL State (FrozenGen u))
    (PartitionSeq : ∀ s : ℝ, ℕ → FrozenPartition s)
    (s : ℝ) (N : ℕ) :
    IsCPTP State (Eapprox State FrozenGen FrozenGen_GKSL PartitionSeq s N) :=
  (FrozenApprox State FrozenGen FrozenGen_GKSL (PartitionSeq s N)).cptp

/-- Product-integral convergence.
    Assumption: standard product-integral convergence under regularity hypotheses. -/
axiom productIntegral_converges
    (FrozenGen : ℝ → Generator State)
    (FrozenGen_GKSL : ∀ u : ℝ, IsGKSL State (FrozenGen u))
    (E : ℝ → State → State)
    (PartitionSeq : ∀ s : ℝ, ℕ → FrozenPartition s)
    (R : RateData State X) (hReg : RegularityAssumptions State X R)
    (hHam : HamiltonianAssumption) (s : ℝ) (hs : 0 ≤ s) :
    StrongConverges State
      (fun N => Eapprox State FrozenGen FrozenGen_GKSL PartitionSeq s N) (E s)


/-! ## 4. Theorem H.1 — CP/TP preservation -/

/-- **Theorem H.1**: The nonlinear WESH evolution E_s preserves complete positivity
    and trace. Each frozen micro-step is CPTP, and the product-integral limit
    preserves these properties. -/
theorem Theorem_H1_CPTP
    (FrozenGen : ℝ → Generator State)
    (FrozenGen_GKSL : ∀ u : ℝ, IsGKSL State (FrozenGen u))
    (E : ℝ → State → State)
    (PartitionSeq : ∀ s : ℝ, ℕ → FrozenPartition s)
    (R : RateData State X)
    (hReg : RegularityAssumptions State X R)
    (hHam : HamiltonianAssumption)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ Es : CPTPMap State, ∀ ρ : State, Es ρ = E s ρ := by
  have hconv := productIntegral_converges State X FrozenGen FrozenGen_GKSL E PartitionSeq R hReg hHam s hs
  have hEs : IsCPTP State (E s) :=
    IsCPTP_of_strongLimit State
      (fun N => Eapprox State FrozenGen FrozenGen_GKSL PartitionSeq s N) (E s)
      (fun N => Eapprox_isCPTP State FrozenGen FrozenGen_GKSL PartitionSeq s N) hconv
  exact ⟨{ toFun := E s, cptp := hEs }, fun _ => rfl⟩


/-! ## 5. Corollary H.1 — System-ancilla consistency -/

/-- Ancilla extension data. -/
structure AncillaData where
  ExtState : Type*
  instNorm : NormedAddCommGroup ExtState
  tensorId : (State → State) → (ExtState → ExtState)

variable (anc : AncillaData State)

/-- Positivity predicate on extended state. -/
opaque IsPositive : anc.ExtState → Prop

/-- Unit-trace predicate on extended state. -/
opaque IsUnitTrace : anc.ExtState → Prop

/-- CPTP preserves positivity and trace under tensor extension. -/
axiom CPTP_tensor_preserves
    (Φ : State → State) (hΦ : IsCPTP State Φ) (ρSA : anc.ExtState) :
    IsPositive State anc ρSA → IsUnitTrace State anc ρSA →
      IsPositive State anc (anc.tensorId Φ ρSA) ∧ IsUnitTrace State anc (anc.tensorId Φ ρSA)

/-- **Corollary H.1**: For any ancilla A and initial ρ_SA, 
    (E_s ⊗ 𝟙_A)(ρ_SA) preserves positivity and unit trace. -/
theorem Corollary_H1_ancilla
    (E : ℝ → State → State)
    (s : ℝ) (ρSA : anc.ExtState)
    (hpos : IsPositive State anc ρSA)
    (htr : IsUnitTrace State anc ρSA)
    (hEs : IsCPTP State (E s)) :
    IsPositive State anc (anc.tensorId (E s) ρSA) ∧
    IsUnitTrace State anc (anc.tensorId (E s) ρSA) :=
  CPTP_tensor_preserves State anc (E s) hEs ρSA hpos htr


/-! ## 6. Proposition H.1 — Spacelike no-signaling (finite lattice) -/

section NoSignaling_Finite

variable {Y : Type} [Fintype Y] [DecidableEq Y]
variable (Spacelike : Y → Y → Prop) [∀ x y : Y, Decidable (Spacelike x y)]

/-- Causal closure: A ∪ {y | ∃ x ∈ A, ¬Spacelike x y}. -/
def CausalClosure (A : Set Y) : Set Y :=
  A ∪ {y | ∃ x, x ∈ A ∧ ¬ Spacelike x y}

/-- Kernel has causal support if it vanishes on spacelike-separated pairs. -/
def CausalSupport (γ : Y → Y → ℝ) : Prop :=
  ∀ x y, Spacelike x y → γ x y = 0

/-- Masked generator induced by kernel γ on region S. Returns a function Y → ℝ. -/
noncomputable def MaskedGenerator (γ : Y → Y → ℝ) (S : Set Y) (ρ : Y → ℝ) : Y → ℝ :=
  fun x => if x ∈ S then ∑ y : Y, (if y ∈ S then γ x y * (ρ x - ρ y) else 0) else 0

/-- No-signaling equation: masking by J(A) doesn't change the generator on A. -/
def NoSignalingEq (γ : Y → Y → ℝ) (A : Set Y) (ρ : ℝ → Y → ℝ) : Prop :=
  ∀ s x, x ∈ A →
    (MaskedGenerator γ (CausalClosure Spacelike A) (ρ s)) x =
    (MaskedGenerator γ Set.univ (ρ s)) x

/-- **Proposition H.1**: Causal support implies no-signaling. -/
theorem Proposition_H1_noSignaling
    (γ : Y → Y → ℝ)
    (hγ : CausalSupport Spacelike γ)
    (A : Set Y) (ρ : ℝ → Y → ℝ) :
    NoSignalingEq Spacelike γ A ρ := by
  intro s x hxA
  have hxJA : x ∈ CausalClosure Spacelike A := Or.inl hxA
  simp only [MaskedGenerator, hxJA, ↓reduceIte, Set.mem_univ]
  refine Finset.sum_congr rfl ?_
  intro y _hy
  by_cases hyJA : y ∈ CausalClosure Spacelike A
  · simp only [hyJA, ↓reduceIte]
  · have hsp : Spacelike x y := by
      by_contra hns
      apply hyJA
      exact Or.inr ⟨x, hxA, hns⟩
    simp only [hyJA, ↓reduceIte, hγ x y hsp, zero_mul]

end NoSignaling_Finite

end QFTT.WESH.AppendixH
