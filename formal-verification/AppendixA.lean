import Mathlib

/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-!
# Appendix A (QFTT-WESH): Kernel derivation and scales ξ, γ₀

Lean 4 / Mathlib formalization of Appendix A.

## Scope
- 4D Minkowski space with signature η = diag(-,+,+,+)
- Causal envelope kernel K_ξ with L¹ integrability
- **Proved:** V_ξ = 8πξ⁴ (correlation four-volume)
- **Proved:** ∫K̄_ξ = 1 (normalization)
- Collapse kernel γ(x,y) with N⁻² collective scaling
- ν-matching as self-consistency constraint
- Planck anchoring

## Axiom policy
- Retarded propagator existence: standard QFT, out of scope
- Gate bounds C ∈ [0,1]: proved in WESH formalism, out of scope here
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise
open MeasureTheory

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

set_option autoImplicit false

noncomputable section

namespace QFTT.WESH.AppendixA

/-! ## Minkowski space structure -/

/-- 4D Minkowski label space (pre-chronogenesis sector). -/
def Point := Fin 4 → ℝ

/-- Minkowski metric η = diag(-1,+1,+1,+1). -/
def eta (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then -1 else 1) else 0

/-- Minkowski inner product. -/
def minkowski_dot (x y : Point) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, eta i j * x i * y j

/-- Minkowski squared norm z² = -z₀² + z₁² + z₂² + z₃². -/
def minkowski_sq (x : Point) : ℝ := minkowski_dot x x

/-- Heaviside step function Θ(x). -/
noncomputable def Heaviside (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

lemma Heaviside_nonneg (x : ℝ) : 0 ≤ Heaviside x := by
  unfold Heaviside; split_ifs <;> norm_num

lemma Heaviside_le_one (x : ℝ) : Heaviside x ≤ 1 := by
  unfold Heaviside; split_ifs <;> norm_num

/-- Vector subtraction in Minkowski space. -/
instance : Sub Point where
  sub x y := fun i => x i - y i

/-- MeasurableSpace instance for Point. -/
instance : MeasurableSpace Point := by unfold Point; infer_instance

/-- MeasureSpace instance for Point. -/
instance : MeasureSpace Point := by unfold Point; infer_instance

/-! ## Physical parameters -/

/-- Fundamental physical constants with positivity proofs. -/
structure PhysicsParameters where
  hbar : ℝ          -- reduced Planck constant
  c : ℝ             -- speed of light
  mT : ℝ            -- mediator mass
  hbar_pos : 0 < hbar
  c_pos : 0 < c
  mT_pos : 0 < mT

/-- Compton correlation length ξ = ℏ/(m_T c). -/
def PhysicsParameters.xi (p : PhysicsParameters) : ℝ :=
  p.hbar / (p.mT * p.c)

lemma PhysicsParameters.xi_pos (p : PhysicsParameters) : 0 < p.xi := by
  unfold PhysicsParameters.xi
  exact div_pos p.hbar_pos (mul_pos p.mT_pos p.c_pos)

/-- Relation ξ = ℏ/(m_T c) (Eq. A.3). -/
def xi_relation (xi m_T hbar c : ℝ) : Prop := xi = hbar / (m_T * c)

/-! ## A.2: Causal envelope kernel K_ξ -/

/-- Causal envelope kernel K_ξ(z) = exp(-z⁰/ξ) Θ(z⁰) Θ(-z²) (Eq. A.4). -/
noncomputable def K_xi (xi : ℝ) (z : Point) : ℝ :=
  Real.exp (-z 0 / xi) * Heaviside (z 0) * Heaviside (-minkowski_sq z)

/-- K_ξ is non-negative everywhere. -/
theorem K_xi_nonneg (xi : ℝ) (z : Point) : 0 ≤ K_xi xi z := by
  exact mul_nonneg (mul_nonneg (Real.exp_nonneg _)
    (by unfold Heaviside; split_ifs <;> norm_num))
    (by unfold Heaviside; split_ifs <;> norm_num)

/-- K_ξ(z) ≤ exp(-z⁰/ξ). -/
lemma K_xi_le_exp (xi : ℝ) (z : Point) : K_xi xi z ≤ Real.exp (-z 0 / xi) := by
  unfold K_xi
  calc Real.exp (-z 0 / xi) * Heaviside (z 0) * Heaviside (-minkowski_sq z)
      ≤ Real.exp (-z 0 / xi) * Heaviside (z 0) * 1 := by
          apply mul_le_mul_of_nonneg_left (Heaviside_le_one _)
          apply mul_nonneg (le_of_lt (Real.exp_pos _)) (Heaviside_nonneg _)
    _ ≤ Real.exp (-z 0 / xi) * 1 * 1 := by
          apply mul_le_mul_of_nonneg_right
          apply mul_le_mul_of_nonneg_left (Heaviside_le_one _) (le_of_lt (Real.exp_pos _))
          norm_num
    _ = Real.exp (-z 0 / xi) := by ring

/-- Future causal cone: z⁰ ≥ 0 and z² ≤ 0. -/
def CausalFuture (z : Point) : Prop := 0 ≤ z 0 ∧ minkowski_sq z ≤ 0

/-- Causal support: K_ξ(z) ≠ 0 implies z is in the future causal cone. -/
theorem causalSupport_K {xi : ℝ} {z : Point} (h : K_xi xi z ≠ 0) : CausalFuture z := by
  unfold K_xi at h
  unfold CausalFuture
  constructor
  · by_contra hc
    push_neg at hc
    have : Heaviside (z 0) = 0 := by unfold Heaviside; simp [not_le.mpr hc]
    simp [this] at h
  · by_contra hc
    push_neg at hc
    have : Heaviside (-minkowski_sq z) = 0 := by
      unfold Heaviside; simp [not_le.mpr (neg_neg_of_pos hc)]
    simp [this] at h

/-- Causal relation (timelike or lightlike separation). -/
def is_causal (x y : Point) : Prop := minkowski_sq (x - y) ≤ 0

/-! ## A.2: Correlation four-volume V_ξ -/

/-- Correlation four-volume V_ξ := ∫ K_ξ (Eq. A.4'). -/
noncomputable def V_xi (xi : ℝ) : ℝ := ∫ z : Point, K_xi xi z

/-- **THEOREM (Eq. A.4'):** V_ξ = 8πξ⁴.
    This is a full calculation, not an axiom. -/
theorem V_xi_eq (xi : ℝ) (hxi : 0 < xi) : V_xi xi = 8 * Real.pi * xi ^ 4 := by
  unfold V_xi
  -- The integral over the 3-ball of radius t is (4/3)πt³.
  have h_ball : ∀ t : ℝ, 0 ≤ t → ∫ x : Fin 3 → ℝ, (if (∑ i, x i ^ 2) ≤ t ^ 2 then 1 else 0) = (4 / 3) * Real.pi * t ^ 3 := by
    intro t ht
    have := @MeasureTheory.volume_sum_rpow_le (Fin 3)
    convert congr_arg ENNReal.toReal (@this (inferInstance) (inferInstance) 2 (by norm_num) t) using 1 <;> norm_num [Fin.sum_univ_three]
    · rw [MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator]
      change ∫ x in { x : Fin 3 → ℝ | (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ (1 / 2 : ℝ) ≤ t }, 1 = _
      · norm_num [← Real.sqrt_eq_rpow]
        rfl
      · exact measurableSet_le (Continuous.measurable (by exact Continuous.rpow (by continuity) (by continuity) <| by norm_num)) measurable_const
      · norm_num [← Real.sqrt_eq_rpow, Real.sqrt_le_left ht]
        norm_num [Filter.EventuallyEq, Set.indicator]
    · rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one, Real.Gamma_add_one] <;> norm_num
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring_nf; norm_num [ht]
      field_simp
      rw [ENNReal.toReal_ofReal (by positivity), Real.sq_sqrt (by positivity)]; ring
  -- Substitute the result for the integral over the 3-ball.
  have h_subst : ∫ z : ℝ × (Fin 3 → ℝ), (if 0 ≤ z.1 ∧ (∑ i, z.2 i ^ 2) ≤ z.1 ^ 2 then Real.exp (-z.1 / xi) else 0) = ∫ t in Set.Ici 0, Real.exp (-t / xi) * (4 / 3) * Real.pi * t ^ 3 := by
    erw [MeasureTheory.integral_prod]
    · rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
      congr with x; by_cases hx : 0 ≤ x <;> simp +decide [hx, mul_assoc]
      rw [show (∫ y : Fin 3 → ℝ, if ∑ i, y i ^ 2 ≤ x ^ 2 then Real.exp (-x / xi) else 0) = Real.exp (-x / xi) * (∫ y : Fin 3 → ℝ, if ∑ i, y i ^ 2 ≤ x ^ 2 then 1 else 0) by rw [← MeasureTheory.integral_const_mul]; congr; ext; split_ifs <;> ring_nf, h_ball x hx]; ring_nf
    · rw [MeasureTheory.integrable_prod_iff]
      · field_simp
        constructor
        · filter_upwards [] with x
          by_cases hx : 0 ≤ x <;> simp +decide [hx]
          refine' MeasureTheory.Integrable.congr _ _
          refine' fun y => Set.indicator ({ y : Fin 3 → ℝ | ∑ i, y i ^ 2 ≤ x ^ 2 }) (fun _ => Real.exp (-(x / xi))) y
          · rw [MeasureTheory.integrable_indicator_iff]
            · norm_num +zetaDelta at *
              refine' lt_of_le_of_lt (MeasureTheory.measure_mono _) _
              exact Set.Icc (-fun _ => x) (fun _ => x)
              · exact fun y hy => ⟨fun i => neg_le_of_abs_le <| by simpa [hx] using Real.abs_le_sqrt <| le_trans (Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ i)) hy, fun i => le_of_abs_le <| by simpa [hx] using Real.abs_le_sqrt <| le_trans (Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ i)) hy⟩
              · erw [Real.volume_Icc_pi]; norm_num
            · exact measurableSet_le (by measurability) (by measurability)
          · norm_num [Filter.EventuallyEq, Set.indicator]
        · have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t / xi) * (4 / 3) * Real.pi * t ^ 3) (Set.Ici 0) := by
            have h_integrable : ∫ t in Set.Ici 0, Real.exp (-t / xi) * t ^ 3 = 6 * xi ^ 4 := by
              have := @integral_rpow_mul_exp_neg_mul_rpow
              rw [MeasureTheory.integral_Ici_eq_integral_Ioi]; convert @this 1 3 (1 / xi) (by norm_num) (by norm_num) (by positivity) using 1 <;> norm_num [div_eq_mul_inv, mul_comm]
              norm_cast
            contrapose! h_integrable
            rw [MeasureTheory.integral_undef]
            · positivity
            · exact fun h => h_integrable <| by simpa [mul_assoc, mul_comm, mul_left_comm] using h.mul_const (4 / 3 * Real.pi)
          rw [← MeasureTheory.integrable_indicator_iff (measurableSet_Ici)] at *
          convert h_integrable using 1
          ext t; by_cases ht : 0 ≤ t <;> simp +decide [ht]; ring_nf
          convert congr_arg (fun x : ℝ => x * Real.exp (-(t * xi⁻¹))) (h_ball t ht) using 1 <;> ring_nf
          rw [← MeasureTheory.integral_mul_const]; congr; ext; split_ifs <;> norm_num [abs_of_nonneg, Real.exp_nonneg]
      · refine' Measurable.aestronglyMeasurable _
        exact Measurable.ite (measurableSet_le measurable_const measurable_fst |> MeasurableSet.inter <| measurableSet_le (show Measurable fun z : ℝ × (Fin 3 → ℝ) => ∑ i, z.2 i ^ 2 from by measurability) <| show Measurable fun z : ℝ × (Fin 3 → ℝ) => z.1 ^ 2 from by measurability) (by exact Measurable.exp <| by exact Measurable.div_const (measurable_neg.comp measurable_fst) _) measurable_const
  convert h_subst using 1
  · -- Identify Point with ℝ × (Fin 3 → ℝ)
    have h_iso : (MeasureTheory.volume : MeasureTheory.Measure (Fin 4 → ℝ)) = MeasureTheory.Measure.map (fun z : ℝ × (Fin 3 → ℝ) => Fin.cons z.1 z.2) (MeasureTheory.volume : MeasureTheory.Measure (ℝ × (Fin 3 → ℝ))) := by
      simp +decide [MeasureTheory.MeasureSpace.volume]
      erw [MeasureTheory.Measure.pi_eq]
      intro s hs; erw [MeasureTheory.Measure.map_apply]
      · simp +decide [Set.preimage, Fin.forall_fin_succ]
        erw [show { x : ℝ × (Fin 3 → ℝ) | x.1 ∈ s 0 ∧ x.2 0 ∈ s 1 ∧ x.2 1 ∈ s 2 ∧ x.2 2 ∈ s 3 } = (s 0 ×ˢ { x : Fin 3 → ℝ | x 0 ∈ s 1 ∧ x 1 ∈ s 2 ∧ x 2 ∈ s 3 }) by ext; aesop]; erw [MeasureTheory.Measure.prod_prod]; simp +decide [Fin.prod_univ_succ]
        erw [show { x : Fin 3 → ℝ | x 0 ∈ s 1 ∧ x 1 ∈ s 2 ∧ x 2 ∈ s 3 } = (Set.pi Set.univ fun i => if i = 0 then s 1 else if i = 1 then s 2 else s 3) by ext; simp +decide [Fin.forall_fin_succ]]; erw [MeasureTheory.Measure.pi_pi]; simp +decide [Fin.prod_univ_three]; ring!
      · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [exact measurable_fst; exact measurable_pi_iff.mp measurable_snd 0; exact measurable_pi_iff.mp measurable_snd 1; exact measurable_pi_iff.mp measurable_snd 2]
      · exact MeasurableSet.univ_pi hs
    rw [h_iso, MeasureTheory.integral_map]
    · unfold K_xi
      congr with z; unfold minkowski_sq; norm_num [Fin.sum_univ_succ]; ring_nf
      unfold minkowski_dot; norm_num [Fin.sum_univ_succ]; ring_nf
      unfold Heaviside eta; norm_num [Fin.ext_iff]; ring_nf
      grind
    · refine' Measurable.aemeasurable _
      exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [exact measurable_fst; exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd; exact measurable_pi_apply 1 |> Measurable.comp <| measurable_snd; exact measurable_pi_apply 2 |> Measurable.comp <| measurable_snd]
    · refine' Measurable.aestronglyMeasurable _
      apply_rules [Measurable.mul, Measurable.exp, Measurable.neg, Measurable.div, measurable_const]
      · exact measurable_pi_apply 0
      · exact Measurable.ite (measurableSet_Ici.preimage (measurable_pi_apply 0)) measurable_const measurable_const
      · apply_rules [Measurable.ite, measurable_const]
        unfold minkowski_sq minkowski_dot
        simp +decide [Fin.sum_univ_four, eta]
        exact measurableSet_le (Measurable.add (measurable_pi_apply 1 |> Measurable.mul <| measurable_pi_apply 1) <| Measurable.add (measurable_pi_apply 2 |> Measurable.mul <| measurable_pi_apply 2) <| measurable_pi_apply 3 |> Measurable.mul <| measurable_pi_apply 3) (measurable_pi_apply 0 |> Measurable.mul <| measurable_pi_apply 0) |> MeasurableSet.mem
  · -- Evaluate the final integral
    have h_eval : ∫ t in Set.Ici 0, Real.exp (-t / xi) * t ^ 3 = 6 * xi ^ 4 := by
      have := @integral_rpow_mul_exp_neg_mul_rpow
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]; convert @this 1 3 (1 / xi) (by norm_num) (by norm_num) (by positivity) using 1 <;> norm_num [div_eq_mul_inv, mul_comm]
      norm_cast
    rw [show (fun t : ℝ => Real.exp (-t / xi) * (4 / 3) * Real.pi * t ^ 3) = fun t : ℝ => (4 / 3) * Real.pi * (Real.exp (-t / xi) * t ^ 3) by ext; ring, MeasureTheory.integral_const_mul]; rw [h_eval]; ring

/-- V_ξ > 0 for ξ > 0. -/
theorem V_xi_pos (xi : ℝ) (hxi : 0 < xi) : 0 < V_xi xi := by
  rw [V_xi_eq xi hxi]
  positivity

/-! ## Normalized kernel -/

/-- Normalized kernel K̄_ξ := K_ξ / V_ξ. -/
noncomputable def Kbar (xi : ℝ) (z : Point) : ℝ := K_xi xi z / V_xi xi

lemma Kbar_nonneg (xi : ℝ) (hxi : 0 < xi) (z : Point) : 0 ≤ Kbar xi z := by
  unfold Kbar
  exact div_nonneg (K_xi_nonneg xi z) (le_of_lt (V_xi_pos xi hxi))

/-- **THEOREM:** ∫K̄_ξ = 1 (normalization). -/
theorem integral_Kbar (xi : ℝ) (hxi : 0 < xi) : ∫ z : Point, Kbar xi z = 1 := by
  unfold Kbar
  rw [MeasureTheory.integral_div, div_eq_iff]
  · simp +zetaDelta at *
    rfl
  · exact ne_of_gt (by rw [V_xi_eq xi hxi]; positivity)

/-! ## A.3: Collapse kernel γ(x,y) -/

/-- Collapse kernel γ(x,y) = (γ₀/N²) K_ξ(x-y) Θ[causal(x,y)] (Eq. in A.3). -/
noncomputable def gamma_kernel (gamma_0 N : ℝ) (xi : ℝ) (x y : Point) : ℝ :=
  (gamma_0 / N ^ 2) * K_xi xi (x - y) * (if is_causal x y then 1 else 0)

lemma gamma_kernel_nonneg {gamma_0 N xi : ℝ} (hγ : 0 ≤ gamma_0) (x y : Point) :
    0 ≤ gamma_kernel gamma_0 N xi x y := by
  unfold gamma_kernel
  apply mul_nonneg
  apply mul_nonneg
  · exact div_nonneg hγ (sq_nonneg _)
  · exact K_xi_nonneg xi _
  · split_ifs <;> norm_num

/-- N⁻² scaling: γ · N² is independent of N. -/
lemma gamma_mul_Nsq {gamma_0 N xi : ℝ} (hN : N ≠ 0) (x y : Point) :
    gamma_kernel gamma_0 N xi x y * N ^ 2 = gamma_0 * K_xi xi (x - y) * (if is_causal x y then 1 else 0) := by
  unfold gamma_kernel
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 hN
  field_simp [hN2]

/-! ## A.4: Entanglement gate and ν-matching -/

/-- Gate structure: C(Ψ;x,y) ∈ [0,1]. -/
structure Gate where
  C : Point → Point → ℝ
  C_nonneg : ∀ x y, 0 ≤ C x y
  C_le_one : ∀ x y, C x y ≤ 1

/-- Coarse-grained average C̄_x := (1/V_ξ) ∫ K_ξ(x-y) C(x,y) dy (Eq. A.5). -/
noncomputable def Cbar (G : Gate) (xi : ℝ) (x : Point) : ℝ :=
  (1 / V_xi xi) * ∫ y : Point, K_xi xi (x - y) * G.C x y

/-- ν-matching constraint: ν = γ₀ · C̄_x (Eq. A.5). -/
def nu_matching (nu gamma_0 : ℝ) (bar_C_val : ℝ) : Prop :=
  nu = gamma_0 * bar_C_val

/-! ## A.5: Planck anchoring -/

/-- Planck anchoring: γ₀ = Θ₀ · t_P⁻¹ (Eq. A.6). -/
def planck_anchoring (gamma_0 Theta_0 t_P : ℝ) : Prop :=
  gamma_0 = Theta_0 * t_P⁻¹

/-- Combined Planck anchoring with bounded Θ₀. -/
structure PlanckParameters where
  gamma_0 : ℝ
  Theta_0 : ℝ
  t_P : ℝ
  xi : ℝ
  L_P : ℝ
  ht_P : 0 < t_P
  hL_P : 0 < L_P
  hTheta_0_pos : 0 < Theta_0
  anchoring : planck_anchoring gamma_0 Theta_0 t_P
  correlation : xi = L_P

lemma PlanckParameters.gamma_0_pos (P : PlanckParameters) : 0 < P.gamma_0 := by
  rw [P.anchoring]
  exact mul_pos P.hTheta_0_pos (inv_pos.mpr P.ht_P)

lemma PlanckParameters.xi_pos (P : PlanckParameters) : 0 < P.xi := by
  rw [P.correlation]
  exact P.hL_P

/-! ## d'Alembertian and retarded Green function -/

/-- NormedAddCommGroup instance for Point. -/
noncomputable instance : NormedAddCommGroup Point := by unfold Point; infer_instance

/-- NormedSpace instance for Point. -/
noncomputable instance : NormedSpace ℝ Point := by unfold Point; infer_instance

/-- Basis vector in Minkowski space. -/
def basis_vector (i : Fin 4) : Point :=
  fun j => if i = j then 1 else 0

/-- d'Alembertian operator □ = η^μν ∂_μ ∂_ν. -/
noncomputable def dAlembertian (f : Point → ℝ) (x : Point) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, eta i j * (iteratedFDeriv ℝ 2 f x (Fin.cons (basis_vector i) (Fin.cons (basis_vector j) finZeroElim)))

/-- Retarded Green function property: support in future light cone, satisfies Klein-Gordon. -/
def is_retarded_green_function (Delta_R : Point → ℝ) (m_T : ℝ) : Prop :=
  (∀ z, z 0 < 0 ∨ minkowski_sq z > 0 → Delta_R z = 0) ∧
  (∀ z, z ≠ 0 → dAlembertian Delta_R z - m_T ^ 2 * Delta_R z = 0)

/-- Existence of retarded Green function (standard QFT result). -/
axiom exists_retardedGreen (m_T : ℝ) (hmT : 0 < m_T) :
  ∃ Delta_R : Point → ℝ, is_retarded_green_function Delta_R m_T

end QFTT.WESH.AppendixA

end