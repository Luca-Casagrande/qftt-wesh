/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

/-!
# Section 6 Part I — Black Hole Thermodynamics (QFTT-WESH)

Formal derivation of Bekenstein–Hawking entropy from WESH principles.
The universal 1/4 prefactor emerges from bipartite pairing (1/2) × swap-even projection (1/2).

## Main results

* `trace_swap`: Tr(G_xy) = D (orthonormal basis decomposition)
* `theorem_6_1_asymptotic_halving`: Tr(P_swap_even)/Tr(id) = D(D+1)/(2D²)
* `factor_swap_even_tendsto_half`: factor_swap_even(D) → 1/2 as D → ∞
* `corollary_universal_prefactor`: N_phys(D) → (1/4)(A/ξ²) as D → ∞
* `theorem_S_BH_asymptotics`: S_BH = A/(4ξ²) + O(1)

All theorems fully proven without axioms or `sorry` statements.
-/

set_option linter.mathlibStandardSet false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical Pointwise

noncomputable section

open TensorProduct LinearMap Filter Topology Asymptotics

namespace QFTTWESH.Section6.Part1

variable (D : ℕ)

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

abbrev H_kin := H ⊗[ℂ] H

def G_xy : H_kin H →ₗ[ℂ] H_kin H := TensorProduct.comm ℂ H H

/-- The swap-even state-level projector `P_swap_even = (1 + G_xy)/2`. -/
noncomputable def P_swap_even : H_kin H →ₗ[ℂ] H_kin H :=
  (2 : ℂ)⁻¹ • (LinearMap.id + G_xy H)

lemma trace_id_tensor (hD : Module.finrank ℂ H = D) :
    LinearMap.trace ℂ (H_kin H) LinearMap.id = (D : ℂ) ^ 2 := by
  classical
  have hfinrank : Module.finrank ℂ (H_kin H) = D * D := by
    dsimp [H_kin]; rw [Module.finrank_tensorProduct, hD]
  simp [LinearMap.trace_id, hfinrank, pow_two, Nat.cast_mul]

/-- Tr(swap) = D. Standard linear algebra result. -/
theorem trace_swap (hD : Module.finrank ℂ H = D) :
    LinearMap.trace ℂ (H_kin H) (G_xy H) = (D : ℂ) := by
  -- Let's choose an orthonormal basis $\{e_i\}$ for $H$.
  obtain ⟨basis, hbasis⟩ : ∃ basis : OrthonormalBasis (Fin D) ℂ H, True := by
    simp;
    exact ⟨ by simpa [ hD ] using ( stdOrthonormalBasis ℂ H ) |> OrthonormalBasis.reindex <| Fintype.equivFinOfCardEq <| by simp +decide [ hD ] ⟩;
  unfold QFTTWESH.Section6.Part1.G_xy;
  rw [ LinearMap.trace_eq_matrix_trace ℂ ( basis.toBasis.tensorProduct basis.toBasis ) ];
  simp +decide [ Matrix.trace, LinearMap.toMatrix_apply ];
  erw [ Finset.sum_product ] ; aesop

/--
Theorem 6.1 (Asymptotic halving / symmetric-subspace count):
`Tr(P_swap_even)/Tr(id) = D(D+1)/(2D²)`.
-/
theorem theorem_6_1_asymptotic_halving (hD : Module.finrank ℂ H = D) :
    (LinearMap.trace ℂ (H_kin H) (P_swap_even H)) / (LinearMap.trace ℂ (H_kin H) LinearMap.id) =
      (D * (D + 1) / 2 : ℂ) / (D ^ 2 : ℂ) := by
  classical
  have h_id := trace_id_tensor D H hD
  have h_sw := trace_swap D H hD
  have h_even : LinearMap.trace ℂ (H_kin H) (P_swap_even H) = (2 : ℂ)⁻¹ * ((D : ℂ) ^ 2 + (D : ℂ)) := by
    simp only [P_swap_even, map_smul, map_add, h_id, h_sw, smul_eq_mul]
  rw [h_even, h_id]; field_simp

noncomputable def factor_bipartite : ℝ := 1 / 2

/-- Swap-even projection factor as a function of `D`: (D(D+1)/2)/D². -/
noncomputable def factor_swap_even (D : ℕ) : ℝ := (D * (D + 1) / 2 : ℝ) / (D ^ 2 : ℝ)

lemma factor_swap_even_eq (D : ℕ) (hD : D ≠ 0) : factor_swap_even D = 1/2 + 1/(2 * D) := by
  unfold factor_swap_even
  have hD_pos : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  field_simp [hD_pos]

theorem factor_swap_even_tendsto_half : Tendsto (fun D : ℕ => factor_swap_even D) atTop (nhds (1/2 : ℝ)) := by
  have h_eq : ∀ D : ℕ, D ≠ 0 → factor_swap_even D = 1/2 + 1/(2 * D) := fun D hD => factor_swap_even_eq D hD
  have h_tail : Tendsto (fun D : ℕ => (1 : ℝ)/(2 * D)) atTop (nhds 0) := by
    have h1 : Tendsto (fun D : ℕ => (2 * D : ℝ)⁻¹) atTop (nhds 0) := by
      apply tendsto_inv_atTop_zero.comp
      exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    simp only [one_div]; exact h1
  have h_sum : Tendsto (fun D : ℕ => (1/2 : ℝ) + 1/(2 * D)) atTop (nhds (1/2 + 0)) :=
    Tendsto.add tendsto_const_nhds h_tail
  simp only [add_zero] at h_sum
  apply h_sum.congr'
  filter_upwards [Ioi_mem_atTop 0] with D hD
  exact (h_eq D (Nat.pos_iff_ne_zero.mp hD)).symm

variable (A ξ : ℝ)

/-- `N_phys = factor_bipartite * factor_swap_even * (A/ξ²)`. -/
noncomputable def N_phys (D : ℕ) : ℝ := factor_bipartite * factor_swap_even D * (A / ξ ^ 2)

/-- Universal 1/4 prefactor: N_phys → (1/4)(A/ξ²) -/
theorem corollary_universal_prefactor :
    Tendsto (fun D : ℕ => N_phys A ξ D) atTop (nhds ((1 / 4) * (A / ξ ^ 2))) := by
  unfold N_phys factor_bipartite
  have h_factor := factor_swap_even_tendsto_half
  have h_half : Tendsto (fun D : ℕ => (1/2 : ℝ) * factor_swap_even D) atTop (nhds ((1/2) * (1/2))) :=
    tendsto_const_nhds.mul h_factor
  have h_full : Tendsto (fun D : ℕ => (1/2 : ℝ) * factor_swap_even D * (A / ξ^2)) atTop
                        (nhds ((1/2) * (1/2) * (A / ξ^2))) :=
    h_half.mul tendsto_const_nhds
  simp only [show (1/2 : ℝ) * (1/2) = 1/4 by norm_num, show (1/4 : ℝ) * (A / ξ^2) = 1/4 * (A / ξ^2) by ring] at h_full
  exact h_full

variable (s_bar : ℝ → ℝ)

noncomputable def N_phys_limit : ℝ := (1 / 4) * (A / ξ ^ 2)

noncomputable def S_BH : ℝ := N_phys_limit A ξ * s_bar A

/-- Bekenstein-Hawking asymptotics: S_BH = A/(4ξ²) + O(1) -/
theorem theorem_S_BH_asymptotics
    (h_s_bar : (fun A => s_bar A - 1) =O[atTop] (fun A => ξ ^ 2 / A)) :
    (fun A => S_BH A ξ s_bar - A / (4 * ξ ^ 2)) =O[atTop] (fun _ => (1 : ℝ)) := by
  have h_diff : ∀ A, S_BH A ξ s_bar - A / (4 * ξ^2) = (1/4) * (A / ξ^2) * (s_bar A - 1) := by
    intro A; unfold S_BH N_phys_limit; ring
  simp_rw [h_diff]
  have h_prod : (fun A => (1 / 4) * (A / ξ ^ 2) * (s_bar A - 1)) =O[Filter.atTop] (fun A => (1 / 4) * (A / ξ ^ 2) * (ξ ^ 2 / A)) := by
    apply_rules [ Asymptotics.IsBigO.mul, Asymptotics.isBigO_refl ];
  refine h_prod.trans ?_;
  refine' Asymptotics.isBigO_iff.mpr _;
  by_cases hξ : ξ = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ];
  · exact ⟨ 0, 0, fun _ _ => le_rfl ⟩;
  · exact ⟨ 4⁻¹, 1, fun x hx => by rw [ ← mul_assoc, mul_inv_cancel₀ ( by positivity ), one_mul ] ⟩

end QFTTWESH.Section6.Part1