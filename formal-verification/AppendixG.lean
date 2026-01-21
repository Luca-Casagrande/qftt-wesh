/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-
Formalization of Appendix G: WESH-Noether as Pre-Geometric Path Independence.

Key results (all proven, not axiomatized):
- lindbladAdjoint: D†[A] = LAL - ½(L²A + AL²)
- weshGeneratorAdjoint: L†[A] = -i[H,A] + Σγ D†[A]
- trace_lindblad_adjoint_self: Tr(Q D†[Q]) = -½ Tr([L,Q]†[L,Q])
- wesh_noether_iff_commute: Prop G.2 — WESH-Noether ⟺ [H,Q]=0 ∧ [L,Q]=0
- wesh_generator_duality: Tr(Q L[ρ]) = Tr(L†[Q] ρ)
- wesh_path_independence: Cor G.1.1 — d/ds⟨Q⟩ = 0
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
Definition of the Lindblad dissipator adjoint for a Hermitian operator L.
-/
def lindbladAdjoint {n : Type} [Fintype n] [DecidableEq n] (L : Matrix n n ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  L * A * L - (1 / 2 : ℂ) • (L ^ 2 * A + A * L ^ 2)

/-
Definition of the WESH generator adjoint.
L^†[A] = -i[H, A] + ∑_k γ_k D_{L_k}^†[A]
-/
def weshGeneratorAdjoint {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I) • (H * A - A * H) +
  L_gamma.foldl (fun acc p => acc + (p.2 : ℂ) • lindbladAdjoint p.1 A) 0

/-
Definition of the Pre-geometric WESH-Noether condition.
-/
def weshNoether {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ) : Prop :=
  weshGeneratorAdjoint H L_gamma Q = 0

/-
Trace of B [A, B] is 0.
-/
lemma trace_commutator_self {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) : Matrix.trace (B * (A * B - B * A)) = 0 := by
  -- Expand the expression using the distributive property of the trace over matrix multiplication.
  simp [mul_sub, Matrix.trace_mul_comm B];
  norm_num [ Matrix.mul_assoc, Matrix.trace_mul_comm B ]

/-
Trace of Q D_L[Q] is -1/2 Tr([L, Q]† [L, Q]).
-/
lemma trace_lindblad_adjoint_self {n : Type} [Fintype n] [DecidableEq n] (L Q : Matrix n n ℂ) (hL : L.IsHermitian) (hQ : Q.IsHermitian) :
  Matrix.trace (Q * lindbladAdjoint L Q) = - (1 / 2 : ℂ) * Matrix.trace (Matrix.conjTranspose (L * Q - Q * L) * (L * Q - Q * L)) := by
    unfold lindbladAdjoint;
    simp +decide [ mul_sub, mul_add, mul_assoc, Matrix.sub_mul, Matrix.trace_mul_comm L, hL.eq, hQ.eq ] ; ring_nf;
    norm_num [ sq, Matrix.mul_assoc ]

/-
Trace of A† A is non-negative (real part).
-/
lemma trace_conj_mul_self_nonneg {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : 0 ≤ (Matrix.trace (Matrix.conjTranspose A * A)).re := by
  norm_num [ Matrix.trace ];
  norm_num [ Matrix.mul_apply ];
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ )

/-
Trace of A† A is 0 iff A is 0.
-/
lemma trace_conj_mul_self_eq_zero_iff {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Matrix.trace (Matrix.conjTranspose A * A) = 0 ↔ A = 0 := by
  have h_trace : (Matrix.trace (Matrix.conjTranspose A * A)).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    simp +decide [ Matrix.trace, Matrix.mul_apply, Complex.normSq, Complex.sq_norm ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  constructor <;> intro h <;> simp_all +decide [ Complex.ext_iff ];
  -- Since the sum of non-negative terms is zero, each term must be zero.
  have h_zero : ∀ i j, ‖A i j‖^2 = 0 := by
    exact fun i j => by rw [ eq_comm ] at h_trace; exact le_antisymm ( h_trace ▸ Finset.single_le_sum ( fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ( ‖A i j‖ ) ) ( Finset.mem_univ i ) |> le_trans ( Finset.single_le_sum ( fun j _ => sq_nonneg ( ‖A i j‖ ) ) ( Finset.mem_univ j ) ) ) ( sq_nonneg _ ) ;
  exact Matrix.ext fun i j => norm_eq_zero.mp <| sq_eq_zero_iff.mp <| h_zero i j

/-
The trace of Q * L†[Q] is the sum of traces of Q * D†[Q] (weighted by gamma), since the Hamiltonian part vanishes.
-/
lemma trace_wesh_generator_adjoint_eq_sum
  {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ) :
  Matrix.trace (Q * weshGeneratorAdjoint H L_gamma Q) =
  (L_gamma.map (fun p => (p.2 : ℂ) * Matrix.trace (Q * lindbladAdjoint p.1 Q))).sum := by
    unfold weshGeneratorAdjoint;
    induction' L_gamma using List.reverseRecOn with p L_gamma ih;
    · simp +decide [ Matrix.mul_sub, mul_assoc, Matrix.trace_mul_comm ( Q : Matrix n n ℂ ) ];
    · simp_all +decide [ Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, List.foldl_append ];
      linear_combination' ih

/-
If WESH-Noether holds, then all active Lindblad operators commute with Q.
-/
lemma wesh_noether_implies_lindblad_commute {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ)
  (_hH : H.IsHermitian) (hQ : Q.IsHermitian)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian)
  (h_gamma : ∀ p ∈ L_gamma, 0 ≤ p.2)
  (h_noether : weshNoether H L_gamma Q) :
  ∀ p ∈ L_gamma, p.2 > 0 → Commute p.1 Q := by
    have h_trace_zero : Matrix.trace (Q * weshGeneratorAdjoint H L_gamma Q) = 0 := by
      unfold weshNoether at h_noether; aesop;
    -- Applying the trace_lindblad_adjoint_self lemma to each term in the sum, we get that the sum of the traces of the Lindblad terms is zero.
    have h_lindblad_trace_zero : (L_gamma.map (fun p => (p.2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)))).sum = 0 := by
      have h_lindblad_trace_zero : Matrix.trace (Q * weshGeneratorAdjoint H L_gamma Q) = - (1 / 2 : ℂ) * (L_gamma.map (fun p => (p.2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)))).sum := by
        rw [ trace_wesh_generator_adjoint_eq_sum ];
        have h_lindblad_trace_zero : ∀ p ∈ L_gamma, Matrix.trace (Q * lindbladAdjoint p.1 Q) = - (1 / 2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)) := by
          exact fun p a => trace_lindblad_adjoint_self p.1 Q (hL p a) hQ;
        rw [ ← List.sum_map_mul_left ];
        exact congr_arg _ ( List.map_congr_left fun p hp => by rw [ h_lindblad_trace_zero p hp ] ; ring );
      grind;
    -- Since the sum of non-negative terms is zero, each term must be zero.
    have h_each_term_zero : ∀ p ∈ L_gamma, (p.2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)) = 0 := by
      have h_each_term_zero : ∀ p ∈ L_gamma, 0 ≤ (p.2 : ℝ) * (Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1))).re := by
        intros p hp
        apply mul_nonneg (h_gamma p hp);
        apply trace_conj_mul_self_nonneg;
      have h_each_term_zero : ∀ p ∈ L_gamma, (p.2 : ℝ) * (Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1))).re = 0 := by
        have h_each_term_zero : ∀ {l : List ℝ}, (∀ x ∈ l, 0 ≤ x) → List.sum l = 0 → ∀ x ∈ l, x = 0 := by
          exact fun {l} a a_1 x a_2 => List.all_zero_of_le_zero_le_of_sum_eq_zero a a_1 a_2;
        intros p hp
        have h_sum_zero : List.sum (List.map (fun p => (p.2 : ℝ) * (Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1))).re) L_gamma) = 0 := by
          convert congr_arg Complex.re h_lindblad_trace_zero using 1;
          induction' L_gamma with p L_gamma ih;
          · contradiction;
          · induction' ( p :: L_gamma ) with p L_gamma ih <;> norm_num [ Complex.ext_iff ] at * ; linarith;
        exact h_each_term_zero ( fun x hx => by obtain ⟨ p, hp, rfl ⟩ := List.mem_map.mp hx; exact ‹∀ p ∈ L_gamma, 0 ≤ p.2 * ( ( p.1 * Q - Q * p.1 ).conjTranspose * ( p.1 * Q - Q * p.1 ) ).trace.re› p hp ) h_sum_zero _ ( List.mem_map.mpr ⟨ p, hp, rfl ⟩ );
      intro p hp; specialize h_each_term_zero p hp; simp_all +decide [ Complex.ext_iff ] ;
      have h_trace_imag_zero : ∀ A : Matrix n n ℂ, (Matrix.trace (Matrix.conjTranspose A * A)).im = 0 := by
        simp +decide [ Matrix.trace, Matrix.mul_apply ];
        exact fun A => Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => by ring;
      specialize h_trace_imag_zero ( p.1 * Q - Q * p.1 ) ; simp_all +decide [ Matrix.conjTranspose_mul ] ;
    intro p hp hp_pos; specialize h_each_term_zero p hp; simp_all +decide ;
    have h_comm : p.1 * Q - Q * p.1 = 0 := by
      have h_comm : Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)) = 0 := by
        convert h_each_term_zero.resolve_left hp_pos.ne' using 1 ; simp +decide [ Matrix.conjTranspose_mul ];
      exact (trace_conj_mul_self_eq_zero_iff (p.1 * Q - Q * p.1)).mp h_comm;
    exact sub_eq_zero.mp h_comm

/-
If L and Q commute, then the Lindblad adjoint D_L[Q] is zero.
-/
lemma commute_implies_lindblad_adjoint_zero {n : Type} [Fintype n] [DecidableEq n]
  (L Q : Matrix n n ℂ) (h : Commute L Q) : lindbladAdjoint L Q = 0 := by
    ext i j;
    unfold lindbladAdjoint;
    simp +decide [ sq, mul_assoc, h.eq ];
    simp +decide [ ← mul_assoc, h.eq ] ; ring

/-
Proposition G.2: WESH-Noether holds iff [H, Q] = 0 and [L, Q] = 0 for all L with positive rate.
-/
theorem wesh_noether_iff_commute {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ)
  (hH : H.IsHermitian) (hQ : Q.IsHermitian)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian)
  (h_gamma : ∀ p ∈ L_gamma, 0 ≤ p.2) :
  weshNoether H L_gamma Q ↔ Commute H Q ∧ (∀ p ∈ L_gamma, p.2 > 0 → Commute p.1 Q) := by
    constructor <;> intros h' <;> simp_all +decide [ weshNoether ];
    · -- If WESH-Noether holds, then all active Lindblad operators commute with Q.
      have h_commute : ∀ p ∈ L_gamma, p.2 > 0 → Commute p.1 Q := by
        apply_rules [ wesh_noether_implies_lindblad_commute ];
        · grind;
        · aesop;
      -- Since the Hamiltonian part of the WESH-Noether condition must vanish, we have [H, Q] = 0.
      have h_hamiltonian : (-Complex.I) • (H * Q - Q * H) = 0 := by
        have h_hamiltonian : (-Complex.I) • (H * Q - Q * H) = - (L_gamma.foldl (fun acc p => acc + (p.2 : ℂ) • lindbladAdjoint p.1 Q) 0) := by
          exact eq_neg_of_add_eq_zero_left h';
        -- Since each Lindblad adjoint term is zero, their sum is also zero.
        have h_lindblad_zero : ∀ p ∈ L_gamma, (p.2 : ℂ) • lindbladAdjoint p.1 Q = 0 := by
          intro p hp; specialize h_commute p hp; by_cases h : p.2 > 0 <;> simp_all +decide [ lindbladAdjoint ] ;
          · simp_all +decide [ sq, mul_assoc, Commute.eq ];
            exact Or.inr ( by ext i j; norm_num; ring );
          · exact Or.inl ( le_antisymm h ( h_gamma _ _ hp ) );
        have h_foldl_zero : ∀ {L : List (Matrix n n ℂ × ℝ)}, (∀ p ∈ L, (p.2 : ℂ) • lindbladAdjoint p.1 Q = 0) → List.foldl (fun acc p => acc + (p.2 : ℂ) • lindbladAdjoint p.1 Q) 0 L = 0 := by
          intros L hL; induction' L using List.reverseRecOn with p L ih <;> aesop;
        rw [ h_hamiltonian, h_foldl_zero h_lindblad_zero, neg_zero ];
      simp_all +decide [ Commute, sub_eq_zero ];
      exact ⟨ by simp_all +decide [ SemiconjBy ], h_commute ⟩;
    · rw [ weshGeneratorAdjoint ];
      -- Since $[H, Q] = 0$ and $[L, Q] = 0$ for all $L$ with positive rate, each term in the sum is zero.
      have h_zero_terms : ∀ p ∈ L_gamma, p.2 > 0 → lindbladAdjoint p.1 Q = 0 := by
        intros p hp hp_pos
        apply commute_implies_lindblad_adjoint_zero
        apply h'.2 p.1 p.2 hp hp_pos;
      -- Since each term in the sum is zero, the entire sum is zero.
      have h_sum_zero : List.foldl (fun (acc : Matrix n n ℂ) (p : Matrix n n ℂ × ℝ) => acc + (p.2 : ℂ) • lindbladAdjoint p.1 Q) 0 L_gamma = 0 := by
        have h_sum_zero : ∀ p ∈ L_gamma, (p.2 : ℂ) • lindbladAdjoint p.1 Q = 0 := by
          intro p hp; specialize h_zero_terms p hp; cases lt_or_eq_of_le ( h_gamma _ _ hp ) <;> aesop;
        have h_sum_zero : ∀ {l : List (Matrix n n ℂ × ℝ)}, (∀ p ∈ l, (p.2 : ℂ) • lindbladAdjoint p.1 Q = 0) → List.foldl (fun (acc : Matrix n n ℂ) (p : Matrix n n ℂ × ℝ) => acc + (p.2 : ℂ) • lindbladAdjoint p.1 Q) 0 l = 0 := by
          intros l hl; induction' l using List.reverseRecOn with p l ih <;> aesop;
        exact h_sum_zero ‹_›;
      simp_all +decide [ ← h'.1.eq ]

/-
Definition of the WESH generator (primal).
L[ρ] = i[H, ρ] + ∑_k γ_k D_{L_k}[ρ]
Note: The Hamiltonian term has a sign flip relative to the adjoint to ensure duality.
The dissipative term is self-dual for Hermitian Lindblad operators.
-/
def weshGenerator {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (rho : Matrix n n ℂ) : Matrix n n ℂ :=
  (Complex.I) • (H * rho - rho * H) +
  L_gamma.foldl (fun acc p => acc + (p.2 : ℂ) • lindbladAdjoint p.1 rho) 0

/-
Duality of the WESH generator: Tr(Q L[ρ]) = Tr(L†[Q] ρ).
-/
lemma wesh_generator_duality {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q rho : Matrix n n ℂ)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian) :
  Matrix.trace (Q * weshGenerator H L_gamma rho) = Matrix.trace (weshGeneratorAdjoint H L_gamma Q * rho) := by
    unfold weshGenerator weshGeneratorAdjoint;
    induction' L_gamma using List.reverseRecOn with p L_gamma ih;
    · simp +decide [ mul_assoc, mul_sub, sub_mul, Matrix.trace_mul_comm Q ];
      rw [ ← Matrix.trace_mul_comm, Matrix.mul_assoc ];
    · have h_trace : Matrix.trace (Q * lindbladAdjoint L_gamma.1 rho) = Matrix.trace (lindbladAdjoint L_gamma.1 Q * rho) := by
        unfold lindbladAdjoint;
        simp +decide [ sq, mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.trace_mul_comm L_gamma.1 ] ; ring;
      simp_all +decide [ Matrix.mul_add, Matrix.add_mul ];
      linear_combination' ih

/-
Corollary G.1.1: Path independence / s-conservation.
If WESH-Noether holds, then d/ds <Q> = Tr(Q L[rho]) = 0 for any state rho.
-/
theorem wesh_path_independence {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q rho : Matrix n n ℂ)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian)
  (h_noether : weshNoether H L_gamma Q) :
  Matrix.trace (Q * weshGenerator H L_gamma rho) = 0 := by
    -- By the duality relation between the WESH generator and its adjoint, we have:
    have h_dual : Matrix.trace (Q * weshGenerator H L_gamma rho) = Matrix.trace (weshGeneratorAdjoint H L_gamma Q * rho) := by
      exact wesh_generator_duality H L_gamma Q rho hL;
    unfold weshNoether at h_noether; aesop;

/-
Complete structure for WESH-Noether as pre-geometric path independence.
-/

/-- Pre-geometric WESH-Noether structure combining all elements of Appendix G. -/
structure PreGeometricWESH (n : Type) [Fintype n] [DecidableEq n] where
  /-- Effective Hamiltonian H_eff -/
  H : Matrix n n ℂ
  /-- Lindblad operators with rates (L_k, γ_k) -/
  L_gamma : List (Matrix n n ℂ × ℝ)
  /-- Conserved charge Q -/
  Q : Matrix n n ℂ
  /-- H is Hermitian -/
  hH : H.IsHermitian
  /-- Q is Hermitian -/
  hQ : Q.IsHermitian
  /-- All Lindblad operators are Hermitian -/
  hL : ∀ p ∈ L_gamma, p.1.IsHermitian
  /-- All rates are non-negative -/
  h_gamma : ∀ p ∈ L_gamma, 0 ≤ p.2

/-- WESH-Noether condition for the structure. -/
def PreGeometricWESH.noetherCondition {n : Type} [Fintype n] [DecidableEq n] 
    (W : PreGeometricWESH n) : Prop :=
  weshNoether W.H W.L_gamma W.Q

/-- Equivalence: WESH-Noether ⟺ all commutators vanish. -/
theorem PreGeometricWESH.noether_iff_commute {n : Type} [Fintype n] [DecidableEq n]
    (W : PreGeometricWESH n) :
    W.noetherCondition ↔ Commute W.H W.Q ∧ (∀ p ∈ W.L_gamma, p.2 > 0 → Commute p.1 W.Q) :=
  wesh_noether_iff_commute W.H W.L_gamma W.Q W.hH W.hQ W.hL W.h_gamma

/-- Path independence: if WESH-Noether holds, d/ds⟨Q⟩ = 0 for any state. -/
theorem PreGeometricWESH.path_independence {n : Type} [Fintype n] [DecidableEq n]
    (W : PreGeometricWESH n) (rho : Matrix n n ℂ) (h : W.noetherCondition) :
    Matrix.trace (W.Q * weshGenerator W.H W.L_gamma rho) = 0 :=
  wesh_path_independence W.H W.L_gamma W.Q rho W.hL h