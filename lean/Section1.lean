/-
WESH Section 1 Formalization

Formal support for Section 1 of:
"A Dissipative Time-Field Completion of Wheeler--DeWitt Dynamics:
The Weak Entanglement Symmetry Hypothesis"

Scope of this file:
- pre-geometric finite-range N_xi locality;
- WESH--Noether algebraic conservation;
- quadratic local dissipator selection from unraveling-level CPT and N² stability;
- WESH master equation with local and bilocal jump operators;
- unnormalized Rényi-2 entanglement gate used in the submitted manuscript;
- eigentime production functional Γ and monotonicity lemmas;
- collective scaling balance selecting α = 2;
- formal G → 0 decoupling of dissipative rates;
- parameter consistency table for Section 1.

This file is intentionally restricted to the Section 1 manuscript scope.

Boundary with the appendices of the submitted manuscript:
- Appendix A fixes an illustrative flat-space realisation of the kernel and
  Planck-scale anchoring; this file formalises only the Section 1
  pre-geometric `Nξ` kernel algebra.
- Appendix B develops the auxiliary-parameter interpretation and the full
  counting-process/LLN narrative; this file proves the algebraic
  positivity and survival-probability consequences used in Section 1.
- The N-scaling appendix gives heuristic large-`N` scaling arguments; this
  file proves the algebraic fixed-regime selection `α = 2`.
- Appendix D contains the detailed WESH--Noether derivation; this file
  includes the finite algebraic trace machinery needed by the Section 1
  statement.
- Appendix E treats CP/TP preservation for the nonlinear frozen-rate
  product-integral evolution; this file contains the Lindblad and
  `Nξ`-local algebraic core, not the analytic product-integral theorem.
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

open scoped BigOperators Real Nat Classical Pointwise
open Filter Topology

noncomputable section

namespace WESH.Section1

/-! ## 1. Pre-geometric finite-range label structure -/

/--
A pre-geometric finite-range label graph.  The relation `Nxi` is the
fundamental finite-range neighbourhood used by WESH before any metric
structure has emerged.  Symmetry is part of the label-space structure.
-/
structure PreGeometricGraph (Site : Type*) where
  Nxi : Site → Site → Prop
  decidable_Nxi : DecidableRel Nxi
  symmetric : ∀ x y : Site, Nxi x y → Nxi y x

/-- Indicator of the pre-geometric neighbourhood relation. -/
def Nxi_indicator {Site : Type*} (G : PreGeometricGraph Site) (x y : Site) : ℝ :=
  letI : DecidableRel G.Nxi := G.decidable_Nxi
  if G.Nxi x y then 1 else 0

/-- The neighbourhood indicator is non-negative. -/
theorem Nxi_indicator_nonneg {Site : Type*} (G : PreGeometricGraph Site) (x y : Site) :
    0 ≤ Nxi_indicator G x y := by
  unfold Nxi_indicator
  letI : DecidableRel G.Nxi := G.decidable_Nxi
  by_cases h : G.Nxi x y
  · simp [h]
  · simp [h]

/-- The neighbourhood indicator is bounded by one. -/
theorem Nxi_indicator_le_one {Site : Type*} (G : PreGeometricGraph Site) (x y : Site) :
    Nxi_indicator G x y ≤ 1 := by
  unfold Nxi_indicator
  letI : DecidableRel G.Nxi := G.decidable_Nxi
  by_cases h : G.Nxi x y
  · simp [h]
  · simp [h]

/--
Finite-range WESH rate kernel:
`γ(x,y) = γ₀ Kξ(x,y) 1_{Nξ}(x,y) / N²`.
-/
def WESH_gamma_kernel {Site : Type*}
    (gamma0 Ntot : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (x y : Site) : ℝ :=
  gamma0 * Kxi x y * Nxi_indicator G x y / (Ntot ^ 2)

/--
Finite-cardinality value of the total label number `N`.  The pointwise kernel
keeps an explicit `Ntot` for asymptotic scaling arguments, while the finite
pre-geometric graph instantiation binds it to `Fintype.card Site`.
-/
def WESH_Ntot_card (Site : Type*) [Fintype Site] : ℝ :=
  (Fintype.card Site : ℝ)

/--
Finite-cardinality WESH kernel obtained by setting `N = card(Site)`.
This is the paper-level finite-label instantiation of the `N^{-2}` prefactor.
-/
def WESH_gamma_kernel_card {Site : Type*} [Fintype Site]
    (gamma0 : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (x y : Site) : ℝ :=
  WESH_gamma_kernel gamma0 (WESH_Ntot_card Site) Kxi G x y

/-- The finite-range kernel vanishes outside the pre-geometric neighbourhood. -/
theorem WESH_gamma_outside_Nxi_vanishes {Site : Type*}
    (gamma0 Ntot : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (x y : Site)
    (h_not : ¬ G.Nxi x y) :
    WESH_gamma_kernel gamma0 Ntot Kxi G x y = 0 := by
  unfold WESH_gamma_kernel Nxi_indicator
  letI : DecidableRel G.Nxi := G.decidable_Nxi
  simp [h_not]

/-- The finite-range WESH kernel is non-negative under the physical sign conditions. -/
theorem WESH_gamma_kernel_nonneg {Site : Type*}
    (gamma0 Ntot : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (x y : Site)
    (h_gamma0 : 0 ≤ gamma0)
    (hK : ∀ x y : Site, 0 ≤ Kxi x y) :
    0 ≤ WESH_gamma_kernel gamma0 Ntot Kxi G x y := by
  unfold WESH_gamma_kernel
  have hnum : 0 ≤ gamma0 * Kxi x y * Nxi_indicator G x y := by
    exact mul_nonneg (mul_nonneg h_gamma0 (hK x y)) (Nxi_indicator_nonneg G x y)
  have hden : 0 ≤ Ntot ^ 2 := sq_nonneg Ntot
  exact div_nonneg hnum hden

/-- The cardinality-bound WESH kernel vanishes outside `Nξ`. -/
theorem WESH_gamma_kernel_card_outside_Nxi_vanishes {Site : Type*} [Fintype Site]
    (gamma0 : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (x y : Site)
    (h_not : ¬ G.Nxi x y) :
    WESH_gamma_kernel_card gamma0 Kxi G x y = 0 := by
  unfold WESH_gamma_kernel_card
  exact WESH_gamma_outside_Nxi_vanishes gamma0 (WESH_Ntot_card Site) Kxi G x y h_not

/-- The cardinality-bound WESH kernel is non-negative under the sign conditions. -/
theorem WESH_gamma_kernel_card_nonneg {Site : Type*} [Fintype Site]
    (gamma0 : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (x y : Site)
    (h_gamma0 : 0 ≤ gamma0)
    (hK : ∀ x y : Site, 0 ≤ Kxi x y) :
    0 ≤ WESH_gamma_kernel_card gamma0 Kxi G x y := by
  unfold WESH_gamma_kernel_card
  exact WESH_gamma_kernel_nonneg gamma0 (WESH_Ntot_card Site) Kxi G x y h_gamma0 hK

/-- Symmetry of the finite-range relation transfers through the graph data. -/
theorem Nxi_symmetric {Site : Type*} (G : PreGeometricGraph Site)
    {x y : Site} (h : G.Nxi x y) : G.Nxi y x :=
  G.symmetric x y h

/-- Algebraic form of bounded total pair power under the N⁻² prefactor. -/
theorem pair_power_normalization (gamma0 Ntot W : ℝ) (hN : Ntot ≠ 0) :
    gamma0 / (Ntot ^ 2) * (Ntot ^ 2 * W) = gamma0 * W := by
  have hN2 : Ntot ^ 2 ≠ 0 := pow_ne_zero 2 hN
  field_simp [hN2]

/-! ## 2. Generic algebraic operations and Lindblad channels -/

section GenericOperatorAlgebra

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Commutator `[X,Y]=XY-YX`. -/
def commutator (X Y : A) : A := X * Y - Y * X

/-- Anticommutator `{X,Y}=XY+YX`. -/
def anticommutator (X Y : A) : A := X * Y + Y * X

/-- Schrödinger-picture Lindblad dissipator. -/
def lindblad (L ρ : A) : A :=
  L * ρ * star L - ((1 / 2 : ℂ) • anticommutator (star L * L) ρ)

/-- Heisenberg-picture Lindblad adjoint. -/
def lindbladAdjoint (L O : A) : A :=
  star L * O * L - ((1 / 2 : ℂ) • anticommutator (star L * L) O)


/--
A faithful cyclic complex trace on the operator algebra.  This records the
trace properties used in the WESH--Noether dissipative argument: cyclicity,
complex linearity, and positive-definiteness of `tr(X†X)`.
-/
class IsTrace (tr : A → ℂ) : Prop where
  /-- Cyclicity of the trace. -/
  cyclic : ∀ X Y : A, tr (X * Y) = tr (Y * X)
  /-- Additivity of the trace. -/
  add : ∀ X Y : A, tr (X + Y) = tr X + tr Y
  /-- Complex homogeneity of the trace. -/
  smul : ∀ (c : ℂ) (X : A), tr (c • X) = c * tr X
  /-- The trace of zero is zero. -/
  trace_zero : tr 0 = 0
  /-- Positivity of the Hilbert--Schmidt trace form. -/
  pos_re : ∀ X : A, 0 ≤ (tr (star X * X)).re
  /-- Faithfulness of the Hilbert--Schmidt trace form. -/
  pos_re_eq_zero : ∀ X : A, (tr (star X * X)).re = 0 → X = 0

namespace IsTrace

variable (tr : A → ℂ) [IsTrace tr]

/-- Trace of a negated term. -/
lemma neg (X : A) : tr (-X) = - tr X := by
  calc
    tr (-X) = tr ((-1 : ℂ) • X) := by rw [neg_one_smul]
    _ = (-1 : ℂ) * tr X := IsTrace.smul (-1) X
    _ = - tr X := by ring

/-- Trace of a difference. -/
lemma sub (X Y : A) : tr (X - Y) = tr X - tr Y := by
  calc
    tr (X - Y) = tr (X + -Y) := by rw [sub_eq_add_neg]
    _ = tr X + tr (-Y) := IsTrace.add X (-Y)
    _ = tr X + (- tr Y) := by rw [IsTrace.neg tr Y]
    _ = tr X - tr Y := by ring

/-- Trace of a product with a scalar on the right factor. -/
lemma mul_smul_right (X Y : A) (c : ℂ) :
    tr (X * (c • Y)) = c * tr (X * Y) := by
  calc
    tr (X * (c • Y)) = tr (c • (X * Y)) := by rw [mul_smul_comm]
    _ = c * tr (X * Y) := IsTrace.smul c (X * Y)

/-- Trace of a product with a scalar on the left factor. -/
lemma mul_smul_left (X Y : A) (c : ℂ) :
    tr ((c • X) * Y) = c * tr (X * Y) := by
  calc
    tr ((c • X) * Y) = tr (c • (X * Y)) := by rw [smul_mul_assoc]
    _ = c * tr (X * Y) := IsTrace.smul c (X * Y)

/-- Cyclic rotation of a triple product. -/
lemma rotate_three (X Y Z : A) :
    tr (X * (Y * Z)) = tr (Y * Z * X) := by
  calc
    tr (X * (Y * Z)) = tr ((Y * Z) * X) := IsTrace.cyclic X (Y * Z)
    _ = tr (Y * Z * X) := by rw [mul_assoc]

/-- Cyclic rotation of a left-associated triple product. -/
lemma rotate_three_left (X Y Z : A) :
    tr (X * Y * Z) = tr (Y * Z * X) := by
  calc
    tr (X * Y * Z) = tr ((X * Y) * Z) := rfl
    _ = tr (Z * (X * Y)) := IsTrace.cyclic (X * Y) Z
    _ = tr (Z * X * Y) := by rw [mul_assoc]
    _ = tr ((Z * X) * Y) := rfl
    _ = tr (Y * (Z * X)) := IsTrace.cyclic (Z * X) Y
    _ = tr (Y * Z * X) := by rw [mul_assoc]

/-- Trace of a commutator vanishes. -/
lemma trace_commutator (X Y : A) : tr (commutator X Y) = 0 := by
  unfold commutator
  have hcyc : tr (X * Y) = tr (Y * X) := IsTrace.cyclic X Y
  calc
    tr (X * Y - Y * X) = tr (X * Y) - tr (Y * X) := IsTrace.sub tr (X * Y) (Y * X)
    _ = tr (Y * X) - tr (Y * X) := by rw [hcyc]
    _ = 0 := sub_self (tr (Y * X))

/-- Trace of a finite sum. -/
lemma sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    tr (Finset.sum s f) = Finset.sum s (fun i => tr (f i)) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [IsTrace.trace_zero]
  | insert a s ha ih =>
      calc
        tr (Finset.sum (insert a s) f)
            = tr (f a + Finset.sum s f) := by rw [Finset.sum_insert ha]
        _ = tr (f a) + tr (Finset.sum s f) := IsTrace.add (f a) (Finset.sum s f)
        _ = tr (f a) + Finset.sum s (fun i => tr (f i)) := by rw [ih]
        _ = Finset.sum (insert a s) (fun i => tr (f i)) := by
            rw [Finset.sum_insert ha]

end IsTrace

/-- If `L` and `Q` are Hermitian, then `[L,Q]† = -[L,Q]`. -/
lemma star_commutator_of_hermitian
    (L Q : A) (hL : star L = L) (hQ : star Q = Q) :
    star (commutator L Q) = - commutator L Q := by
  unfold commutator
  rw [star_sub, star_mul, star_mul, hL, hQ]
  abel

/-- Trace pairing of the Hamiltonian commutator with `Q` vanishes by cyclicity. -/
lemma trace_hamiltonian_pairing_zero
    (tr : A → ℂ) [IsTrace tr] (Q H : A) :
    tr (Q * (H * Q - Q * H)) = 0 := by
  have h1 : tr (Q * (H * Q)) = tr (H * Q * Q) := by
    calc
      tr (Q * (H * Q)) = tr ((H * Q) * Q) := IsTrace.cyclic Q (H * Q)
      _ = tr (H * Q * Q) := rfl
  have h2 : tr (Q * (Q * H)) = tr (H * Q * Q) := by
    calc
      tr (Q * (Q * H)) = tr ((Q * Q) * H) := by rw [← mul_assoc]
      _ = tr (H * (Q * Q)) := IsTrace.cyclic (Q * Q) H
      _ = tr (H * Q * Q) := by rw [mul_assoc]
  calc
    tr (Q * (H * Q - Q * H)) = tr (Q * (H * Q) - Q * (Q * H)) := by rw [mul_sub]
    _ = tr (Q * (H * Q)) - tr (Q * (Q * H)) := IsTrace.sub tr (Q * (H * Q)) (Q * (Q * H))
    _ = tr (H * Q * Q) - tr (H * Q * Q) := by rw [h1, h2]
    _ = 0 := sub_self (tr (H * Q * Q))

/--
Trace identity for the Hermitian Lindblad adjoint:
`tr(Q D†_L[Q]) = -1/2 tr([L,Q]†[L,Q])`.
-/
theorem trace_lindbladAdjoint_Hermitian
    (tr : A → ℂ) [IsTrace tr]
    (L Q : A) (hL : star L = L) (hQ : star Q = Q) :
    tr (Q * lindbladAdjoint L Q) =
      -((1 / 2 : ℂ) * tr (star (commutator L Q) * commutator L Q)) := by
  let K : A := commutator L Q
  have hKstar : star K = -K := by
    dsimp [K]
    exact star_commutator_of_hermitian L Q hL hQ
  have h_rhs :
      -((1 / 2 : ℂ) * tr (star K * K)) =
        (1 / 2 : ℂ) * tr (K * K) := by
    rw [hKstar, neg_mul]
    rw [IsTrace.neg tr (K * K)]
    ring
  have h_q_lql : tr (Q * (L * Q * L)) = tr (L * Q * L * Q) := by
    calc
      tr (Q * (L * Q * L)) = tr ((L * Q * L) * Q) := IsTrace.cyclic Q (L * Q * L)
      _ = tr (L * Q * L * Q) := rfl
  have h_q_llq : tr (Q * (L * L * Q)) = tr (L * L * Q * Q) := by
    calc
      tr (Q * (L * L * Q)) = tr ((L * L * Q) * Q) := IsTrace.cyclic Q (L * L * Q)
      _ = tr (L * L * Q * Q) := rfl
  have h_q_qll : tr (Q * (Q * (L * L))) = tr (L * L * Q * Q) := by
    calc
      tr (Q * (Q * (L * L))) = tr ((Q * Q) * (L * L)) := by rw [← mul_assoc]
      _ = tr ((L * L) * (Q * Q)) := IsTrace.cyclic (Q * Q) (L * L)
      _ = tr (L * L * Q * Q) := by rw [← mul_assoc (L * L) Q Q]
  have h_lhs :
      tr (Q * lindbladAdjoint L Q) =
        tr (L * Q * L * Q) - (1 / 2 : ℂ) * tr (L * L * Q * Q)
          - (1 / 2 : ℂ) * tr (L * L * Q * Q) := by
    unfold lindbladAdjoint anticommutator
    rw [hL]
    calc
      tr (Q * (L * Q * L - (1 / 2 : ℂ) • (L * L * Q + Q * (L * L)))) =
          tr (Q * (L * Q * L) - Q * ((1 / 2 : ℂ) • (L * L * Q + Q * (L * L)))) := by
            rw [mul_sub]
      _ = tr (Q * (L * Q * L)) -
            tr (Q * ((1 / 2 : ℂ) • (L * L * Q + Q * (L * L)))) :=
            IsTrace.sub tr (Q * (L * Q * L))
              (Q * ((1 / 2 : ℂ) • (L * L * Q + Q * (L * L))))
      _ = tr (Q * (L * Q * L)) -
            (1 / 2 : ℂ) * tr (Q * (L * L * Q + Q * (L * L))) := by
            rw [IsTrace.mul_smul_right tr Q (L * L * Q + Q * (L * L)) (1 / 2 : ℂ)]
      _ = tr (Q * (L * Q * L)) -
            (1 / 2 : ℂ) * (tr (Q * (L * L * Q)) + tr (Q * (Q * (L * L)))) := by
            have hmul : Q * (L * L * Q + Q * (L * L)) =
                Q * (L * L * Q) + Q * (Q * (L * L)) := by
              rw [mul_add]
            have hadd : tr (Q * (L * L * Q) + Q * (Q * (L * L))) =
                tr (Q * (L * L * Q)) + tr (Q * (Q * (L * L))) :=
              IsTrace.add (Q * (L * L * Q)) (Q * (Q * (L * L)))
            rw [hmul, hadd]
      _ = tr (L * Q * L * Q) - (1 / 2 : ℂ) * tr (L * L * Q * Q)
          - (1 / 2 : ℂ) * tr (L * L * Q * Q) := by
            rw [h_q_lql, h_q_llq, h_q_qll]
            ring
  have h_kk :
      tr (K * K) =
        tr (L * Q * L * Q) - tr (L * L * Q * Q)
          - tr (L * L * Q * Q) + tr (L * Q * L * Q) := by
    dsimp [K]
    unfold commutator
    have h_lq_lq : tr ((L * Q) * (L * Q)) = tr (L * Q * L * Q) := by
      rw [← mul_assoc (L * Q) L Q]
    have h_lq_ql : tr ((L * Q) * (Q * L)) = tr (L * L * Q * Q) := by
      calc
        tr ((L * Q) * (Q * L)) = tr (L * Q * Q * L) := by rw [← mul_assoc (L * Q) Q L]
        _ = tr (L * (Q * Q) * L) := by rw [mul_assoc L Q Q]
        _ = tr (L * (L * (Q * Q))) := IsTrace.cyclic (L * (Q * Q)) L
        _ = tr ((L * L) * (Q * Q)) := by rw [← mul_assoc L L (Q * Q)]
        _ = tr (L * L * Q * Q) := by rw [← mul_assoc (L * L) Q Q]
    have h_ql_lq : tr ((Q * L) * (L * Q)) = tr (L * L * Q * Q) := by
      calc
        tr ((Q * L) * (L * Q)) = tr (Q * (L * L * Q)) := by
          rw [← mul_assoc (Q * L) L Q, mul_assoc Q L L, mul_assoc Q (L * L) Q]
        _ = tr (L * L * Q * Q) := h_q_llq
    have h_ql_ql : tr ((Q * L) * (Q * L)) = tr (L * Q * L * Q) := by
      calc
        tr ((Q * L) * (Q * L)) = tr (Q * (L * Q * L)) := by
          rw [← mul_assoc (Q * L) Q L, mul_assoc Q L Q, mul_assoc Q (L * Q) L]
        _ = tr (L * Q * L * Q) := h_q_lql
    calc
      tr ((L * Q - Q * L) * (L * Q - Q * L)) =
          tr (((L * Q) * (L * Q) - (L * Q) * (Q * L)) -
              ((Q * L) * (L * Q) - (Q * L) * (Q * L))) := by
            rw [sub_mul, mul_sub, mul_sub]
      _ = tr ((L * Q) * (L * Q) - (L * Q) * (Q * L)) -
          tr ((Q * L) * (L * Q) - (Q * L) * (Q * L)) :=
            IsTrace.sub tr
              ((L * Q) * (L * Q) - (L * Q) * (Q * L))
              ((Q * L) * (L * Q) - (Q * L) * (Q * L))
      _ = (tr ((L * Q) * (L * Q)) - tr ((L * Q) * (Q * L))) -
          (tr ((Q * L) * (L * Q)) - tr ((Q * L) * (Q * L))) := by
            rw [IsTrace.sub tr ((L * Q) * (L * Q)) ((L * Q) * (Q * L))]
            rw [IsTrace.sub tr ((Q * L) * (L * Q)) ((Q * L) * (Q * L))]
      _ = tr (L * Q * L * Q) - tr (L * L * Q * Q)
          - tr (L * L * Q * Q) + tr (L * Q * L * Q) := by
            rw [h_lq_lq, h_lq_ql, h_ql_lq, h_ql_ql]
            ring
  rw [h_lhs, h_rhs, h_kk]
  ring

/-- The real part of the Hermitian Lindblad trace pairing is non-positive. -/
theorem re_trace_lindbladAdjoint_Hermitian_nonpos
    (tr : A → ℂ) [IsTrace tr]
    (L Q : A) (hL : star L = L) (hQ : star Q = Q) :
    (tr (Q * lindbladAdjoint L Q)).re ≤ 0 := by
  rw [trace_lindbladAdjoint_Hermitian tr L Q hL hQ]
  have hpos : 0 ≤ (tr (star (commutator L Q) * commutator L Q)).re :=
    IsTrace.pos_re (commutator L Q)
  have hhalf : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have hmul : 0 ≤ (1 / 2 : ℝ) * (tr (star (commutator L Q) * commutator L Q)).re :=
    mul_nonneg hhalf hpos
  have hre :
      (-((1 / 2 : ℂ) * tr (star (commutator L Q) * commutator L Q))).re =
        -((1 / 2 : ℝ) * (tr (star (commutator L Q) * commutator L Q)).re) := by
    simp [Complex.mul_re]
  rw [hre]
  linarith

/-- Vanishing real trace pairing forces the Hermitian Lindblad commutator to vanish. -/
theorem commutator_zero_of_re_trace_lindbladAdjoint_zero
    (tr : A → ℂ) [IsTrace tr]
    (L Q : A) (hL : star L = L) (hQ : star Q = Q)
    (htrace_re : (tr (Q * lindbladAdjoint L Q)).re = 0) :
    commutator L Q = 0 := by
  rw [trace_lindbladAdjoint_Hermitian tr L Q hL hQ] at htrace_re
  have hre_expr :
      (-((1 / 2 : ℂ) * tr (star (commutator L Q) * commutator L Q))).re =
        -((1 / 2 : ℝ) * (tr (star (commutator L Q) * commutator L Q)).re) := by
    simp [Complex.mul_re]
  rw [hre_expr] at htrace_re
  have hnorm_re : (tr (star (commutator L Q) * commutator L Q)).re = 0 := by
    nlinarith
  exact IsTrace.pos_re_eq_zero (commutator L Q) hnorm_re

/-- Sum of non-positive real terms equal to zero forces every term to vanish. -/
lemma eq_zero_of_univ_sum_eq_zero_of_nonpos
    {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h_nonpos : ∀ i : ι, f i ≤ 0)
    (h_sum : Finset.univ.sum f = 0) :
    ∀ i : ι, f i = 0 := by
  intro i
  have hnot_lt : ¬ f i < 0 := by
    intro hlt
    have hsum_neg_zero : Finset.univ.sum (fun j : ι => - f j) = 0 := by
      rw [show Finset.univ.sum (fun j : ι => - f j) = - Finset.univ.sum f by simp]
      rw [h_sum, neg_zero]
    have hsum_neg_pos : 0 < Finset.univ.sum (fun j : ι => - f j) := by
      exact Finset.sum_pos' (fun j _ => neg_nonneg.mpr (h_nonpos j))
        ⟨i, Finset.mem_univ i, by linarith⟩
    linarith
  exact le_antisymm (h_nonpos i) (not_lt.mp hnot_lt)


/-- Multiplying a doubled term by one half returns the original term. -/
lemma half_smul_add_self (a : A) : ((1 / 2 : ℂ) • (a + a)) = a := by
  rw [← two_smul ℂ a, smul_smul]
  have h : ((1 / 2 : ℂ) * (2 : ℂ)) = 1 := by
    norm_num
  rw [h, one_smul]

/-- If `L` is self-adjoint and commutes with `O`, then `D†_L[O]=0`. -/
lemma lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm
    (L O : A) (h_self : star L = L) (h_comm : L * O = O * L) :
    lindbladAdjoint L O = 0 := by
  unfold lindbladAdjoint anticommutator
  rw [h_self]
  have h1 : L * O * L = O * L * L := by
    rw [h_comm]
  have h2 : L * L * O = O * L * L := by
    calc
      L * L * O = L * (L * O) := by rw [mul_assoc]
      _ = L * (O * L) := by rw [h_comm]
      _ = (L * O) * L := by rw [← mul_assoc]
      _ = (O * L) * L := by rw [h_comm]
      _ = O * L * L := rfl
  have h3 : O * (L * L) = O * L * L := (mul_assoc O L L).symm
  rw [h1, h2, h3]
  have hhalf : (1 / 2 : ℂ) • (O * L * L + O * L * L) = O * L * L := by
    exact half_smul_add_self (O * L * L)
  rw [hhalf, sub_self]

/--
Local WESH jump `L_x = T(x)^2`.  In the paper, each `T(x)` is a
self-adjoint time-field observable with spectral measure `E_x(dt)`.  The
Section 1 algebraic formalisation uses exactly the part of that spectral
status needed by the WESH generator: self-adjointness is carried explicitly
as hypotheses in theorems that require it, while the continuous spectral
measure itself is not unfolded inside the finite algebraic proof layer.
-/
def localJump {Site : Type*} (T : Site → A) (x : Site) : A :=
  T x ^ 2

/-- Bilocal WESH jump `L_xy = T(x)^2 - T(y)^2`. -/
def bilocalJump {Site : Type*} (T : Site → A) (x y : Site) : A :=
  T x ^ 2 - T y ^ 2

/-- `L_xx = 0`: there is no diagonal bilocal mismatch. -/
theorem bilocalJump_self {Site : Type*} (T : Site → A) (x : Site) :
    bilocalJump T x x = 0 := by
  unfold bilocalJump
  rw [sub_self]

/-- `L_xy = - L_yx`: the bilocal mismatch is antisymmetric. -/
theorem bilocalJump_swap {Site : Type*} (T : Site → A) (x y : Site) :
    bilocalJump T x y = - bilocalJump T y x := by
  unfold bilocalJump
  rw [neg_sub]

/-- Algebraic commutation predicate used for WESH--Noether. -/
def Commutes (X Y : A) : Prop := X * Y = Y * X

/-- T-neutrality: every local time-field operator commutes with the total charge. -/
def TNeutrality {Site : Type*} (T : Site → A) (Q : A) : Prop :=
  ∀ x : Site, Commutes (T x) Q

/-- T-neutrality implies commutation of `T(x)^2` with the total charge. -/
theorem TNeutrality_square {Site : Type*} (T : Site → A) (Q : A)
    (hT : TNeutrality T Q) :
    ∀ x : Site, Commutes (T x ^ 2) Q := by
  intro x
  unfold TNeutrality at hT
  unfold Commutes at hT ⊢
  have hx : T x * Q = Q * T x := hT x
  calc
    (T x ^ 2) * Q = (T x * T x) * Q := by rw [pow_two]
    _ = T x * (T x * Q) := by rw [mul_assoc]
    _ = T x * (Q * T x) := by rw [hx]
    _ = (T x * Q) * T x := by rw [← mul_assoc]
    _ = (Q * T x) * T x := by rw [hx]
    _ = Q * (T x * T x) := by rw [mul_assoc]
    _ = Q * (T x ^ 2) := by rw [pow_two]

/-- T-neutrality implies commutation of the bilocal difference channel. -/
theorem TNeutrality_bilocal {Site : Type*} (T : Site → A) (Q : A)
    (hT : TNeutrality T Q) :
    ∀ x y : Site, Commutes (bilocalJump T x y) Q := by
  intro x y
  unfold bilocalJump Commutes
  have hx : (T x ^ 2) * Q = Q * (T x ^ 2) := TNeutrality_square T Q hT x
  have hy : (T y ^ 2) * Q = Q * (T y ^ 2) := TNeutrality_square T Q hT y
  calc
    (T x ^ 2 - T y ^ 2) * Q = (T x ^ 2) * Q - (T y ^ 2) * Q := by rw [sub_mul]
    _ = Q * (T x ^ 2) - Q * (T y ^ 2) := by rw [hx, hy]
    _ = Q * (T x ^ 2 - T y ^ 2) := by rw [mul_sub]

/-- If `T(x)` is self-adjoint, then the local jump `T(x)^2` is self-adjoint. -/
theorem localJump_selfAdjoint {Site : Type*} (T : Site → A)
    (hT : ∀ x : Site, star (T x) = T x) :
    ∀ x : Site, star (localJump T x) = localJump T x := by
  intro x
  unfold localJump
  rw [star_pow, hT x]

/-- If `T(x)` is self-adjoint, then the bilocal jump is self-adjoint. -/
theorem bilocalJump_selfAdjoint {Site : Type*} (T : Site → A)
    (hT : ∀ x : Site, star (T x) = T x) :
    ∀ x y : Site, star (bilocalJump T x y) = bilocalJump T x y := by
  intro x y
  unfold bilocalJump
  rw [star_sub, star_pow, star_pow, hT x, hT y]

end GenericOperatorAlgebra

/-! ## 3. WESH--Noether adjoint generator -/

section WESHNoether

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Heisenberg adjoint WESH generator for the Section 1 channel set. -/
def WESH_Adjoint_Generator
    (Q H_eff : A) (T : Site → A) (nu : ℝ)
    (gamma C : Site → Site → ℝ) : A :=
  (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff) +
  (nu : ℂ) • (Finset.univ.sum fun x => lindbladAdjoint (localJump T x) Q) +
  Finset.univ.sum (fun x => Finset.univ.sum fun y =>
    ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q)

/-- WESH--Noether condition at generator level. -/
def WESHNoetherCondition
    (Q H_eff : A) (T : Site → A) (nu : ℝ)
    (gamma C : Site → Site → ℝ) : Prop :=
  WESH_Adjoint_Generator Q H_eff T nu gamma C = 0

/--
Sufficiency direction of WESH--Noether used in Section 1:
if the charge commutes with the Hamiltonian and the time-field is T-neutral,
then the WESH adjoint generator annihilates the charge.
-/
theorem WESH_Noether_of_TNeutrality
    (Q H_eff : A) (T : Site → A) (nu : ℝ)
    (gamma C : Site → Site → ℝ)
    (h_comm_H : H_eff * Q = Q * H_eff)
    (h_T_neutral : TNeutrality T Q)
    (h_herm_T : ∀ x : Site, star (T x) = T x) :
    WESHNoetherCondition Q H_eff T nu gamma C := by
  unfold WESHNoetherCondition WESH_Adjoint_Generator
  have hHam : (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff) = 0 := by
    have hzero : H_eff * Q - Q * H_eff = 0 := sub_eq_zero.mpr h_comm_H
    rw [hzero, smul_zero]
  have hLocalPoint : ∀ x : Site, lindbladAdjoint (localJump T x) Q = 0 := by
    intro x
    have hself : star (localJump T x) = localJump T x := localJump_selfAdjoint T h_herm_T x
    have hcomm : localJump T x * Q = Q * localJump T x := TNeutrality_square T Q h_T_neutral x
    exact lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm (localJump T x) Q hself hcomm
  have hLocalSum : Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
    exact Finset.sum_eq_zero fun x _ => hLocalPoint x
  have hLocal :
      (nu : ℂ) • Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
    rw [hLocalSum, smul_zero]
  have hBilocalPoint : ∀ x y : Site, lindbladAdjoint (bilocalJump T x y) Q = 0 := by
    intro x y
    have hself : star (bilocalJump T x y) = bilocalJump T x y :=
      bilocalJump_selfAdjoint T h_herm_T x y
    have hcomm : bilocalJump T x y * Q = Q * bilocalJump T x y :=
      TNeutrality_bilocal T Q h_T_neutral x y
    exact lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm (bilocalJump T x y) Q hself hcomm
  have hBilocalInner :
      ∀ x : Site,
        Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q) = 0 := by
    intro x
    exact Finset.sum_eq_zero fun y _ => by
      rw [hBilocalPoint x y, smul_zero]
  have hBilocal :
      Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q)) = 0 := by
    exact Finset.sum_eq_zero fun x _ => hBilocalInner x
  rw [hHam, hLocal, hBilocal, zero_add, zero_add]

/--
General commutant-sufficiency form of WESH--Noether: if the Hamiltonian,
local jumps, and bilocal jumps commute with the charge, then the adjoint
WESH generator annihilates the charge.
-/
theorem WESH_Noether_of_commutant_conditions
    (Q H_eff : A) (T : Site → A) (nu : ℝ)
    (gamma C : Site → Site → ℝ)
    (h_comm_H : H_eff * Q = Q * H_eff)
    (h_local_self : ∀ x : Site, star (localJump T x) = localJump T x)
    (h_bilocal_self : ∀ x y : Site, star (bilocalJump T x y) = bilocalJump T x y)
    (h_local_comm : ∀ x : Site, localJump T x * Q = Q * localJump T x)
    (h_bilocal_comm : ∀ x y : Site, bilocalJump T x y * Q = Q * bilocalJump T x y) :
    WESHNoetherCondition Q H_eff T nu gamma C := by
  unfold WESHNoetherCondition WESH_Adjoint_Generator
  have hHam : (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff) = 0 := by
    have hzero : H_eff * Q - Q * H_eff = 0 := sub_eq_zero.mpr h_comm_H
    rw [hzero, smul_zero]
  have hLocalPoint : ∀ x : Site, lindbladAdjoint (localJump T x) Q = 0 := by
    intro x
    exact lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm
      (localJump T x) Q (h_local_self x) (h_local_comm x)
  have hLocalSum : Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
    exact Finset.sum_eq_zero fun x _ => hLocalPoint x
  have hLocal :
      (nu : ℂ) • Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
    rw [hLocalSum, smul_zero]
  have hBilocalPoint : ∀ x y : Site, lindbladAdjoint (bilocalJump T x y) Q = 0 := by
    intro x y
    exact lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm
      (bilocalJump T x y) Q (h_bilocal_self x y) (h_bilocal_comm x y)
  have hBilocalInner :
      ∀ x : Site,
        Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q) = 0 := by
    intro x
    exact Finset.sum_eq_zero fun y _ => by
      rw [hBilocalPoint x y, smul_zero]
  have hBilocal :
      Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q)) = 0 := by
    exact Finset.sum_eq_zero fun x _ => hBilocalInner x
  rw [hHam, hLocal, hBilocal, zero_add, zero_add]


/-- Real part of a trace after multiplication by a real scalar cast to `ℂ`. -/
lemma re_ofReal_mul (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
  simp [Complex.mul_re]

/-- Real part commutes with finite sums of complex numbers. -/
lemma re_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (Finset.univ.sum f).re = Finset.univ.sum (fun i => (f i).re) := by
  simp

/--
Real trace balance of the WESH adjoint generator paired with `Q`.  The
Hamiltonian term has zero trace pairing by cyclicity, and the remaining
terms are exactly the local and bilocal dissipative trace pairings.
-/
theorem re_trace_WESH_Adjoint_Generator_balance
    (tr : A → ℂ) [IsTrace tr]
    (Q H_eff : A) (T : Site → A) (nu : ℝ)
    (gamma C : Site → Site → ℝ) :
    (tr (Q * WESH_Adjoint_Generator Q H_eff T nu gamma C)).re =
      nu * Finset.univ.sum (fun x : Site =>
        (tr (Q * lindbladAdjoint (localJump T x) Q)).re) +
      Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
        gamma x y * C x y *
          (tr (Q * lindbladAdjoint (bilocalJump T x y) Q)).re)) := by
  unfold WESH_Adjoint_Generator
  have hHamRe :
      (tr (Q * ((-Complex.I : ℂ) • (H_eff * Q - Q * H_eff)))).re = 0 := by
    rw [IsTrace.mul_smul_right tr Q (H_eff * Q - Q * H_eff) (-Complex.I)]
    rw [trace_hamiltonian_pairing_zero tr Q H_eff]
    norm_num
  have hLocalRe :
      (tr (Q * ((nu : ℂ) •
          (Finset.univ.sum fun x : Site => lindbladAdjoint (localJump T x) Q)))).re =
        nu * Finset.univ.sum (fun x : Site =>
          (tr (Q * lindbladAdjoint (localJump T x) Q)).re) := by
    rw [IsTrace.mul_smul_right tr Q
      (Finset.univ.sum fun x : Site => lindbladAdjoint (localJump T x) Q) (nu : ℂ)]
    rw [Finset.mul_sum]
    rw [IsTrace.sum tr Finset.univ (fun x : Site => Q * lindbladAdjoint (localJump T x) Q)]
    rw [re_ofReal_mul]
    rw [re_sum]
  have hBilocalTrace :
      tr (Q * (Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q)))) =
        Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) *
            tr (Q * lindbladAdjoint (bilocalJump T x y) Q))) := by
    rw [Finset.mul_sum]
    rw [IsTrace.sum tr Finset.univ (fun x : Site =>
      Q * (Finset.univ.sum (fun y : Site =>
        ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q)))]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Finset.mul_sum]
    rw [IsTrace.sum tr Finset.univ (fun y : Site =>
      Q * (((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q))]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [IsTrace.mul_smul_right tr Q (lindbladAdjoint (bilocalJump T x y) Q)
        (((gamma x y * C x y : ℝ) : ℂ))]
  have hBilocalRe :
      (tr (Q * (Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q))))).re =
        Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          gamma x y * C x y *
            (tr (Q * lindbladAdjoint (bilocalJump T x y) Q)).re)) := by
    rw [hBilocalTrace]
    rw [re_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [re_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [re_ofReal_mul]
  let ham : A := (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff)
  let loc : A := (nu : ℂ) •
    (Finset.univ.sum fun x : Site => lindbladAdjoint (localJump T x) Q)
  let bil : A := Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
    ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q))
  have hOuter : tr (Q * (ham + loc + bil)) =
      tr (Q * (ham + loc)) + tr (Q * bil) := by
    calc
      tr (Q * (ham + loc + bil)) = tr (Q * (ham + loc) + Q * bil) := by rw [mul_add]
      _ = tr (Q * (ham + loc)) + tr (Q * bil) :=
        IsTrace.add (Q * (ham + loc)) (Q * bil)
  have hInner : tr (Q * (ham + loc)) = tr (Q * ham) + tr (Q * loc) := by
    calc
      tr (Q * (ham + loc)) = tr (Q * ham + Q * loc) := by rw [mul_add]
      _ = tr (Q * ham) + tr (Q * loc) := IsTrace.add (Q * ham) (Q * loc)
  have hHamRe' : (tr (Q * ham)).re = 0 := by
    dsimp [ham]
    exact hHamRe
  have hLocalRe' : (tr (Q * loc)).re =
      nu * Finset.univ.sum (fun x : Site =>
        (tr (Q * lindbladAdjoint (localJump T x) Q)).re) := by
    dsimp [loc]
    exact hLocalRe
  have hBilocalRe' : (tr (Q * bil)).re =
      Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
        gamma x y * C x y *
          (tr (Q * lindbladAdjoint (bilocalJump T x y) Q)).re)) := by
    dsimp [bil]
    exact hBilocalRe
  change (tr (Q * (ham + loc + bil))).re = _
  rw [hOuter, hInner, Complex.add_re, Complex.add_re]
  rw [hHamRe', hLocalRe', hBilocalRe']
  ring

/--
WESH--Noether biconditional extracted through the faithful trace argument,
with the bilocal commutant required exactly on the active WESH support.

The submitted paper requires bilocal commutation only for channels with
nonzero rate.  Algebraically, this means that local jumps commute for all
labels because `ν > 0`, while bilocal jumps commute only when
`γ(x,y) C(x,y) ≠ 0`.  Inactive bilocal channels vanish from the generator
by their scalar coefficient and therefore impose no commutant condition.
-/
theorem wesh_noether_iff_commutant_conditions_via_trace
    [NoZeroSMulDivisors ℂ A]
    (tr : A → ℂ) [IsTrace tr]
    (Q H_eff : A) (T : Site → A) (nu : ℝ)
    (gamma C : Site → Site → ℝ)
    (h_nu_pos : 0 < nu)
    (h_gamma_nonneg : ∀ x y : Site, 0 ≤ gamma x y)
    (h_C_nonneg : ∀ x y : Site, 0 ≤ C x y)
    (h_herm_Q : star Q = Q)
    (h_herm_T : ∀ x : Site, star (T x) = T x) :
    WESHNoetherCondition Q H_eff T nu gamma C ↔
      (H_eff * Q = Q * H_eff ∧
       (∀ x : Site, localJump T x * Q = Q * localJump T x) ∧
       (∀ x y : Site,
          gamma x y * C x y ≠ 0 →
            bilocalJump T x y * Q = Q * bilocalJump T x y)) := by
  constructor
  · intro h_noether
    have hTraceZero : (tr (Q * WESH_Adjoint_Generator Q H_eff T nu gamma C)).re = 0 := by
      rw [h_noether, mul_zero]
      have htr0 : tr 0 = 0 := IsTrace.trace_zero
      rw [htr0]
      norm_num
    have hBalance := re_trace_WESH_Adjoint_Generator_balance tr Q H_eff T nu gamma C
    rw [hBalance] at hTraceZero
    let localTerm : Site → ℝ := fun x =>
      (tr (Q * lindbladAdjoint (localJump T x) Q)).re
    let bilocalTerm : Site → Site → ℝ := fun x y =>
      (tr (Q * lindbladAdjoint (bilocalJump T x y) Q)).re
    have hLocalNonpos : ∀ x : Site, localTerm x ≤ 0 := by
      intro x
      dsimp [localTerm]
      exact re_trace_lindbladAdjoint_Hermitian_nonpos tr
        (localJump T x) Q (localJump_selfAdjoint T h_herm_T x) h_herm_Q
    have hBilocalNonpos : ∀ x y : Site, bilocalTerm x y ≤ 0 := by
      intro x y
      dsimp [bilocalTerm]
      exact re_trace_lindbladAdjoint_Hermitian_nonpos tr
        (bilocalJump T x y) Q (bilocalJump_selfAdjoint T h_herm_T x y) h_herm_Q
    have hLocalTotalNonpos : nu * Finset.univ.sum localTerm ≤ 0 := by
      have hsum : Finset.univ.sum localTerm ≤ 0 :=
        Finset.sum_nonpos fun x _ => hLocalNonpos x
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_nu_pos) hsum
    have hBilocalWeightedNonpos :
        ∀ x y : Site, gamma x y * C x y * bilocalTerm x y ≤ 0 := by
      intro x y
      have hw_nonneg : 0 ≤ gamma x y * C x y :=
        mul_nonneg (h_gamma_nonneg x y) (h_C_nonneg x y)
      exact mul_nonpos_of_nonneg_of_nonpos hw_nonneg (hBilocalNonpos x y)
    have hBilocalTotalNonpos :
        Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          gamma x y * C x y * bilocalTerm x y)) ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro x _
      refine Finset.sum_nonpos ?_
      intro y _
      exact hBilocalWeightedNonpos x y
    have hBalanceLocalBilocal :
        nu * Finset.univ.sum localTerm +
          Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
            gamma x y * C x y * bilocalTerm x y)) = 0 := by
      dsimp [localTerm, bilocalTerm]
      exact hTraceZero
    have hLocalTotalZero : nu * Finset.univ.sum localTerm = 0 := by
      linarith
    have hBilocalTotalZero :
        Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          gamma x y * C x y * bilocalTerm x y)) = 0 := by
      linarith
    have hLocalSumZero : Finset.univ.sum localTerm = 0 := by
      exact (mul_eq_zero.mp hLocalTotalZero).resolve_left (ne_of_gt h_nu_pos)
    have hLocalTermZero : ∀ x : Site, localTerm x = 0 :=
      eq_zero_of_univ_sum_eq_zero_of_nonpos localTerm hLocalNonpos hLocalSumZero
    have hBilocalInnerNonpos :
        ∀ x : Site, (Finset.univ.sum (fun y : Site =>
          gamma x y * C x y * bilocalTerm x y)) ≤ 0 := by
      intro x
      refine Finset.sum_nonpos ?_
      intro y _
      exact hBilocalWeightedNonpos x y
    have hBilocalInnerZero :
        ∀ x : Site, Finset.univ.sum (fun y : Site =>
          gamma x y * C x y * bilocalTerm x y) = 0 :=
      eq_zero_of_univ_sum_eq_zero_of_nonpos
        (fun x : Site => Finset.univ.sum (fun y : Site =>
          gamma x y * C x y * bilocalTerm x y))
        hBilocalInnerNonpos hBilocalTotalZero
    have hBilocalActiveTermZero :
        ∀ x y : Site, gamma x y * C x y ≠ 0 → bilocalTerm x y = 0 := by
      intro x y hactive
      have hWeightedZero : gamma x y * C x y * bilocalTerm x y = 0 :=
        eq_zero_of_univ_sum_eq_zero_of_nonpos
          (fun y : Site => gamma x y * C x y * bilocalTerm x y)
          (fun y => hBilocalWeightedNonpos x y)
          (hBilocalInnerZero x) y
      exact (mul_eq_zero.mp hWeightedZero).resolve_left hactive
    have hLocalComm : ∀ x : Site, localJump T x * Q = Q * localJump T x := by
      intro x
      have hcomm0 : commutator (localJump T x) Q = 0 :=
        commutator_zero_of_re_trace_lindbladAdjoint_zero tr
          (localJump T x) Q (localJump_selfAdjoint T h_herm_T x) h_herm_Q
          (hLocalTermZero x)
      unfold commutator at hcomm0
      exact sub_eq_zero.mp hcomm0
    have hBilocalCommActive :
        ∀ x y : Site,
          gamma x y * C x y ≠ 0 →
            bilocalJump T x y * Q = Q * bilocalJump T x y := by
      intro x y hactive
      have hcomm0 : commutator (bilocalJump T x y) Q = 0 :=
        commutator_zero_of_re_trace_lindbladAdjoint_zero tr
          (bilocalJump T x y) Q (bilocalJump_selfAdjoint T h_herm_T x y) h_herm_Q
          (hBilocalActiveTermZero x y hactive)
      unfold commutator at hcomm0
      exact sub_eq_zero.mp hcomm0
    have hLocalPointZero : ∀ x : Site, lindbladAdjoint (localJump T x) Q = 0 := by
      intro x
      exact lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm
        (localJump T x) Q (localJump_selfAdjoint T h_herm_T x) (hLocalComm x)
    have hLocalSumZeroA :
        Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
      exact Finset.sum_eq_zero fun x _ => hLocalPointZero x
    have hLocalA :
        (nu : ℂ) • Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
      rw [hLocalSumZeroA, smul_zero]
    have hBilocalInnerZeroA :
        ∀ x : Site, Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q) = 0 := by
      intro x
      exact Finset.sum_eq_zero fun y _ => by
        by_cases hactive : gamma x y * C x y ≠ 0
        · have hcomm : bilocalJump T x y * Q = Q * bilocalJump T x y :=
            hBilocalCommActive x y hactive
          have hzero : lindbladAdjoint (bilocalJump T x y) Q = 0 :=
            lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm
              (bilocalJump T x y) Q (bilocalJump_selfAdjoint T h_herm_T x y) hcomm
          rw [hzero, smul_zero]
        · have hprod0 : gamma x y * C x y = 0 := by
            by_contra hne
            exact hactive hne
          rw [hprod0]
          simp
    have hBilocalA :
        Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q)) = 0 := by
      exact Finset.sum_eq_zero fun x _ => hBilocalInnerZeroA x
    have hGenH : WESH_Adjoint_Generator Q H_eff T nu gamma C =
        (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff) := by
      unfold WESH_Adjoint_Generator
      rw [hLocalA, hBilocalA, add_zero, add_zero]
    have hHtermZero : (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff) = 0 := by
      rw [← hGenH]
      exact h_noether
    have hHdiffZero : H_eff * Q - Q * H_eff = 0 := by
      have hsplit := smul_eq_zero.mp hHtermZero
      cases hsplit with
      | inl hscalar =>
          norm_num at hscalar
      | inr hzero =>
          exact hzero
    refine ⟨sub_eq_zero.mp hHdiffZero, hLocalComm, hBilocalCommActive⟩
  · rintro ⟨h_comm_H, h_local_comm, h_bilocal_comm_active⟩
    unfold WESHNoetherCondition WESH_Adjoint_Generator
    have hHam : (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff) = 0 := by
      have hzero : H_eff * Q - Q * H_eff = 0 := sub_eq_zero.mpr h_comm_H
      rw [hzero, smul_zero]
    have hLocalPoint : ∀ x : Site, lindbladAdjoint (localJump T x) Q = 0 := by
      intro x
      exact lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm
        (localJump T x) Q (localJump_selfAdjoint T h_herm_T x) (h_local_comm x)
    have hLocalSum : Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
      exact Finset.sum_eq_zero fun x _ => hLocalPoint x
    have hLocal :
        (nu : ℂ) • Finset.univ.sum (fun x : Site => lindbladAdjoint (localJump T x) Q) = 0 := by
      rw [hLocalSum, smul_zero]
    have hBilocalInner :
        ∀ x : Site,
          Finset.univ.sum (fun y : Site =>
            ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q) = 0 := by
      intro x
      exact Finset.sum_eq_zero fun y _ => by
        by_cases hactive : gamma x y * C x y ≠ 0
        · have hcomm : bilocalJump T x y * Q = Q * bilocalJump T x y :=
            h_bilocal_comm_active x y hactive
          have hzero : lindbladAdjoint (bilocalJump T x y) Q = 0 :=
            lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm
              (bilocalJump T x y) Q (bilocalJump_selfAdjoint T h_herm_T x y) hcomm
          rw [hzero, smul_zero]
        · have hprod0 : gamma x y * C x y = 0 := by
            by_contra hne
            exact hactive hne
          rw [hprod0]
          simp
    have hBilocal :
        Finset.univ.sum (fun x : Site => Finset.univ.sum (fun y : Site =>
          ((gamma x y * C x y : ℝ) : ℂ) • lindbladAdjoint (bilocalJump T x y) Q)) = 0 := by
      exact Finset.sum_eq_zero fun x _ => hBilocalInner x
    rw [hHam, hLocal, hBilocal, zero_add, zero_add]

/--
Full-support corollary of the active-support WESH--Noether biconditional.
If every bilocal scalar weight is strictly positive, the active-support
condition reduces to commutation of all bilocal jumps.
-/
theorem wesh_noether_iff_full_support_commutant_conditions_via_trace
    [NoZeroSMulDivisors ℂ A]
    (tr : A → ℂ) [IsTrace tr]
    (Q H_eff : A) (T : Site → A) (nu : ℝ)
    (gamma C : Site → Site → ℝ)
    (h_nu_pos : 0 < nu)
    (h_gamma_pos : ∀ x y : Site, 0 < gamma x y)
    (h_C_pos : ∀ x y : Site, 0 < C x y)
    (h_herm_Q : star Q = Q)
    (h_herm_T : ∀ x : Site, star (T x) = T x) :
    WESHNoetherCondition Q H_eff T nu gamma C ↔
      (H_eff * Q = Q * H_eff ∧
       (∀ x : Site, localJump T x * Q = Q * localJump T x) ∧
       (∀ x y : Site, bilocalJump T x y * Q = Q * bilocalJump T x y)) := by
  have hActive := wesh_noether_iff_commutant_conditions_via_trace
    tr Q H_eff T nu gamma C h_nu_pos
    (fun x y => le_of_lt (h_gamma_pos x y))
    (fun x y => le_of_lt (h_C_pos x y))
    h_herm_Q h_herm_T
  constructor
  · intro h
    obtain ⟨hH, hLoc, hBiActive⟩ := hActive.mp h
    refine ⟨hH, hLoc, ?_⟩
    intro x y
    have hWeight : gamma x y * C x y ≠ 0 :=
      ne_of_gt (mul_pos (h_gamma_pos x y) (h_C_pos x y))
    exact hBiActive x y hWeight
  · intro h
    exact hActive.mpr ⟨h.1, h.2.1, fun x y _ => h.2.2 x y⟩
/--
Path independence in the form used by the paper: if the Heisenberg adjoint
annihilates the charge, then the charge-velocity pairing with every state is zero.
-/
theorem WESH_path_independence_from_noether
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q H_eff : Matrix n n ℂ) (T : Site → Matrix n n ℂ) (nu : ℝ)
    (gamma C : Site → Site → ℝ) (rho : Matrix n n ℂ)
    (h_noether : WESHNoetherCondition Q H_eff T nu gamma C) :
    Matrix.trace (WESH_Adjoint_Generator Q H_eff T nu gamma C * rho) = 0 := by
  unfold WESHNoetherCondition at h_noether
  rw [h_noether]
  simp

/-- Path independence obtained directly from T-neutrality. -/
theorem WESH_path_independence_of_TNeutrality
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q H_eff : Matrix n n ℂ) (T : Site → Matrix n n ℂ) (nu : ℝ)
    (gamma C : Site → Site → ℝ) (rho : Matrix n n ℂ)
    (h_comm_H : H_eff * Q = Q * H_eff)
    (h_T_neutral : TNeutrality T Q)
    (h_herm_T : ∀ x : Site, star (T x) = T x) :
    Matrix.trace (WESH_Adjoint_Generator Q H_eff T nu gamma C * rho) = 0 := by
  apply WESH_path_independence_from_noether
  exact WESH_Noether_of_TNeutrality Q H_eff T nu gamma C h_comm_H h_T_neutral h_herm_T

end WESHNoether

/-! ## 4. Unraveling-level CPT and quadratic dissipator selection -/

section QuadraticSelection

/-- Index `n` of an even local jump `F(T) ~ T^{2n}` with `n ≥ 1`. -/
structure DissipatorIndex where
  n : ℕ
  positive : 1 ≤ n

/-- Local jump degree selected by unraveling-level CPT: `2n`. -/
def dissipator_degree (idx : DissipatorIndex) : ℕ :=
  2 * idx.n

/-- The degree selected by unraveling-level CPT is even. -/
theorem dissipator_degree_even (idx : DissipatorIndex) :
    Even (dissipator_degree idx) := by
  unfold dissipator_degree
  exact even_two_mul idx.n

/-- Coherence-time exponent associated with `T^{2n}`. -/
def coherence_exponent (idx : DissipatorIndex) : ℕ :=
  2 * idx.n

/-- Section 1 collective-stability target exponent. -/
def collective_stability_exponent : ℕ :=
  2

/-- Collective stability `N²` fixes `n=1`. -/
theorem quadratic_selection (idx : DissipatorIndex)
    (h_stable : coherence_exponent idx = collective_stability_exponent) :
    idx.n = 1 := by
  unfold coherence_exponent collective_stability_exponent at h_stable
  omega

/-- Therefore the selected local jump degree is quadratic. -/
theorem stable_dissipator_is_quadratic (idx : DissipatorIndex)
    (h_stable : coherence_exponent idx = collective_stability_exponent) :
    dissipator_degree idx = 2 := by
  unfold dissipator_degree
  rw [quadratic_selection idx h_stable]

end QuadraticSelection

/-! ## 4a. Real-valued stability exponent form -/

section QuadraticSelectionReal

/-- Real-valued target exponent used in the scaling discussion. -/
def stability_exponent_real : ℝ := 2

/-- Real-valued coherence exponent corresponding to `T^{2n}`. -/
def coherence_exponent_real (idx : DissipatorIndex) : ℝ := 2 * idx.n

/-- Real-valued selection: `2n = 2` again fixes `n = 1`. -/
theorem quadratic_selection_real (idx : DissipatorIndex)
    (h_stable : coherence_exponent_real idx = stability_exponent_real) :
    idx.n = 1 := by
  unfold coherence_exponent_real stability_exponent_real at h_stable
  have h_as_real : (idx.n : ℝ) = 1 := by
    linarith
  exact_mod_cast h_as_real

/-- The real-valued stability condition also gives a quadratic degree. -/
theorem stable_dissipator_is_quadratic_real (idx : DissipatorIndex)
    (h_stable : coherence_exponent_real idx = stability_exponent_real) :
    dissipator_degree idx = 2 := by
  unfold dissipator_degree
  rw [quadratic_selection_real idx h_stable]

end QuadraticSelectionReal


/-! ## 5. WESH master equation and Nξ-local support -/

section MasterEquation

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Dimensionless field `T̃(x)=τ_s^{-1}T(x)`. -/
def T_tilde (T : Site → A) (tau_s : ℝ) (x : Site) : A :=
  (1 / tau_s : ℂ) • T x

/-- Local jump in dimensionless units. -/
def L_local (T : Site → A) (tau_s : ℝ) (x : Site) : A :=
  T_tilde T tau_s x ^ 2

/-- Bilocal jump in dimensionless units. -/
def L_bilocal (T : Site → A) (tau_s : ℝ) (x y : Site) : A :=
  T_tilde T tau_s x ^ 2 - T_tilde T tau_s y ^ 2

/-- Diagonal bilocal jump vanishes. -/
theorem L_bilocal_self (T : Site → A) (tau_s : ℝ) (x : Site) :
    L_bilocal T tau_s x x = 0 := by
  unfold L_bilocal
  rw [sub_self]

/-- Bilocal dimensionless jump is antisymmetric. -/
theorem L_bilocal_swap (T : Site → A) (tau_s : ℝ) (x y : Site) :
    L_bilocal T tau_s x y = - L_bilocal T tau_s y x := by
  unfold L_bilocal
  rw [neg_sub]

/-- WESH master-equation right-hand side in Section 1 notation. -/
def WESH_MasterEquation
    (ρ H_eff : A) (T : Site → A) (tau_s : ℝ) (nu : ℝ)
    (gamma C : Site → Site → ℝ) : A :=
  let hamiltonianTerm : A := (-Complex.I : ℂ) • (H_eff * ρ - ρ * H_eff)
  let localTerm : A :=
    (nu : ℂ) • (Finset.univ.sum fun x => lindblad (L_local T tau_s x) ρ)
  let bilocalTerm : A :=
    Finset.univ.sum fun x => Finset.univ.sum fun y =>
      ((gamma x y * C x y : ℝ) : ℂ) • lindblad (L_bilocal T tau_s x y) ρ
  hamiltonianTerm + localTerm + bilocalTerm

/-- A bilocal master-equation coefficient vanishes outside `Nξ`. -/
theorem WESH_bilocal_coefficient_outside_Nxi_vanishes
    (gamma0 Ntot : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (C : Site → Site → ℝ)
    (x y : Site) (h_not : ¬ G.Nxi x y) :
    WESH_gamma_kernel gamma0 Ntot Kxi G x y * C x y = 0 := by
  rw [WESH_gamma_outside_Nxi_vanishes gamma0 Ntot Kxi G x y h_not]
  rw [zero_mul]

/-- Observable commutation with a local time field at one site. -/
def CommutesWithTAt (O : A) (T : Site → A) (w : Site) : Prop :=
  O * T w = T w * O ∧ O * (T w ^ 2) = (T w ^ 2) * O

/-- Algebraic Nξ-local no-signaling statement for a bilocal Heisenberg term. -/
theorem WESH_NoSignaling_Nxi_Heisenberg
    (O : A) (T : Site → A) (G : PreGeometricGraph Site) (z : Site)
    (h_herm_T : ∀ w : Site, star (T w) = T w)
    (h_comm_outside : ∀ w : Site, ¬ G.Nxi z w → ¬ G.Nxi w z → CommutesWithTAt O T w)
    (x y : Site)
    (h_x_outside : ¬ G.Nxi z x ∧ ¬ G.Nxi x z)
    (h_y_outside : ¬ G.Nxi z y ∧ ¬ G.Nxi y z) :
    lindbladAdjoint (bilocalJump T x y) O = 0 := by
  have hx : CommutesWithTAt O T x := h_comm_outside x h_x_outside.1 h_x_outside.2
  have hy : CommutesWithTAt O T y := h_comm_outside y h_y_outside.1 h_y_outside.2
  have hx2 : (T x ^ 2) * O = O * (T x ^ 2) := Eq.symm hx.2
  have hy2 : (T y ^ 2) * O = O * (T y ^ 2) := Eq.symm hy.2
  have hcomm : bilocalJump T x y * O = O * bilocalJump T x y := by
    unfold bilocalJump
    rw [sub_mul, mul_sub, hx2, hy2]
  have hself : star (bilocalJump T x y) = bilocalJump T x y :=
    bilocalJump_selfAdjoint T h_herm_T x y
  exact lindbladAdjoint_eq_zero_of_selfAdjoint_of_comm (bilocalJump T x y) O hself hcomm

end MasterEquation

/-! ## 6. Canonical time-field structure -/

section CCR

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {Site : Type*} [DecidableEq Site]

/-- Minisuperspace canonical commutation relation `[T,P_T]=iℏ`. -/
def Minisuperspace_CCR (T P_T : A) (hbar : ℝ) : Prop :=
  T * P_T - P_T * T = (Complex.I * (hbar : ℂ)) • (1 : A)

/-- Minisuperspace total Hamiltonian `H_tot=H_universe+P_T`. -/
def Minisuperspace_Htot (H_universe P_T : A) : A :=
  H_universe + P_T

/-- If the universe Hamiltonian commutes with `T`, then `H_tot` generates the CCR. -/
theorem Minisuperspace_Time_Commutator
    (T P_T H_universe : A) (hbar : ℝ)
    (h_ccr : Minisuperspace_CCR T P_T hbar)
    (h_comm : T * H_universe = H_universe * T) :
    let H_tot := Minisuperspace_Htot H_universe P_T
    T * H_tot - H_tot * T = (Complex.I * (hbar : ℂ)) • (1 : A) := by
  dsimp [Minisuperspace_Htot]
  have hsplit :
      T * (H_universe + P_T) - (H_universe + P_T) * T =
        (T * H_universe - H_universe * T) + (T * P_T - P_T * T) := by
    rw [mul_add, add_mul]
    exact add_sub_add_comm (T * H_universe) (T * P_T) (H_universe * T) (P_T * T)
  rw [hsplit]
  have hzero : T * H_universe - H_universe * T = 0 := sub_eq_zero.mpr h_comm
  rw [hzero, zero_add]
  exact h_ccr

/-- Local time-field CCR on an arbitrary kinematical label slice. -/
def Local_CCR (T Pi_T : Site → A) (hbar : ℝ) : Prop :=
  ∀ x y : Site,
    T x * Pi_T y - Pi_T y * T x =
      if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0

/-- Constraint-surface identification `Π_T(x)=-H(x)`. -/
def Local_Momentum_Identification (Pi_T H_cal : Site → A) : Prop :=
  ∀ x : Site, Pi_T x = - H_cal x

/-- Local Hamiltonian density becomes conjugate to the time field. -/
theorem Local_Time_Translation_Generator
    (T Pi_T H_cal : Site → A) (hbar : ℝ)
    (h_ccr : Local_CCR T Pi_T hbar)
    (h_ident : Local_Momentum_Identification Pi_T H_cal) :
    ∀ x y : Site,
      T x * H_cal y - H_cal y * T x =
        if x = y then -((Complex.I * (hbar : ℂ)) • (1 : A)) else 0 := by
  intro x y
  have h0 :
      T x * Pi_T y - Pi_T y * T x =
        if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0 := h_ccr x y
  have hy : Pi_T y = - H_cal y := h_ident y
  rw [hy] at h0
  have hneg : T x * (-H_cal y) - (-H_cal y) * T x =
      - (T x * H_cal y - H_cal y * T x) := by
    rw [mul_neg, neg_mul, sub_eq_add_neg, neg_neg, sub_eq_add_neg, neg_add, neg_neg]
  rw [hneg] at h0
  have hmain : T x * H_cal y - H_cal y * T x =
      - (if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0) := by
    exact (neg_eq_iff_eq_neg).1 h0
  by_cases hxy : x = y
  · rw [if_pos hxy] at hmain
    rw [if_pos hxy]
    exact hmain
  · rw [if_neg hxy] at hmain
    rw [neg_zero] at hmain
    rw [if_neg hxy]
    exact hmain

end CCR

/-! ## 7. Rényi-2 entanglement gate -/

section RenyiGate

/-- Positive part `[u]_+`. -/
def positive_part (u : ℝ) : ℝ :=
  max 0 u

/-- Unnormalized Rényi-2 WESH gate used in the submitted manuscript. -/
def Renyi2Gate (P_xy P_x P_y : ℝ) : ℝ :=
  positive_part (P_xy - P_x * P_y)

/-- The Rényi-2 gate is non-negative. -/
theorem Renyi2Gate_nonneg (P_xy P_x P_y : ℝ) :
    0 ≤ Renyi2Gate P_xy P_x P_y := by
  unfold Renyi2Gate positive_part
  exact le_max_left 0 (P_xy - P_x * P_y)

/-- Under purity bounds, the unnormalized gate is bounded above by one. -/
theorem Renyi2Gate_le_one
    (P_xy P_x P_y : ℝ)
    (hPxy_le : P_xy ≤ 1)
    (hPx_nonneg : 0 ≤ P_x)
    (hPy_nonneg : 0 ≤ P_y) :
    Renyi2Gate P_xy P_x P_y ≤ 1 := by
  unfold Renyi2Gate positive_part
  have hprod_nonneg : 0 ≤ P_x * P_y := mul_nonneg hPx_nonneg hPy_nonneg
  have hdiff_le : P_xy - P_x * P_y ≤ 1 := by
    have h_le_pxy : P_xy - P_x * P_y ≤ P_xy := sub_le_self P_xy hprod_nonneg
    exact le_trans h_le_pxy hPxy_le
  exact max_le (by norm_num) hdiff_le

/-- If `P_xy < 1`, the gate is strictly less than one. -/
theorem Renyi2Gate_lt_one
    (P_xy P_x P_y : ℝ)
    (hPxy_lt : P_xy < 1)
    (hPx_nonneg : 0 ≤ P_x)
    (hPy_nonneg : 0 ≤ P_y) :
    Renyi2Gate P_xy P_x P_y < 1 := by
  unfold Renyi2Gate positive_part
  have hprod_nonneg : 0 ≤ P_x * P_y := mul_nonneg hPx_nonneg hPy_nonneg
  have hdiff_lt : P_xy - P_x * P_y < 1 := by
    have h_le_pxy : P_xy - P_x * P_y ≤ P_xy := sub_le_self P_xy hprod_nonneg
    exact lt_of_le_of_lt h_le_pxy hPxy_lt
  exact max_lt (by norm_num) hdiff_lt

/-- Product reductions have zero WESH gate when `P_xy=P_x P_y`. -/
theorem Renyi2Gate_product_zero (P_x P_y : ℝ) :
    Renyi2Gate (P_x * P_y) P_x P_y = 0 := by
  unfold Renyi2Gate positive_part
  rw [sub_self]
  norm_num

end RenyiGate

/-! ## 8. Eigentime production functional -/

section Gamma

open MeasureTheory intervalIntegral Real

variable {Site : Type*} [Fintype Site]

/--
Finite-sum version of the time-production functional Γ.  The functions
`localTrace` and `bilocalTrace` denote the real trace contributions appearing
in the local and bilocal terms of Section 1.
-/
def Gamma_functional
    (localTrace : Site → ℝ)
    (bilocalTrace : Site → Site → ℝ)
    (nu tau_Eig : ℝ)
    (gamma C : Site → Site → ℝ) : ℝ :=
  let localTerm := nu * Finset.univ.sum localTrace
  let bilocalTerm := Finset.univ.sum fun x : Site => Finset.univ.sum fun y : Site =>
    gamma x y * C x y * bilocalTrace x y
  tau_Eig * (localTerm + bilocalTerm)

/-- Non-negativity of Γ from non-negative rates, gates, and trace contributions. -/
theorem Gamma_nonneg
    (localTrace : Site → ℝ)
    (bilocalTrace : Site → Site → ℝ)
    (nu tau_Eig : ℝ)
    (gamma C : Site → Site → ℝ)
    (h_local : ∀ x : Site, 0 ≤ localTrace x)
    (h_bilocal : ∀ x y : Site, 0 ≤ bilocalTrace x y)
    (h_nu : 0 ≤ nu)
    (h_tau : 0 ≤ tau_Eig)
    (h_gamma : ∀ x y : Site, 0 ≤ gamma x y)
    (h_C : ∀ x y : Site, 0 ≤ C x y) :
    0 ≤ Gamma_functional localTrace bilocalTrace nu tau_Eig gamma C := by
  unfold Gamma_functional
  refine mul_nonneg h_tau ?_
  refine add_nonneg ?_ ?_
  · exact mul_nonneg h_nu (Finset.sum_nonneg fun x _ => h_local x)
  · refine Finset.sum_nonneg ?_
    intro x _
    refine Finset.sum_nonneg ?_
    intro y _
    exact mul_nonneg (mul_nonneg (h_gamma x y) (h_C x y)) (h_bilocal x y)

/-- Strict positivity of Γ from a positive local contribution. -/
theorem Gamma_pos_of_local_active
    [Nonempty Site]
    (localTrace : Site → ℝ)
    (bilocalTrace : Site → Site → ℝ)
    (nu tau_Eig : ℝ)
    (gamma C : Site → Site → ℝ)
    (x0 : Site)
    (h_local_nonneg : ∀ x : Site, 0 ≤ localTrace x)
    (h_local_pos : 0 < localTrace x0)
    (h_bilocal : ∀ x y : Site, 0 ≤ bilocalTrace x y)
    (h_nu : 0 < nu)
    (h_tau : 0 < tau_Eig)
    (h_gamma : ∀ x y : Site, 0 ≤ gamma x y)
    (h_C : ∀ x y : Site, 0 ≤ C x y) :
    0 < Gamma_functional localTrace bilocalTrace nu tau_Eig gamma C := by
  unfold Gamma_functional
  have hsum_local : 0 < Finset.univ.sum localTrace := by
    exact Finset.sum_pos' (fun x _ => h_local_nonneg x)
      ⟨x0, Finset.mem_univ x0, h_local_pos⟩
  have hlocal_term : 0 < nu * Finset.univ.sum localTrace := mul_pos h_nu hsum_local
  have hbilocal_nonneg :
      0 ≤ Finset.univ.sum (fun x : Site => Finset.univ.sum fun y : Site =>
        gamma x y * C x y * bilocalTrace x y) := by
    refine Finset.sum_nonneg ?_
    intro x _
    refine Finset.sum_nonneg ?_
    intro y _
    exact mul_nonneg (mul_nonneg (h_gamma x y) (h_C x y)) (h_bilocal x y)
  have hinside : 0 < nu * Finset.univ.sum localTrace +
      Finset.univ.sum (fun x : Site => Finset.univ.sum fun y : Site =>
        gamma x y * C x y * bilocalTrace x y) := add_pos_of_pos_of_nonneg hlocal_term hbilocal_nonneg
  exact mul_pos h_tau hinside

/-- Local hazard associated with a local trace contribution. -/
def local_hazard (nu : ℝ) (localTraceAtX : ℝ) : ℝ :=
  nu * localTraceAtX

/-- Local hazard is non-negative under non-negative rate and trace contribution. -/
theorem local_hazard_nonneg (nu localTraceAtX : ℝ)
    (hnu : 0 ≤ nu) (htrace : 0 ≤ localTraceAtX) :
    0 ≤ local_hazard nu localTraceAtX := by
  unfold local_hazard
  exact mul_nonneg hnu htrace

/-- Survival probability after an integrated positive eigentime intensity. -/
def eigentime_survival (integratedIntensity tau_Eig : ℝ) : ℝ :=
  Real.exp (-(integratedIntensity / tau_Eig))

/-- Positive integrated intensity gives non-trivial eigentime activation. -/
theorem eigentime_activation_from_positive_integrated_intensity
    (integratedIntensity tau_Eig : ℝ)
    (hI : 0 < integratedIntensity)
    (hTau : 0 < tau_Eig) :
    eigentime_survival integratedIntensity tau_Eig < 1 := by
  unfold eigentime_survival
  have hdiv : 0 < integratedIntensity / tau_Eig := div_pos hI hTau
  have hneg : -(integratedIntensity / tau_Eig) < 0 := by
    linarith
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hneg


/-- Integrated eigentime intensity appearing in the survival probability. -/
def eigentime_integrated_intensity
    (Gamma : ℝ → ℝ) (tau_Eig s0 delta : ℝ) : ℝ :=
  intervalIntegral (fun s : ℝ => Gamma s / tau_Eig) s0 (s0 + delta) MeasureTheory.volume

/-- Survival probability written directly from the integrated intensity. -/
def eigentime_survival_from_integral
    (Gamma : ℝ → ℝ) (tau_Eig s0 delta : ℝ) : ℝ :=
  Real.exp (-(eigentime_integrated_intensity Gamma tau_Eig s0 delta))

/-- Positive integrated intensity gives non-trivial eigentime activation. -/
theorem eigentime_activation_from_positive_integral
    (Gamma : ℝ → ℝ) (tau_Eig s0 delta : ℝ)
    (hI : 0 < eigentime_integrated_intensity Gamma tau_Eig s0 delta) :
    eigentime_survival_from_integral Gamma tau_Eig s0 delta < 1 := by
  unfold eigentime_survival_from_integral
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

end Gamma



/-! ## 8a. Constraint closure of the Section 1 WESH structure -/

section ConstraintClosure

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/--
Aggregated constraint-closure consequences theorem for the Section 1 WESH generator.

This theorem collects the formal consequences corresponding to the paper's
constraint-led selection.  It is intentionally not a formalisation of the full
space of all admissible generators; instead it bundles the proved consequences
that Section 1 uses from the constraint ledger: unraveling-level CPT plus collective stability fixes
the quadratic local degree; T-neutral closed-universe conservation gives
WESH--Noether; finite-range pre-geometric locality kills the bilocal coefficient
outside `Nξ`; product reductions have zero Rényi-2 gate; and non-negative
rates/gates/trace contributions give non-negative eigentime production.
-/
theorem wesh_constraint_closure_consequences
    (idx : DissipatorIndex)
    (Q H_eff : A) (T : Site → A)
    (nu tau_Eig : ℝ) (gamma C : Site → Site → ℝ)
    (gamma0 Ntot : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (x y : Site)
    (P_x P_y : ℝ)
    (localTrace : Site → ℝ)
    (bilocalTrace : Site → Site → ℝ)
    (h_stable : coherence_exponent idx = collective_stability_exponent)
    (h_comm_H : H_eff * Q = Q * H_eff)
    (h_T_neutral : TNeutrality T Q)
    (h_herm_T : ∀ z : Site, star (T z) = T z)
    (h_not_Nxi : ¬ G.Nxi x y)
    (h_local : ∀ z : Site, 0 ≤ localTrace z)
    (h_bilocal : ∀ u v : Site, 0 ≤ bilocalTrace u v)
    (h_nu : 0 ≤ nu)
    (h_tau : 0 ≤ tau_Eig)
    (h_gamma : ∀ u v : Site, 0 ≤ gamma u v)
    (h_C : ∀ u v : Site, 0 ≤ C u v) :
    dissipator_degree idx = 2 ∧
    WESHNoetherCondition Q H_eff T nu gamma C ∧
    WESH_gamma_kernel gamma0 Ntot Kxi G x y = 0 ∧
    WESH_gamma_kernel gamma0 Ntot Kxi G x y * C x y = 0 ∧
    Renyi2Gate (P_x * P_y) P_x P_y = 0 ∧
    0 ≤ Gamma_functional localTrace bilocalTrace nu tau_Eig gamma C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stable_dissipator_is_quadratic idx h_stable
  · exact WESH_Noether_of_TNeutrality Q H_eff T nu gamma C h_comm_H h_T_neutral h_herm_T
  · exact WESH_gamma_outside_Nxi_vanishes gamma0 Ntot Kxi G x y h_not_Nxi
  · exact WESH_bilocal_coefficient_outside_Nxi_vanishes gamma0 Ntot Kxi G C x y h_not_Nxi
  · exact Renyi2Gate_product_zero P_x P_y
  · exact Gamma_nonneg localTrace bilocalTrace nu tau_Eig gamma C
      h_local h_bilocal h_nu h_tau h_gamma h_C

/--
Cardinality-bound version of the finite-range locality component in the
constraint closure: with `N = card(Site)`, the bilocal coefficient still
vanishes outside the pre-geometric neighbourhood.
-/
theorem wesh_constraint_closure_consequences_cardinality_locality
    (gamma0 : ℝ) (Kxi : Site → Site → ℝ)
    (G : PreGeometricGraph Site) (C : Site → Site → ℝ)
    (x y : Site) (h_not_Nxi : ¬ G.Nxi x y) :
    WESH_gamma_kernel_card gamma0 Kxi G x y = 0 ∧
    WESH_gamma_kernel_card gamma0 Kxi G x y * C x y = 0 := by
  have hker : WESH_gamma_kernel_card gamma0 Kxi G x y = 0 :=
    WESH_gamma_kernel_card_outside_Nxi_vanishes gamma0 Kxi G x y h_not_Nxi
  refine ⟨hker, ?_⟩
  rw [hker, zero_mul]

end ConstraintClosure

/-! ## 9. Collective stability and α = 2 -/

section CollectiveScaling

open Real

/-- Effective coarse-grained dissipative rate under the WESH `N^{-2}` law:
`λ_eff(N) = γ₀ Vξ / N²`. -/
def lambda_eff_N (gamma0 Vxi N : ℝ) : ℝ :=
  gamma0 * Vxi / N ^ 2

/-- Effective eigentime spacing associated with `λ_eff(N)`.  This is the
paper-level expression `τ_Eig_eff(N)=N²/(γ₀Vξ)`, i.e. the inverse of the
coarse-grained rate on the positive parameter domain. -/
def tau_Eig_eff_N (gamma0 Vxi N : ℝ) : ℝ :=
  N ^ 2 / (gamma0 * Vxi)

/-- Dimensionless finite-memory parameter
`μ(N)=τ_corr/τ_Eig_eff(N)`. -/
def mu_finite_memory_N (tau_corr gamma0 Vxi N : ℝ) : ℝ :=
  tau_corr / tau_Eig_eff_N gamma0 Vxi N

/-- Coherence-time ansatz `τ_coh(N)=N^α`. -/
def tau_coh_N (alpha N : ℝ) : ℝ :=
  N ^ alpha

/-- The effective eigentime spacing is the inverse of the effective rate. -/
theorem lambda_eff_mul_tau_Eig_eff_N
    (gamma0 Vxi N : ℝ)
    (hgamma : 0 < gamma0) (hV : 0 < Vxi) (hN : 0 < N) :
    lambda_eff_N gamma0 Vxi N * tau_Eig_eff_N gamma0 Vxi N = 1 := by
  unfold lambda_eff_N tau_Eig_eff_N
  have hprod : gamma0 * Vxi ≠ 0 := mul_ne_zero (ne_of_gt hgamma) (ne_of_gt hV)
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hN)
  field_simp [hprod, hN2]

/-- Closed form of the finite-memory parameter:
`μ(N)=τ_corr γ₀ Vξ/N²`. -/
theorem mu_finite_memory_N_closed_form
    (tau_corr gamma0 Vxi N : ℝ)
    (hgamma : 0 < gamma0) (hV : 0 < Vxi) (hN : 0 < N) :
    mu_finite_memory_N tau_corr gamma0 Vxi N =
      tau_corr * gamma0 * Vxi / N ^ 2 := by
  unfold mu_finite_memory_N tau_Eig_eff_N
  have hprod : gamma0 * Vxi ≠ 0 := mul_ne_zero (ne_of_gt hgamma) (ne_of_gt hV)
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hN)
  field_simp [hprod, hN2]

/-- Closed form of the same memory parameter when written as
`τ_corr/(1/λ_eff(N))`, the form used internally by `alpha_selection_scaling`. -/
theorem mu_from_lambda_eff_closed_form
    (tau_corr gamma0 Vxi N : ℝ)
    (hgamma : 0 < gamma0) (hV : 0 < Vxi) (hN : 0 < N) :
    tau_corr / (1 / lambda_eff_N gamma0 Vxi N) =
      tau_corr * gamma0 * Vxi / N ^ 2 := by
  unfold lambda_eff_N
  have hprod : gamma0 * Vxi ≠ 0 := mul_ne_zero (ne_of_gt hgamma) (ne_of_gt hV)
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hN)
  have hlambda : gamma0 * Vxi / N ^ 2 ≠ 0 := div_ne_zero hprod hN2
  field_simp [hprod, hN2, hlambda]

/-- Fixed finite-memory balance written with the explicit WESH finite-memory
quantities: `μ(N) τ_coh(N)=C₀` for all `N>1`. -/
def finite_memory_fixed_regime_balance
    (tau_corr gamma0 Vxi alpha C0 : ℝ) : Prop :=
  ∀ N : ℝ, 1 < N →
    mu_finite_memory_N tau_corr gamma0 Vxi N * tau_coh_N alpha N = C0

/-- The finite-memory balance is equivalent, on the positive parameter domain,
to the closed-form balance `(τ_corr γ₀ Vξ/N²) N^α = C₀`. -/
theorem finite_memory_balance_closed_form
    (tau_corr gamma0 Vxi alpha C0 : ℝ)
    (hgamma : 0 < gamma0) (hV : 0 < Vxi)
    (h_balance : finite_memory_fixed_regime_balance tau_corr gamma0 Vxi alpha C0) :
    ∀ N : ℝ, 1 < N →
      (tau_corr * gamma0 * Vxi / N ^ 2) * N ^ alpha = C0 := by
  intro N hN
  have hNpos : 0 < N := lt_trans zero_lt_one hN
  have hmu := mu_finite_memory_N_closed_form tau_corr gamma0 Vxi N hgamma hV hNpos
  have hb := h_balance N hN
  unfold tau_coh_N at hb
  rw [hmu] at hb
  exact hb

/--
Selection of `α=2` from the WESH fixed-regime scaling balance.

This is the algebraic core of the paper's finite-memory argument.  The
physical inputs are already present in the displayed balance:

* `gamma0 * Vxi / N²` is the effective coarse-grained dissipative rate
  coming from the WESH `N^{-2}` bilocal normalisation;
* `tau_Eig_eff = 1/lambda_eff` is the corresponding effective eigentime
  spacing;
* `mu = tau_corr/tau_Eig_eff` is the dimensionless finite-memory parameter;
* `tau_coh = N^alpha` is the collective coherence-time ansatz;
* `h_balance` is the fixed-regime condition that `mu * tau_coh` is
  independent of `N`.

The proof uses only the algebraic consequence of that finite-memory balance:
evaluating the balance at `N=2` and `N=4` forces `alpha=2`.
-/
theorem alpha_selection_scaling
    (gamma0 tau_corr Vxi : ℝ)
    (h_pos : 0 < gamma0 ∧ 0 < tau_corr ∧ 0 < Vxi)
    (alpha C0 : ℝ) (_hC : 0 < C0)
    (h_balance : ∀ N : ℝ, 1 < N →
      let lambda_eff := gamma0 * Vxi / N ^ 2
      let tau_Eig_eff := 1 / lambda_eff
      let mu := tau_corr / tau_Eig_eff
      let tau_coh := N ^ alpha
      mu * tau_coh = C0) :
    alpha = 2 := by
  have h_at_two := h_balance 2 (by norm_num)
  have h_at_four := h_balance 4 (by norm_num)
  norm_num at h_at_two h_at_four
  have h_alpha : (2 : ℝ) ^ (alpha - 2) = 1 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    norm_num
    rw [show (4 : ℝ) ^ alpha = 2 ^ alpha * 2 ^ alpha by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num] at h_at_four
    ring_nf at h_at_two h_at_four ⊢
    nlinarith [mul_pos h_pos.1 h_pos.2.2]
  norm_num [Real.rpow_def_of_pos] at h_alpha
  linarith

/-- Closed-form finite-memory balance forces the WESH exponent `α=2`. -/
theorem alpha_from_finite_memory_closed_balance
    (gamma0 tau_corr Vxi : ℝ)
    (h_pos : 0 < gamma0 ∧ 0 < tau_corr ∧ 0 < Vxi)
    (alpha C0 : ℝ) (hC : 0 < C0)
    (h_closed_balance : ∀ N : ℝ, 1 < N →
      (tau_corr * gamma0 * Vxi / N ^ 2) * N ^ alpha = C0) :
    alpha = 2 := by
  exact alpha_selection_scaling gamma0 tau_corr Vxi h_pos alpha C0 hC (by
    intro N hN
    have hNpos : 0 < N := lt_trans zero_lt_one hN
    have hmu := mu_from_lambda_eff_closed_form tau_corr gamma0 Vxi N h_pos.1 h_pos.2.2 hNpos
    change (tau_corr / (1 / lambda_eff_N gamma0 Vxi N)) * N ^ alpha = C0
    rw [hmu]
    exact h_closed_balance N hN)

/-- A WESH finite-memory fixed-regime balance forces `α=2`.  This is the
paper-faithful corollary linking finite correlation time, the `N^{-2}`
bilocal rate, the effective eigentime spacing, and the fixed-regime
coherence ansatz. -/
theorem alpha_from_finite_memory_balance
    (gamma0 tau_corr Vxi : ℝ)
    (h_pos : 0 < gamma0 ∧ 0 < tau_corr ∧ 0 < Vxi)
    (alpha C0 : ℝ) (hC : 0 < C0)
    (h_balance : finite_memory_fixed_regime_balance tau_corr gamma0 Vxi alpha C0) :
    alpha = 2 := by
  have h_closed := finite_memory_balance_closed_form
    tau_corr gamma0 Vxi alpha C0 h_pos.1 h_pos.2.2 h_balance
  exact alpha_from_finite_memory_closed_balance gamma0 tau_corr Vxi h_pos alpha C0 hC h_closed

end CollectiveScaling

/-! ## 10. Decoupling in the formal G → 0 limit -/

section Decoupling

open Real Filter Topology

/-- Local coarse-grained rate tends to zero in the formal `G → 0+` limit. -/
theorem decoupling_rate_limit
    (xi gamma0 Vxi rate : ℝ → ℝ)
    (h_xi : ∃ c1 > 0, ∀ G > 0, xi G = c1 * Real.sqrt G)
    (h_gamma : ∃ c2 > 0, ∀ G > 0, gamma0 G = c2 / Real.sqrt G)
    (h_V : ∃ c3 > 0, ∀ G > 0, Vxi G = c3 * (xi G) ^ 4)
    (h_rate : ∃ c4 > 0, ∀ G > 0, rate G = c4 * gamma0 G * Vxi G) :
    Tendsto rate (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨c1, _hc1, hxi_eq⟩ := h_xi
  obtain ⟨c2, _hc2, hgamma_eq⟩ := h_gamma
  obtain ⟨c3, _hc3, hV_xi⟩ := h_V
  obtain ⟨c4, _hc4, hrate⟩ := h_rate
  have h_rate_simplified :
      ∀ G > 0, rate G = c3 * c4 * c2 * c1 ^ 4 * G ^ (3 / 2 : ℝ) := by
    intro G hG
    rw [hrate G hG, hgamma_eq G hG, hV_xi G hG, hxi_eq G hG]
    ring_nf
    rw [show (Real.sqrt G) ^ 4 = (Real.sqrt G ^ 2) ^ 2 by ring,
        Real.sq_sqrt (le_of_lt hG)]
    ring_nf
    rw [show (3 / 2 : ℝ) = 2 - 1 / 2 by norm_num,
        Real.sqrt_eq_rpow, Real.rpow_sub hG]
    norm_num
    ring_nf
  rw [Filter.tendsto_congr'
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [h_rate_simplified x hx])]
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (Continuous.tendsto'
      (by exact Continuous.mul continuous_const (continuous_id'.rpow_const <| by norm_num)) _ _ <| by norm_num)

/-- Integrated bilocal weight has the same decoupling structure. -/
theorem integrated_gamma_limit
    (xi gamma0 Vxi integratedGamma : ℝ → ℝ)
    (h_xi : ∃ c1 > 0, ∀ G > 0, xi G = c1 * Real.sqrt G)
    (h_gamma : ∃ c2 > 0, ∀ G > 0, gamma0 G = c2 / Real.sqrt G)
    (h_V : ∃ c3 > 0, ∀ G > 0, Vxi G = c3 * (xi G) ^ 4)
    (h_integrated : ∃ c4 > 0, ∀ G > 0, integratedGamma G = c4 * gamma0 G * Vxi G) :
    Tendsto integratedGamma (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  decoupling_rate_limit xi gamma0 Vxi integratedGamma h_xi h_gamma h_V h_integrated

/-- If both dissipative coefficients vanish, their bounded observable contribution vanishes. -/
theorem dissipative_bound_tends_zero
    (nu integratedGamma : ℝ → ℝ) (CA : ℝ)
    (hnu : Tendsto nu (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : Tendsto integratedGamma (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun G : ℝ => CA * (nu G + integratedGamma G))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hsum : Tendsto (fun G : ℝ => nu G + integratedGamma G)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 + 0)) := Tendsto.add hnu hint
  have hmul : Tendsto (fun G : ℝ => CA * (nu G + integratedGamma G))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (CA * (0 + 0))) := Tendsto.const_mul CA hsum
  convert hmul using 1
  ring_nf

end Decoupling

/-! ## 11. Section 1 parameter consistency -/

/-- Fundamental Section 1 WESH parameters. -/
structure WESHParameters where
  hbar : ℝ
  c : ℝ
  G : ℝ
  m_T : ℝ
  xi : ℝ
  gamma0 : ℝ
  N : ℝ
  nu : ℝ
  tau_Eig : ℝ
  tau_corr : ℝ
  tau_coh : ℝ
  alpha : ℝ
  Gamma_value : ℝ
  C_value : ℝ

/-- Parameter relations appearing in Section 1 and Table 1. -/
def WESH_consistent (p : WESHParameters) : Prop :=
  p.xi = p.hbar / (p.m_T * p.c) ∧
  p.tau_Eig = 1 / p.nu ∧
  p.tau_corr = p.xi / p.c ∧
  p.tau_coh = p.N ^ p.alpha ∧
  p.alpha = 2 ∧
  0 ≤ p.Gamma_value ∧
  0 ≤ p.C_value ∧ p.C_value ≤ 1

/-- Non-empty witness for the Section 1 parameter consistency relations. -/
theorem wesh_parameters_exist : ∃ p : WESHParameters, WESH_consistent p := by
  refine ⟨⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0⟩, ?_⟩
  unfold WESH_consistent
  norm_num

end WESH.Section1

end
