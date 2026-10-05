-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PolynomialBallEnergy

/-!
# Uniform polynomial divergence estimate on the actual ball

A weighted Rellich identity expresses the difference between three times the
divergence energy and the full gradient energy as nonnegative squares, modulo
a genuinely zero-boundary polynomial divergence. The constant is independent
of polynomial degree. The differential identity is a weighted version of the
classical Miranda-Talenti divergence identity; the specific square completion
below is proved directly.
-/

@[expose] public section

open MvPolynomial CKN MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Polynomial partial derivatives genuinely commute. -/
theorem ballPolynomial_pderiv_comm (v : BallPolynomial) (i j : Fin 3) :
    pderiv i (pderiv j v) = pderiv j (pderiv i v) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  ext m
  simp only [coeff_pderiv]
  have hm : m + Finsupp.single i 1 + Finsupp.single j 1 =
      m + Finsupp.single j 1 + Finsupp.single i 1 := by ac_rfl
  rw [hm]
  simp only [Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij, ite_false,
    add_zero]
  ring

/-- The literal polynomial weight of the Euclidean unit ball. -/
def polynomialBallBoundaryWeight : BallPolynomial := 1 - radiusSquaredPolynomial

theorem polynomialBallBoundaryWeight_pderiv (i : Fin 3) :
    pderiv i polynomialBallBoundaryWeight = -2 * X i := by
  classical
  simp only [polynomialBallBoundaryWeight, map_sub, pderiv_one,
    radiusSquaredPolynomial, map_sum, pderiv_pow, pderiv_X]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_sub]
  ring

theorem polynomialBallBoundaryWeight_eval (x : Vec3) :
    ballPolynomialEval polynomialBallBoundaryWeight x = ballBoundaryWeight 0 1 x := by
  simp [ballPolynomialEval, polynomialBallBoundaryWeight, radiusSquaredPolynomial,
    ballBoundaryWeight]

/-- The polynomial components of the positive weighted gradient. -/
def polynomialWeightedGradient (v : BallPolynomial) (i : Fin 3) : BallPolynomial :=
  polynomialBallBoundaryWeight * pderiv i v

/-- The flux in the sum-of-squares weighted Rellich identity. It has the actual
vanishing ball weight as a factor in every component. -/
def polynomialBallRellichFlux (v : BallPolynomial) (i : Fin 3) : BallPolynomial :=
  polynomialBallBoundaryWeight *
    (C 3 * polynomialBallBoundaryWeight *
      (pderiv i v * polynomialLaplacian v -
        ∑ j : Fin 3, pderiv j v * pderiv i (pderiv j v)) -
      C 12 * pderiv i v * (∑ j : Fin 3, X j * pderiv j v) +
      C 4 * X i * (∑ j : Fin 3, (pderiv j v) ^ 2))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- A degree-independent exact square completion in the polynomial ring.
After integration, each flux derivative vanishes on the actual unit ball. -/
theorem polynomialBallRellich_sum_of_squares (v : BallPolynomial) :
    6 * (∑ i : Fin 3, pderiv i (polynomialWeightedGradient v i)) ^ 2 -
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          (pderiv i (polynomialWeightedGradient v j)) ^ 2) =
      polynomialBallBoundaryWeight ^ 2 *
        ((∑ i : Fin 3, ∑ j : Fin 3, (pderiv i (pderiv j v)) ^ 2) +
          3 * (polynomialLaplacian v) ^ 2) +
        ∑ i : Fin 3, pderiv i (polynomialBallRellichFlux v i) := by
  classical
  simp only [polynomialWeightedGradient, polynomialBallRellichFlux,
    pderiv_mul, polynomialBallBoundaryWeight_pderiv, polynomialLaplacian_apply,
    Fin.sum_univ_three]
  simp only [pderiv_mul, map_add, map_sub, pderiv_C, pderiv_pow, pderiv_X,
    Pi.single_apply,
    polynomialBallBoundaryWeight_pderiv]
  norm_num only [Fin.reduceFinMk, Fin.isValue, reduceIte, one_mul, zero_mul,
    mul_one, mul_zero, zero_add, add_zero, pow_one, pow_zero]
  simp only [ballPolynomial_pderiv_comm (i := 1) (j := 0),
    ballPolynomial_pderiv_comm (i := 2) (j := 0),
    ballPolynomial_pderiv_comm (i := 2) (j := 1)]
  simp only [polynomialBallBoundaryWeight, radiusSquaredPolynomial, Fin.sum_univ_three]
  rw [show C (3 : ℝ) = (3 : BallPolynomial) from map_natCast C 3,
    show C (12 : ℝ) = (12 : BallPolynomial) from map_natCast C 12,
    show C (4 : ℝ) = (4 : BallPolynomial) from map_natCast C 4]
  norm_num
  ring

/-- Every polynomial evaluation is genuinely integrable on the actual unit ball. -/
theorem ballPolynomialEval_integrable_unitBall (p : BallPolynomial) :
    Integrable (ballPolynomialEval p) (volume.restrict (vec3Ball 0 1)) := by
  apply ((ballPolynomialEval_contDiff p).continuous.continuousOn.integrableOn_compact
    weightedClosedUnitBall_isCompact).mono_set
  intro x hx
  exact (ballBoundaryWeight_pos_of_mem_unitBall hx).le

/-- Integration of polynomial evaluations on the actual unit ball is linear. -/
def ballPolynomialIntegral : BallPolynomial →ₗ[ℝ] ℝ where
  toFun p := ∫ x in vec3Ball 0 1, ballPolynomialEval p x
  map_add' p q := by
    simp only [ballPolynomialEval, eval_add]
    exact integral_add (ballPolynomialEval_integrable_unitBall p)
      (ballPolynomialEval_integrable_unitBall q)
  map_smul' c p := by
    simp only [ballPolynomialEval, smul_eval, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c (ballPolynomialEval p)

/-- Integration respects literal natural-number polynomial multiples. -/
theorem ballPolynomialIntegral_nat_mul (n : ℕ) (p : BallPolynomial) :
    ballPolynomialIntegral ((n : BallPolynomial) * p) =
      (n : ℝ) * ballPolynomialIntegral p := by
  rw [show (n : BallPolynomial) = C (n : ℝ) from (map_natCast C n).symm,
    C_mul', map_smul, smul_eq_mul]

/-- A derivative of a polynomial times the true ball boundary weight integrates to zero. -/
theorem ballPolynomialIntegral_boundary_derivative (p : BallPolynomial) (i : Fin 3) :
    ballPolynomialIntegral (pderiv i (polynomialBallBoundaryWeight * p)) = 0 := by
  change (∫ x in vec3Ball 0 1,
    ballPolynomialEval (pderiv i (polynomialBallBoundaryWeight * p)) x) = 0
  have heq : ballPolynomialEval (polynomialBallBoundaryWeight * p) =
      fun x ↦ ballBoundaryWeight 0 1 x * ballPolynomialEval p x := by
    funext x
    rw [show ballPolynomialEval (polynomialBallBoundaryWeight * p) x =
        ballPolynomialEval polynomialBallBoundaryWeight x * ballPolynomialEval p x from
      (eval x).map_mul _ _, polynomialBallBoundaryWeight_eval]
  simp_rw [← spatialDeriv_ballPolynomialEval, heq]
  exact weightedBallBoundary_derivative_integral_eq_zero (ballPolynomialEval_contDiff p) i

/-- The genuine flux in the square completion has zero integral divergence. -/
theorem ballPolynomialIntegral_rellichFlux (v : BallPolynomial) :
    ballPolynomialIntegral (∑ i : Fin 3, pderiv i (polynomialBallRellichFlux v i)) = 0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  exact ballPolynomialIntegral_boundary_derivative _ i

/-- A polynomial that is nonnegative at every actual point has nonnegative ball integral. -/
theorem ballPolynomialIntegral_nonneg {p : BallPolynomial}
    (hp : ∀ x : Vec3, 0 ≤ ballPolynomialEval p x) : 0 ≤ ballPolynomialIntegral p :=
  integral_nonneg hp

/-- The polynomial Hessian square remainder is nonnegative on the actual unit ball. -/
theorem ballPolynomialRellich_remainder_nonneg (v : BallPolynomial) :
    0 ≤ ballPolynomialIntegral (polynomialBallBoundaryWeight ^ 2 *
      ((∑ i : Fin 3, ∑ j : Fin 3, (pderiv i (pderiv j v)) ^ 2) +
        3 * (polynomialLaplacian v) ^ 2)) := by
  apply ballPolynomialIntegral_nonneg
  intro x
  simp only [ballPolynomialEval, eval_mul, eval_pow, eval_add, eval_sum, map_ofNat]
  refine mul_nonneg (sq_nonneg _) (add_nonneg ?_ ?_)
  · exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  · exact mul_nonneg (by norm_num) (sq_nonneg _)

/-- The uniform Rellich estimate, expressed by actual polynomial ball integrals. -/
theorem polynomialWeightedGradient_integral_bound (v : BallPolynomial) :
    ballPolynomialIntegral (∑ i : Fin 3, ∑ j : Fin 3,
      (pderiv i (polynomialWeightedGradient v j)) ^ 2) ≤
      3 * ballPolynomialIntegral ((∑ i : Fin 3,
        pderiv i (polynomialWeightedGradient v i)) ^ 2) := by
  have h := congrArg ballPolynomialIntegral (polynomialBallRellich_sum_of_squares v)
  simp only [map_sub, map_add, ballPolynomialIntegral_rellichFlux, add_zero] at h
  have h6 := ballPolynomialIntegral_nat_mul 6
    ((∑ i : Fin 3, pderiv i (polynomialWeightedGradient v i)) ^ 2)
  have h2 := ballPolynomialIntegral_nat_mul 2
    (∑ i : Fin 3, ∑ j : Fin 3, (pderiv i (polynomialWeightedGradient v j)) ^ 2)
  norm_num only at h6 h2
  rw [h6, h2] at h
  have hpos := ballPolynomialRellich_remainder_nonneg v
  linarith

/-- Genuine component differentiation of the polynomial ball inverse. -/
theorem spatialDeriv_polynomialBallDivergenceField (v : BallPolynomial) (i j : Fin 3)
    (x : Vec3) :
    spatialDeriv (fun y ↦ polynomialBallDivergenceField v y j) i x =
      -ballPolynomialEval (pderiv i (polynomialWeightedGradient v j)) x := by
  have heq : (fun y ↦ polynomialBallDivergenceField v y j) =
      fun y ↦ -ballPolynomialEval (polynomialWeightedGradient v j) y := by
    funext y
    simp only [polynomialBallDivergenceField, Pi.neg_apply, weightedBallGradient,
      polynomialWeightedGradient, spatialDeriv_ballPolynomialEval]
    rw [show ballPolynomialEval (polynomialBallBoundaryWeight * pderiv j v) y =
      ballPolynomialEval polynomialBallBoundaryWeight y * ballPolynomialEval (pderiv j v) y
        from (eval y).map_mul _ _, polynomialBallBoundaryWeight_eval]
  rw [heq]
  unfold spatialDeriv
  rw [fderiv_fun_neg]
  exact congrArg Neg.neg (spatialDeriv_ballPolynomialEval _ i x)

/-- The actual gradient of the polynomial divergence inverse has a degree-independent
bound by three times its actual divergence energy. -/
theorem polynomialBallDivergenceField_gradient_bound (v : BallPolynomial) :
    (∫ x in vec3Ball 0 1, ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialDeriv (fun y ↦ polynomialBallDivergenceField v y j) i x) ^ 2) ≤
      3 * (∫ x in vec3Ball 0 1, (∑ i : Fin 3,
        spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x) ^ 2) := by
  have h := polynomialWeightedGradient_integral_bound v
  change (∫ x in vec3Ball 0 1, ballPolynomialEval _ x) ≤
    3 * (∫ x in vec3Ball 0 1, ballPolynomialEval _ x) at h
  simpa only [ballPolynomialEval, eval_sum, eval_pow,
    spatialDeriv_polynomialBallDivergenceField, neg_sq, Finset.sum_neg_distrib] using h

/-- The degree-independent estimate in the actual Hilbert energy space. -/
theorem polynomialBallDivergenceEnergy_norm_sq_bound (v : BallPolynomial) :
    ‖polynomialBallDivergenceEnergy v‖ ^ 2 ≤
      3 * ‖stokesEnergyDivergence (vec3Ball 0 1) (polynomialBallDivergenceEnergy v)‖ ^ 2 := by
  have hdiv :
      ‖stokesEnergyDivergence (vec3Ball 0 1) (polynomialBallDivergenceEnergy v)‖ ^ 2 =
        ∫ x in vec3Ball 0 1, (∑ i : Fin 3,
          spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [polynomialBallDivergenceEnergy_divergence_ae v] with x hx
    rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hdiv, polynomialBallDivergenceEnergy_norm_sq]
  simpa only [Fintype.sum_prod_type] using polynomialBallDivergenceField_gradient_bound v

/-- Every actual mean-zero polynomial has an actual energy-space divergence inverse
with the uniform norm-square constant three. -/
theorem exists_meanZero_polynomial_stokesEnergy_inverse_bound {f : BallPolynomial}
    (hf : (∫ x in vec3Ball 0 1, ballPolynomialEval f x) = 0) :
    ∃ v : BallPolynomial,
      stokesEnergyDivergence (vec3Ball 0 1) (polynomialBallDivergenceEnergy v) =
        unitBallPolynomialL2 f ∧
      ‖polynomialBallDivergenceEnergy v‖ ^ 2 ≤ 3 * ‖unitBallPolynomialL2 f‖ ^ 2 := by
  obtain ⟨v, hv⟩ := exists_meanZero_polynomial_stokesEnergy_inverse hf
  exact ⟨v, hv, by simpa only [hv] using polynomialBallDivergenceEnergy_norm_sq_bound v⟩

end FluidSingularSets
