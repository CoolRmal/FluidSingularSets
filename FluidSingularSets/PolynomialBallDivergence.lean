-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallPolynomialInverse
public import FluidSingularSets.WeightedBallDivergence

/-!
# Actual smooth polynomial divergence fields on the unit ball

Polynomial inversion is transported to actual smooth functions and genuine
spatial derivatives. The resulting vector field has the prescribed polynomial
divergence modulo a constant and vanishes pointwise on the unit sphere. The
constant is not yet identified with the ball mean; a uniform Sobolev bound is
also a separate analytic obligation.
-/

@[expose] public section

open MvPolynomial CKN
open CKN.Foundation.Parabolic
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A polynomial evaluated on the actual spatial carrier. -/
def ballPolynomialEval (p : BallPolynomial) (x : Vec3) : ℝ := MvPolynomial.eval x p

/-- Actual polynomial evaluation is smooth to every order. -/
theorem ballPolynomialEval_contDiff (p : BallPolynomial) :
    ContDiff ℝ (⊤ : ℕ∞) (ballPolynomialEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 ↦ MvPolynomial.eval x (C c))
    simp only [eval_C]
    exact contDiff_const
  | add p q hp hq =>
    have heq : ballPolynomialEval (p + q) =
        fun y ↦ ballPolynomialEval p y + ballPolynomialEval q y := by
      funext y
      simp [ballPolynomialEval]
    rw [heq]
    exact hp.add hq
  | mul_X p i hp =>
    have heq : ballPolynomialEval (p * X i) = fun y ↦ ballPolynomialEval p y * y i := by
      funext y
      simp [ballPolynomialEval]
    rw [heq]
    exact hp.mul (contDiff_apply ℝ ℝ i)

/-- The genuine spatial derivative equals the evaluated polynomial derivative. -/
theorem spatialDeriv_ballPolynomialEval (p : BallPolynomial) (i : Fin 3) (x : Vec3) :
    spatialDeriv (ballPolynomialEval p) i x = ballPolynomialEval (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on generalizing i x with
  | C c =>
    have heq : ballPolynomialEval (C c) = fun _ : Vec3 ↦ c := by
      funext y
      simp [ballPolynomialEval]
    rw [heq]
    simp [ballPolynomialEval, spatialDeriv]
  | add p q hp hq =>
    have heq : ballPolynomialEval (p + q) =
        fun y ↦ ballPolynomialEval p y + ballPolynomialEval q y := by
      funext y
      simp [ballPolynomialEval]
    rw [heq, spatialDeriv_add
      ((ballPolynomialEval_contDiff p).differentiable (by simp)).differentiableAt
      ((ballPolynomialEval_contDiff q).differentiable (by simp)).differentiableAt,
      hp, hq]
    simp [ballPolynomialEval]
  | mul_X p j hp =>
    have heq : ballPolynomialEval (p * X j) = fun y ↦ ballPolynomialEval p y * y j := by
      funext y
      simp [ballPolynomialEval]
    rw [heq, spatialDeriv_mul
      ((ballPolynomialEval_contDiff p).differentiable (by simp)).differentiableAt
      (differentiableAt_apply j x), hp]
    have hcoord : spatialDeriv (fun y : Vec3 ↦ y j) i x = if i = j then 1 else 0 := by
      rw [spatialDeriv, (hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv]
      simp [basisVec, Pi.single_apply, eq_comm]
    rw [hcoord]
    simp only [pderiv_mul, pderiv_X, ballPolynomialEval, eval_add, eval_mul, eval_X]
    split_ifs <;> simp_all [ballPolynomialEval]

/-- The genuine spatial Laplacian equals the evaluated polynomial Laplacian. -/
theorem spatialLaplacian_ballPolynomialEval (p : BallPolynomial) (x : Vec3) :
    spatialLaplacian (ballPolynomialEval p) x = ballPolynomialEval (polynomialLaplacian p) x := by
  have hd (i : Fin 3) : spatialDeriv (ballPolynomialEval p) i =
      ballPolynomialEval (pderiv i p) := funext (spatialDeriv_ballPolynomialEval p i)
  simp only [spatialLaplacian, hd, spatialDeriv_ballPolynomialEval,
    polynomialLaplacian_apply, ballPolynomialEval, eval_sum]

/-- The actual weighted elliptic operator is exactly the polynomial operator. -/
theorem weightedBallOperator_ballPolynomialEval (p : BallPolynomial) (x : Vec3) :
    weightedBallOperator 0 1 (ballPolynomialEval p) x =
      ballPolynomialEval (polynomialBallOperator p) x := by
  simp only [weightedBallOperator, ballBoundaryWeight, Pi.zero_apply, sub_zero, one_pow,
    spatialLaplacian_ballPolynomialEval, spatialDeriv_ballPolynomialEval,
    polynomialBallOperator_apply, ballPolynomialEval, eval_add, eval_sub, eval_mul,
    smul_eval, eval_sum, eval_X, radiusSquaredPolynomial, eval_pow]
  ring

/-- The genuine polynomial field produced by the weighted ball construction. -/
def polynomialBallDivergenceField (v : BallPolynomial) : Vec3 → Vec3 :=
  -weightedBallGradient 0 1 (ballPolynomialEval v)

/-- The field is an actual smooth vector field. -/
theorem polynomialBallDivergenceField_contDiff (v : BallPolynomial) :
    ContDiff ℝ (⊤ : ℕ∞) (polynomialBallDivergenceField v) := by
  apply ContDiff.neg
  apply contDiff_pi.mpr
  intro i
  exact (ballBoundaryWeight_contDiff 0 1).mul
    (contDiff_spatialDeriv_smooth (ballPolynomialEval_contDiff v) i)

/-- The resulting field vanishes on the actual Euclidean unit sphere. -/
theorem polynomialBallDivergenceField_boundary (v : BallPolynomial) (x : Vec3)
    (hx : vec3EuclideanNorm x = 1) : polynomialBallDivergenceField v x = 0 := by
  unfold polynomialBallDivergenceField
  have hb := weightedBallGradient_eq_zero_on_sphere 0 1
    (ballPolynomialEval v) x (by simpa using hx)
  simp [hb]

/-- Every polynomial datum is the divergence of an actual smooth field modulo a constant. -/
theorem exists_polynomial_divergence_field (f : BallPolynomial) :
    ∃ v : BallPolynomial, ∃ c : ℝ,
      (∀ x : Vec3, (∑ i : Fin 3,
        spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x) =
          ballPolynomialEval f x - c) ∧
      ContDiff ℝ (⊤ : ℕ∞) (polynomialBallDivergenceField v) ∧
      (∀ x : Vec3, vec3EuclideanNorm x = 1 → polynomialBallDivergenceField v x = 0) := by
  obtain ⟨v, c, hv⟩ := exists_polynomialBallOperator_inverse f
  refine ⟨v, c, ?_, polynomialBallDivergenceField_contDiff v,
    polynomialBallDivergenceField_boundary v⟩
  intro x
  have hneg (i : Fin 3) :
      spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x =
        -spatialDeriv (fun y ↦ weightedBallGradient 0 1 (ballPolynomialEval v) y i) i x := by
    change spatialDeriv (fun y ↦ -(weightedBallGradient 0 1 (ballPolynomialEval v) y i)) i x = _
    unfold spatialDeriv
    rw [fderiv_fun_neg]
    rfl
  simp only [hneg, Finset.sum_neg_distrib]
  rw [divergence_weightedBallGradient 0 1 (ballPolynomialEval_contDiff v) x, neg_neg,
    weightedBallOperator_ballPolynomialEval, hv]
  simp [ballPolynomialEval]

end FluidSingularSets
