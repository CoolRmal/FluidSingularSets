-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FischerPolynomial

/-!
# Genuine polynomial inversion of the weighted ball operator

The positive homogeneous principal blocks give an actual polynomial solution
of `-div ((1 - |x|²) grad v) = f - c`. The constant `c` is produced by algebra;
identifying it with the ball average and obtaining a uniform Sobolev estimate
require additional analytic arguments. Neither conclusion is assumed here.
-/

@[expose] public section

open MvPolynomial Module
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual Euler operator on polynomials. -/
def polynomialEuler : BallPolynomial →ₗ[ℝ] BallPolynomial :=
  ∑ i : Fin 3, (LinearMap.mulLeft ℝ (X i)).comp (pderiv i).toLinearMap

/-- The polynomial form of `-div ((1 - |x|²) grad v)`. -/
def polynomialBallOperator : BallPolynomial →ₗ[ℝ] BallPolynomial :=
  (LinearMap.mulLeft ℝ radiusSquaredPolynomial).comp polynomialLaplacian -
    polynomialLaplacian + (2 : ℝ) • polynomialEuler

theorem polynomialEuler_apply (p : BallPolynomial) :
    polynomialEuler p = ∑ i : Fin 3, X i * pderiv i p := by
  simp [polynomialEuler]

theorem polynomialBallOperator_apply (p : BallPolynomial) :
    polynomialBallOperator p = radiusSquaredPolynomial * polynomialLaplacian p -
      polynomialLaplacian p + (2 : ℝ) • (∑ i : Fin 3, X i * pderiv i p) := by
  simp [polynomialBallOperator, polynomialEuler_apply]

theorem polynomialBallOperator_homogeneous {p : BallPolynomial} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    polynomialBallOperator p = ballPrincipalBlock n p - polynomialLaplacian p := by
  rw [polynomialBallOperator_apply, hp.sum_X_mul_pderiv, ballPrincipalBlock_apply]
  rw [← Nat.cast_smul_eq_nsmul ℝ n p, smul_smul]
  abel

theorem polynomialBallOperator_C (c : ℝ) : polynomialBallOperator (C c) = 0 := by
  simp [polynomialBallOperator_apply, polynomialLaplacian_apply]

/-- Every homogeneous right-hand side has a genuine polynomial inverse modulo constants. -/
theorem exists_polynomialBallOperator_inverse_homogeneous (n : ℕ)
    {f : BallPolynomial} (hf : f.IsHomogeneous n) :
    ∃ v : BallPolynomial, ∃ c : ℝ, polynomialBallOperator v = f - C c := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hc := totalDegree_eq_zero_iff_eq_C.mp
        ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hf)
      exact ⟨0, f.coeff 0, by rw [map_zero, hc]; simp⟩
    · obtain ⟨v, hv, heq⟩ :=
        exists_homogeneousBallPrincipalBlock_inverse (Nat.pos_of_ne_zero hn) hf
      by_cases hn2 : n ≤ 1
      · refine ⟨v, 0, ?_⟩
        rw [polynomialBallOperator_homogeneous hv, heq,
          polynomialLaplacian_eq_zero_of_degree_le_one hv hn2]
        simp
      · obtain ⟨w, c, hw⟩ := ih (n - 2) (by omega)
          (polynomialLaplacian_isHomogeneous hv)
        refine ⟨v + w, c, ?_⟩
        rw [map_add, polynomialBallOperator_homogeneous hv, heq, hw]
        abel

/-- Actual inversion for every polynomial datum, with no right-inverse hypothesis. -/
theorem exists_polynomialBallOperator_inverse (f : BallPolynomial) :
    ∃ v : BallPolynomial, ∃ c : ℝ, polynomialBallOperator v = f - C c := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial α c =>
    exact exists_polynomialBallOperator_inverse_homogeneous α.degree
      (isHomogeneous_monomial c rfl)
  | add p q hp hq =>
    obtain ⟨v, c, hv⟩ := hp
    obtain ⟨w, d, hw⟩ := hq
    refine ⟨v + w, c + d, ?_⟩
    rw [map_add, hv, hw, map_add]
    abel

end FluidSingularSets
