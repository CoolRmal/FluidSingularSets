-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The weighted-gradient candidate for a divergence inverse on a ball

The field `(R² - |x - x₀|²) ∇v` vanishes on the sphere and its divergence is
the negative weighted elliptic operator
`-(R² - |x - x₀|²) Δv + 2 (x - x₀) · ∇v`. These identities are proved for
actual smooth functions, including the exact antisymmetric-gradient formula.

A bounded right inverse for all mean-zero `L²` data would additionally require
solving the weighted equation and proving a uniform gradient estimate. Those
quantitative conclusions are not assumed or asserted here.
-/

@[expose] public section

open CKN
open CKN.Foundation.Parabolic
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The quadratic weight that vanishes on a Euclidean sphere. -/
def ballBoundaryWeight (x₀ : Vec3) (R : ℝ) (x : Vec3) : ℝ :=
  R ^ 2 - ∑ i : Fin 3, (x i - x₀ i) ^ 2

/-- The ball weight is genuinely smooth. -/
theorem ballBoundaryWeight_contDiff (x₀ : Vec3) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ballBoundaryWeight x₀ R) := by
  unfold ballBoundaryWeight
  fun_prop

/-- Its actual spatial derivative is the linear radial factor. -/
theorem spatialDeriv_ballBoundaryWeight (x₀ : Vec3) (R : ℝ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (ballBoundaryWeight x₀ R) i x = -2 * (x i - x₀ i) := by
  have hj (j : Fin 3) : HasFDerivAt (fun y : Vec3 ↦ (y j - x₀ j) ^ 2)
      ((2 * (x j - x₀ j)) • (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)) x := by
    simpa using ((hasFDerivAt_apply (𝕜 := ℝ) j x).sub_const (x₀ j)).pow 2
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun j _ ↦ hj j)
  have hw := hsum.const_sub (R ^ 2)
  simp only [Finset.sum_apply] at hw
  have heq : (fun y : Vec3 ↦ R ^ 2 - ∑ j : Fin 3, (y j - x₀ j) ^ 2) =
      ballBoundaryWeight x₀ R := rfl
  rw [heq] at hw
  rw [spatialDeriv, hw.fderiv]
  simp [basisVec, Pi.single_apply]

/-- The weighted-gradient vector field proposed for the ball divergence inverse. -/
def weightedBallGradient (x₀ : Vec3) (R : ℝ) (v : Vec3 → ℝ) : Vec3 → Vec3 :=
  fun x i ↦ ballBoundaryWeight x₀ R x * spatialDeriv v i x

/-- The corresponding weighted elliptic operator, with positive energy sign. -/
def weightedBallOperator (x₀ : Vec3) (R : ℝ) (v : Vec3 → ℝ) : Vec3 → ℝ :=
  fun x ↦ -(ballBoundaryWeight x₀ R x) * spatialLaplacian v x +
    2 * ∑ i : Fin 3, (x i - x₀ i) * spatialDeriv v i x

/-- Every component of the weighted-gradient field is genuinely smooth. -/
theorem weightedBallGradient_contDiff (x₀ : Vec3) (R : ℝ) {v : Vec3 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ weightedBallGradient x₀ R v x i) :=
  (ballBoundaryWeight_contDiff x₀ R).mul (contDiff_spatialDeriv_smooth hv i)

/-- The genuine first derivative of the weighted-gradient candidate. -/
theorem spatialDeriv_weightedBallGradient (x₀ : Vec3) (R : ℝ) {v : Vec3 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i j : Fin 3) (x : Vec3) :
    spatialDeriv (fun y ↦ weightedBallGradient x₀ R v y j) i x =
      -2 * (x i - x₀ i) * spatialDeriv v j x +
        ballBoundaryWeight x₀ R x * mixedSecond v i j x := by
  unfold weightedBallGradient
  rw [spatialDeriv_mul ((ballBoundaryWeight_contDiff x₀ R).differentiable (by simp) x)
    ((contDiff_spatialDeriv_smooth hv j).differentiable (by simp) x) i,
    spatialDeriv_ballBoundaryWeight]
  rfl

/-- Its divergence is exactly the negative weighted elliptic operator. -/
theorem divergence_weightedBallGradient (x₀ : Vec3) (R : ℝ) {v : Vec3 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec3) :
    (∑ i : Fin 3, spatialDeriv (fun y ↦ weightedBallGradient x₀ R v y i) i x) =
      -weightedBallOperator x₀ R v x := by
  simp_rw [spatialDeriv_weightedBallGradient x₀ R hv]
  simp only [weightedBallOperator, spatialLaplacian, mixedSecond]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst : (∑ i : Fin 3, -2 * (x i - x₀ i) * spatialDeriv v i x) =
      -2 * ∑ i : Fin 3, (x i - x₀ i) * spatialDeriv v i x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  rw [hfirst]
  ring

/-- The candidate field vanishes on the actual Euclidean sphere. -/
theorem ballBoundaryWeight_eq_zero_on_sphere (x₀ : Vec3) (R : ℝ)
    (x : Vec3) (hsphere : vec3EuclideanNorm (x - x₀) = R) :
    ballBoundaryWeight x₀ R x = 0 := by
  have hsq : ∑ i : Fin 3, (x i - x₀ i) ^ 2 = R ^ 2 := by
    have hnonneg : 0 ≤ ∑ i : Fin 3, (x i - x₀ i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    have h := congrArg (fun t : ℝ ↦ t ^ 2) hsphere
    simpa [vec3EuclideanNorm, Real.sq_sqrt hnonneg] using h
  simp [ballBoundaryWeight, hsq]

/-- Consequently every weighted-gradient candidate has exactly zero boundary values. -/
theorem weightedBallGradient_eq_zero_on_sphere (x₀ : Vec3) (R : ℝ) (v : Vec3 → ℝ)
    (x : Vec3) (hsphere : vec3EuclideanNorm (x - x₀) = R) :
    weightedBallGradient x₀ R v x = 0 := by
  ext i
  simp [weightedBallGradient, ballBoundaryWeight_eq_zero_on_sphere x₀ R x hsphere]

/-- Actual second derivatives commute for the smooth scalar potential. -/
theorem mixedSecond_commute_smooth {v : Vec3 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i j : Fin 3) (x : Vec3) :
    mixedSecond v i j x = mixedSecond v j i x := by
  have hsym : IsSymmSndFDerivAt ℝ v x :=
    hv.contDiffAt.isSymmSndFDerivAt (by simp)
  have h := hsym.eq (basisVec i) (basisVec j)
  have hfd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    ((contDiff_infty_iff_fderiv.mp hv).2.differentiable (by simp)) x
  have hd (k : Fin 3) : fderiv ℝ (spatialDeriv v k) x =
      (fderiv ℝ (fderiv ℝ v) x).flip (basisVec k) := by
    unfold spatialDeriv
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  simpa only [mixedSecond, spatialDeriv, hd, ContinuousLinearMap.flip_apply] using h

/-- The Hessian terms cancel in the antisymmetric gradient, leaving only angular derivatives. -/
theorem weightedBallGradient_antisymmetric (x₀ : Vec3) (R : ℝ) {v : Vec3 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i j : Fin 3) (x : Vec3) :
    spatialDeriv (fun y ↦ weightedBallGradient x₀ R v y j) i x -
      spatialDeriv (fun y ↦ weightedBallGradient x₀ R v y i) j x =
        -2 * ((x i - x₀ i) * spatialDeriv v j x -
          (x j - x₀ j) * spatialDeriv v i x) := by
  rw [spatialDeriv_weightedBallGradient x₀ R hv,
    spatialDeriv_weightedBallGradient x₀ R hv, mixedSecond_commute_smooth hv i j x]
  ring

/-- Summing the exact antisymmetric-gradient identity gives the angular energy,
by the finite-dimensional Lagrange identity. -/
theorem weightedBallGradient_antisymmetric_energy (x₀ : Vec3) (R : ℝ)
    {v : Vec3 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (spatialDeriv (fun y ↦ weightedBallGradient x₀ R v y j) i x -
        spatialDeriv (fun y ↦ weightedBallGradient x₀ R v y i) j x) ^ 2) =
      8 * ((∑ i : Fin 3, (x i - x₀ i) ^ 2) *
        (∑ i : Fin 3, (spatialDeriv v i x) ^ 2) -
          (∑ i : Fin 3, (x i - x₀ i) * spatialDeriv v i x) ^ 2) := by
  simp_rw [weightedBallGradient_antisymmetric x₀ R hv]
  simp only [Fin.sum_univ_three]
  ring

/-- A genuine centered linear right-hand side, the first nonconstant harmonic mode. -/
def linearBallSource (x₀ a : Vec3) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, a i * (x i - x₀ i)

/-- An explicit zero-boundary polynomial lift for centered linear data. -/
def linearBallDivergenceLift (x₀ : Vec3) (R : ℝ) (a : Vec3) : Vec3 → Vec3 :=
  fun x i ↦ ballBoundaryWeight x₀ R x * (-a i / 2)

/-- The derivative of this explicit lift is computed from the actual quadratic weight. -/
theorem spatialDeriv_linearBallDivergenceLift (x₀ : Vec3) (R : ℝ) (a : Vec3)
    (i j : Fin 3) (x : Vec3) :
    spatialDeriv (fun y ↦ linearBallDivergenceLift x₀ R a y j) i x =
      (x i - x₀ i) * a j := by
  unfold linearBallDivergenceLift
  rw [spatialDeriv_mul ((ballBoundaryWeight_contDiff x₀ R).differentiable (by simp) x)
    (differentiableAt_const _) i, spatialDeriv_ballBoundaryWeight]
  have hc : spatialDeriv (fun _ : Vec3 ↦ -a j / 2) i x = 0 := by
    unfold spatialDeriv
    rw [(hasFDerivAt_const (-a j / 2) x).fderiv]
    rfl
  rw [hc, mul_zero, add_zero]
  ring

/-- This is an actual right inverse for every centered linear source, with no PDE premise. -/
theorem divergence_linearBallDivergenceLift (x₀ : Vec3) (R : ℝ) (a : Vec3) (x : Vec3) :
    (∑ i : Fin 3, spatialDeriv (fun y ↦ linearBallDivergenceLift x₀ R a y i) i x) =
      linearBallSource x₀ a x := by
  simp_rw [spatialDeriv_linearBallDivergenceLift]
  exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)

/-- The explicit polynomial right inverse has exactly zero values on the sphere. -/
theorem linearBallDivergenceLift_eq_zero_on_sphere (x₀ : Vec3) (R : ℝ) (a : Vec3)
    (x : Vec3) (hsphere : vec3EuclideanNorm (x - x₀) = R) :
    linearBallDivergenceLift x₀ R a x = 0 := by
  ext i
  simp [linearBallDivergenceLift, ballBoundaryWeight_eq_zero_on_sphere x₀ R x hsphere]

end FluidSingularSets
