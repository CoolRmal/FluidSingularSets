-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HilbertBallBoundary

/-!
# Polynomial divergence inverses in the actual Stokes energy completion

The actual zero-boundary polynomial fields are placed in the constructed
Hilbert energy space. Their continuous divergence is their literal classical
divergence. Every mean-zero polynomial datum is therefore in the genuine
divergence range, with no divergence-inverse hypothesis.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The norm square of an actual real Hilbert `L²` function is its actual square integral. -/
theorem real_toLp_norm_sq_eq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : Vec3 → E}
    (hf : MemLp f 2 (volume.restrict (vec3Ball 0 1))) :
    ‖hf.toLp f‖ ^ 2 = ∫ x in vec3Ball 0 1, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- An actual weighted smooth vector gradient in the constructed energy completion. -/
def weightedBallEnergy (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) : stokesGradientEnergySpace (vec3Ball 0 1) :=
  ⟨weightedBallMatrixGradientL2 a ha, weightedBallMatrixGradientL2_mem_energy a ha⟩

/-- The continuous energy divergence agrees with actual classical differentiation. -/
theorem weightedBallEnergy_divergence_ae (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) :
    stokesEnergyDivergence (vec3Ball 0 1) (weightedBallEnergy a ha)
      =ᵐ[volume.restrict (vec3Ball 0 1)]
      fun x ↦ ∑ i : Fin 3, spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a i y) i x := by
  have hcomp := stokesMatrixTrace.coeFn_compLpL
    (p := 2) (μ := volume.restrict (vec3Ball 0 1)) (weightedBallMatrixGradientL2 a ha)
  have hgrad := (weightedBallMatrixGradient_memLp a ha).coeFn_toLp
  change stokesMatrixTrace.compLpL 2 (volume.restrict (vec3Ball 0 1))
    (weightedBallMatrixGradientL2 a ha) =ᵐ[volume.restrict (vec3Ball 0 1)] _
  filter_upwards [hcomp, hgrad] with x hcx hgx
  change weightedBallMatrixGradientL2 a ha x = weightedBallMatrixGradient a x at hgx
  rw [hcx, hgx]
  simp [weightedBallMatrixGradient]

/-- The smooth coefficient of the polynomial divergence field. -/
def polynomialBallFieldCoefficient (v : BallPolynomial) (j : Fin 3) (x : Vec3) : ℝ :=
  -spatialDeriv (ballPolynomialEval v) j x

theorem polynomialBallFieldCoefficient_contDiff (v : BallPolynomial) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (polynomialBallFieldCoefficient v j) :=
  (contDiff_spatialDeriv_smooth (ballPolynomialEval_contDiff v) j).neg

/-- The actual mean-zero polynomial divergence field in the genuine energy completion. -/
def polynomialBallDivergenceEnergy (v : BallPolynomial) :
    stokesGradientEnergySpace (vec3Ball 0 1) :=
  weightedBallEnergy (polynomialBallFieldCoefficient v)
    (polynomialBallFieldCoefficient_contDiff v)

theorem polynomialBallDivergenceEnergy_divergence_ae (v : BallPolynomial) :
    stokesEnergyDivergence (vec3Ball 0 1) (polynomialBallDivergenceEnergy v)
      =ᵐ[volume.restrict (vec3Ball 0 1)]
        fun x ↦ ∑ i : Fin 3,
          spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x := by
  have h := weightedBallEnergy_divergence_ae (polynomialBallFieldCoefficient v)
    (polynomialBallFieldCoefficient_contDiff v)
  exact h.trans (.of_forall (fun x ↦ by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [polynomialBallDivergenceField_component]
    rfl))

/-- The actual polynomial right-hand side genuinely belongs to `L²` on the ball. -/
theorem unitBallPolynomial_memLp (f : BallPolynomial) :
    MemLp (ballPolynomialEval f) 2 (volume.restrict (vec3Ball 0 1)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((ballPolynomialEval_contDiff f).continuous).aestronglyMeasurable).mpr
  exact continuous_integrableOn_unitBall ((ballPolynomialEval_contDiff f).continuous.norm.pow 2)

/-- The literal polynomial datum as an actual `L²` equivalence class. -/
def unitBallPolynomialL2 (f : BallPolynomial) : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) :=
  (unitBallPolynomial_memLp f).toLp (ballPolynomialEval f)

theorem unitBallPolynomialL2_norm_sq (f : BallPolynomial) :
    ‖unitBallPolynomialL2 f‖ ^ 2 = ∫ x in vec3Ball 0 1, ballPolynomialEval f x ^ 2 := by
  have h := real_toLp_norm_sq_eq_integral (unitBallPolynomial_memLp f)
  simpa only [unitBallPolynomialL2, Real.norm_eq_abs, sq_abs] using h

/-- Every actual mean-zero polynomial belongs to the actual continuous divergence range. -/
theorem exists_meanZero_polynomial_stokesEnergy_inverse {f : BallPolynomial}
    (hf : (∫ x in vec3Ball 0 1, ballPolynomialEval f x) = 0) :
    ∃ v : BallPolynomial,
      stokesEnergyDivergence (vec3Ball 0 1) (polynomialBallDivergenceEnergy v) =
        unitBallPolynomialL2 f := by
  obtain ⟨v, hdiv, _hsmooth, _hzero⟩ := exists_meanZero_polynomial_divergence_field hf
  refine ⟨v, ?_⟩
  apply Lp.ext
  have h := polynomialBallDivergenceEnergy_divergence_ae v
  have hp := (unitBallPolynomial_memLp f).coeFn_toLp
  filter_upwards [h, hp] with x hx hpx
  change unitBallPolynomialL2 f x = ballPolynomialEval f x at hpx
  rw [hx, hdiv, hpx]

/-- The energy norm is the actual integrated squared matrix gradient of the field. -/
theorem polynomialBallDivergenceEnergy_norm_sq (v : BallPolynomial) :
    ‖polynomialBallDivergenceEnergy v‖ ^ 2 = ∫ x in vec3Ball 0 1,
      ∑ ij : Fin 3 × Fin 3,
        (spatialDeriv (fun y ↦ polynomialBallDivergenceField v y ij.2) ij.1 x) ^ 2 := by
  change ‖weightedBallMatrixGradientL2 (polynomialBallFieldCoefficient v)
    (polynomialBallFieldCoefficient_contDiff v)‖ ^ 2 = _
  rw [weightedBallMatrixGradientL2, real_toLp_norm_sq_eq_integral]
  apply integral_congr_ae
  exact .of_forall (fun x ↦ by
    change ‖weightedBallMatrixGradient (polynomialBallFieldCoefficient v) x‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro ij _hij
    rw [polynomialBallDivergenceField_component]
    rfl)

end FluidSingularSets
