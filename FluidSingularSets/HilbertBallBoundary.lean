-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PolynomialBallMeanInverse

/-!
# Genuine zero-boundary energy membership of the weighted ball fields

The interior compact test gradients converge strongly in actual `L²` to the
gradient of the weighted smooth field. Closure of the constructed Stokes test
gradient space therefore supplies genuine zero-boundary energy membership.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual matrix gradient of a weighted smooth vector field. -/
def weightedBallMatrixGradient (a : Fin 3 → Vec3 → ℝ) : Vec3 → StokesGradientMatrix :=
  fun x ↦ WithLp.toLp 2
    (fun ij ↦ spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x)

theorem weightedBallMatrixGradient_continuous (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) :
    Continuous (weightedBallMatrixGradient a) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro ij
  exact (contDiff_spatialDeriv_smooth
    ((ballBoundaryWeight_contDiff 0 1).mul (ha ij.2)) ij.1).continuous

theorem weightedBallMatrixGradient_memLp (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) :
    MemLp (weightedBallMatrixGradient a) 2 (volume.restrict (vec3Ball 0 1)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (weightedBallMatrixGradient_continuous a ha).aestronglyMeasurable).mpr
  exact continuous_integrableOn_unitBall ((weightedBallMatrixGradient_continuous a ha).norm.pow 2)

/-- The actual target matrix gradient as a Hilbert equivalence class. -/
def weightedBallMatrixGradientL2 (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) : StokesGradientL2 (vec3Ball 0 1) :=
  (weightedBallMatrixGradient_memLp a ha).toLp (weightedBallMatrixGradient a)

/-- The canonical actual compact vector test sequence. -/
def weightedBallVectorTestSeq (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) (n : ℕ) : StokesVectorTest (vec3Ball 0 1) :=
  fun j ↦ weightedBallBoundaryTestSeq (a j) (ha j) n

theorem stokesTestGradient_continuous {U : Set Vec3} (φ : StokesVectorTest U) :
    Continuous (stokesTestGradient φ) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro ij
  exact (contDiff_spatialDeriv_smooth (φ ij.2).contDiff ij.1).continuous

/-- A fixed continuous square majorant for the actual matrix gradient errors. -/
def weightedBallGradientErrorMajorant (a : Fin 3 → Vec3 → ℝ) (T : ℝ) (x : Vec3) : ℝ :=
  ∑ ij : Fin 3 × Fin 3,
    (weightedBoundaryDerivativeMajorant (a ij.2) T ij.1 x +
      |spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x|) ^ 2

theorem weightedBallGradientErrorMajorant_continuous (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) (T : ℝ) :
    Continuous (weightedBallGradientErrorMajorant a T) := by
  apply continuous_finsetSum
  intro ij _hij
  exact ((weightedBoundaryDerivativeMajorant_continuous (ha ij.2) T ij.1).add
    (contDiff_spatialDeriv_smooth
      ((ballBoundaryWeight_contDiff 0 1).mul (ha ij.2)) ij.1).continuous.abs).pow 2

theorem weightedBallGradientErrorMajorant_integrable (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) (T : ℝ) :
    Integrable (weightedBallGradientErrorMajorant a T) (volume.restrict (vec3Ball 0 1)) :=
  continuous_integrableOn_unitBall (weightedBallGradientErrorMajorant_continuous a ha T)

/-- The actual gradient errors have a single integrable square majorant. -/
theorem weightedBallVectorTestSeq_gradient_error_sq_le (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ T)
    (n : ℕ) {x : Vec3} (hx : x ∈ vec3Ball 0 1) :
    ‖stokesTestGradient (weightedBallVectorTestSeq a ha n) x -
      weightedBallMatrixGradient a x‖ ^ 2 ≤
      weightedBallGradientErrorMajorant a T x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro ij _hij
  change (((weightedBallBoundaryTestSeq (a ij.2) (ha ij.2) n).partialDeriv ij.1 x) -
    spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x) ^ 2 ≤ _
  have hbnd := weightedBallBoundaryTest_partialDeriv_le (ha ij.2)
    (ballBoundaryWidth_pos n) hT hb hx ij.1
  change |(weightedBallBoundaryTestSeq (a ij.2) (ha ij.2) n).partialDeriv ij.1 x| ≤
    weightedBoundaryDerivativeMajorant (a ij.2) T ij.1 x at hbnd
  have habs : |(weightedBallBoundaryTestSeq (a ij.2) (ha ij.2) n).partialDeriv ij.1 x -
      spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x| ≤
      weightedBoundaryDerivativeMajorant (a ij.2) T ij.1 x +
        |spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x| :=
    (abs_sub _ _).trans (add_le_add hbnd le_rfl)
  have hnonneg : 0 ≤ weightedBoundaryDerivativeMajorant (a ij.2) T ij.1 x +
      |spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x| := by
    unfold weightedBoundaryDerivativeMajorant
    positivity
  nlinarith [abs_nonneg ((weightedBallBoundaryTestSeq (a ij.2) (ha ij.2) n).partialDeriv ij.1 x -
    spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x),
    sq_abs ((weightedBallBoundaryTestSeq (a ij.2) (ha ij.2) n).partialDeriv ij.1 x -
      spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x)]

/-- At every interior point the actual matrix gradient error eventually vanishes. -/
theorem weightedBallVectorTestSeq_gradient_eventually (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) {x : Vec3} (hx : x ∈ vec3Ball 0 1) :
    (fun n ↦ stokesTestGradient (weightedBallVectorTestSeq a ha n) x) =ᶠ[atTop]
      fun _ ↦ weightedBallMatrixGradient a x := by
  have hall : ∀ᶠ n in atTop, ∀ ij : Fin 3 × Fin 3,
      (weightedBallBoundaryTestSeq (a ij.2) (ha ij.2) n).partialDeriv ij.1 x =
        spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a ij.2 y) ij.1 x :=
    eventually_all.mpr (fun ij ↦
      weightedBallBoundaryTestSeq_partialDeriv_eventually (ha ij.2) hx ij.1)
  filter_upwards [hall] with n hn
  ext ij
  exact hn ij

/-- Actual dominated convergence makes the integrated matrix gradient error vanish. -/
theorem weightedBallVectorTestSeq_gradient_integral_error_tendsto (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) :
    Tendsto (fun n ↦ ∫ x in vec3Ball 0 1,
      ‖stokesTestGradient (weightedBallVectorTestSeq a ha n) x -
        weightedBallMatrixGradient a x‖ ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨T, hT, hb⟩ := exists_smoothTransition_deriv_bound
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (vec3Ball 0 1)) (f := fun _ ↦ (0 : ℝ))
    (F := fun n x ↦ ‖stokesTestGradient (weightedBallVectorTestSeq a ha n) x -
      weightedBallMatrixGradient a x‖ ^ 2)
    (weightedBallGradientErrorMajorant a T) ?_ ?_ ?_ ?_
  · simpa using h
  · intro n
    exact (((stokesTestGradient_continuous (weightedBallVectorTestSeq a ha n)).sub
      (weightedBallMatrixGradient_continuous a ha)).norm.pow 2).aestronglyMeasurable
  · exact weightedBallGradientErrorMajorant_integrable a ha T
  · intro n
    filter_upwards [ae_restrict_mem (vec3Ball_measurable 0 1)] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact weightedBallVectorTestSeq_gradient_error_sq_le a ha hT hb n hx
  · filter_upwards [ae_restrict_mem (vec3Ball_measurable 0 1)] with x hx
    have heq : (fun n ↦
        ‖stokesTestGradient (weightedBallVectorTestSeq a ha n) x -
          weightedBallMatrixGradient a x‖ ^ 2) =ᶠ[atTop] fun _ ↦ (0 : ℝ) := by
      filter_upwards [weightedBallVectorTestSeq_gradient_eventually a ha hx] with n hn
      simp only [hn, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact tendsto_const_nhds.congr' heq.symm

/-- The Hilbert norm square equals the actual integrated square error. -/
theorem weightedBallVectorTestSeq_gradient_L2_error_sq (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) (n : ℕ) :
    ‖stokesTestGradientL2 (weightedBallVectorTestSeq a ha n) -
      weightedBallMatrixGradientL2 a ha‖ ^ 2 =
      ∫ x in vec3Ball 0 1,
        ‖stokesTestGradient (weightedBallVectorTestSeq a ha n) x -
          weightedBallMatrixGradient a x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  have hf := (stokesTestGradient_memLp (weightedBallVectorTestSeq a ha n)).coeFn_toLp
  have hg := (weightedBallMatrixGradient_memLp a ha).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (stokesTestGradientL2 (weightedBallVectorTestSeq a ha n))
    (weightedBallMatrixGradientL2 a ha), hf, hg] with x hsub hfx hgx
  change stokesTestGradientL2 (weightedBallVectorTestSeq a ha n) x = _ at hfx
  change weightedBallMatrixGradientL2 a ha x = _ at hgx
  rw [hsub]
  simp only [Pi.sub_apply, hfx, hgx, real_inner_self_eq_norm_sq]

/-- The genuine compact test gradients converge strongly in the actual Hilbert space. -/
theorem weightedBallVectorTestSeq_gradient_L2_tendsto (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) :
    Tendsto (fun n ↦ stokesTestGradientL2 (weightedBallVectorTestSeq a ha n))
      atTop (𝓝 (weightedBallMatrixGradientL2 a ha)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun n ↦
      ‖stokesTestGradientL2 (weightedBallVectorTestSeq a ha n) -
        weightedBallMatrixGradientL2 a ha‖ ^ 2) atTop (𝓝 0) := by
    simpa only [weightedBallVectorTestSeq_gradient_L2_error_sq] using
      weightedBallVectorTestSeq_gradient_integral_error_tendsto a ha
  have hsqrt : Tendsto (fun n ↦ Real.sqrt
      (‖stokesTestGradientL2 (weightedBallVectorTestSeq a ha n) -
        weightedBallMatrixGradientL2 a ha‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have heq : (fun n ↦ Real.sqrt
      (‖stokesTestGradientL2 (weightedBallVectorTestSeq a ha n) -
        weightedBallMatrixGradientL2 a ha‖ ^ 2)) =
      fun n ↦ ‖stokesTestGradientL2 (weightedBallVectorTestSeq a ha n) -
        weightedBallMatrixGradientL2 a ha‖ := by
    funext n
    rw [Real.sqrt_sq_eq_abs, abs_norm]
  rw [heq, Real.sqrt_zero] at hsqrt
  exact hsqrt

/-- The actual gradient belongs to the constructed zero-boundary Stokes energy completion. -/
theorem weightedBallMatrixGradientL2_mem_energy (a : Fin 3 → Vec3 → ℝ)
    (ha : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) :
    weightedBallMatrixGradientL2 a ha ∈ stokesGradientEnergySpace (vec3Ball 0 1) := by
  exact (stokesGradientEnergySpace (vec3Ball 0 1)).isClosed.mem_of_tendsto
    (weightedBallVectorTestSeq_gradient_L2_tendsto a ha)
    (.of_forall (fun n ↦ stokesTestGradientL2_mem (weightedBallVectorTestSeq a ha n)))

end FluidSingularSets
