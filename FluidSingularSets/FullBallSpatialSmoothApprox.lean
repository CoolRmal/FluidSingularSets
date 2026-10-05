-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicValues
public import FluidSingularSets.HarmonicSpatialSmoothApprox

/-!
# Genuine spatial harmonic smoothing with arbitrary interior radii

A true canonical cutoff extends the whole-ball pressure representative to a
compact global C² potential. Its genuine convolution preserves harmonicity
inside any smaller ball whose boundary margin exceeds the smoothing radius.
The actual first and second derivatives converge uniformly.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance fullBallSpatialForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallSpatialForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual canonical cutoff between arbitrary interior radii. -/
def fullBallSpatialCutoff (σ θ : ℝ) : Vec3 → ℝ := canonicalBallCutoff 0 σ θ

/-- The actual full-ball pressure of the canonically projected force. -/
def fullBallSpatialPressureRepresentative (F : StokesEnergyForce (vec3Ball 0 1)) : Vec3 → ℝ :=
  unitBallFullHarmonicForcePressureRepresentative (unitBallGradientFreeForceProjection F)

/-- The genuine compact pressure extension with arbitrary boundary margin. -/
def fullBallSpatialCutoffPressure (σ θ : ℝ) (F : StokesEnergyForce (vec3Ball 0 1)) :
    Vec3 → ℝ := fun x ↦ fullBallSpatialCutoff σ θ x * fullBallSpatialPressureRepresentative F x

variable {σ θ : ℝ}

/-- The actual cutoff is smooth for arbitrary valid radii. -/
theorem fullBallSpatialCutoff_smooth (hσ : 0 < σ) (hσθ : σ < θ) :
    ContDiff ℝ (⊤ : ℕ∞) (fullBallSpatialCutoff σ θ) :=
  canonicalBallCutoff_smooth 0 hσ.le hσθ

/-- The actual cutoff support lies strictly inside the outer radius. -/
theorem fullBallSpatialCutoff_support (hσ : 0 < σ) (hσθ : σ < θ) :
    tsupport (fullBallSpatialCutoff σ θ) ⊆ vec3Ball 0 θ := by
  have h := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec3)) hσ.le hσθ
  rwa [euclideanBall_eq_vec3Ball (hσ.trans hσθ)] at h

/-- The actual cutoff equals one throughout the chosen inner ball. -/
theorem fullBallSpatialCutoff_one (hσ : 0 < σ) (hσθ : σ < θ)
    {x : Vec3} (hx : x ∈ vec3Ball 0 σ) : fullBallSpatialCutoff σ θ x = 1 := by
  apply canonicalBallCutoff_eq_one_on_inner hσ.le hσθ
  rwa [euclideanBall_eq_vec3Ball hσ]

/-- The true extension is globally C². -/
theorem fullBallSpatialCutoffPressure_contDiff (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    ContDiff ℝ (2 : ℕ∞) (fullBallSpatialCutoffPressure σ θ F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ vec3Ball (0 : Vec3) 1
  · exact ((fullBallSpatialCutoff_smooth hσ hσθ).contDiffAt.of_le (by norm_num)).mul
      ((unitBallFullHarmonicForcePressureRepresentative_contDiff _).contDiffAt
        ((isOpen_vec3Ball 0 1).mem_nhds hx))
  · have hn : x ∉ tsupport (fullBallSpatialCutoff σ θ) :=
      fun h ↦ hx ((vec3Ball_mono hθ.le) (fullBallSpatialCutoff_support hσ hσθ h))
    have hz : fullBallSpatialCutoffPressure σ θ F =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
      ((isClosed_tsupport (fullBallSpatialCutoff σ θ)).isOpen_compl.eventually_mem hn).mono
        fun y hy ↦ by
          simp only [fullBallSpatialCutoffPressure, image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- The literal extension has actual compact support. -/
theorem fullBallSpatialCutoffPressure_hasCompactSupport (hσ : 0 < σ) (hσθ : σ < θ)
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    HasCompactSupport (fullBallSpatialCutoffPressure σ θ F) :=
  (canonicalBallCutoff_hasCompactSupport (x₀ := (0 : Vec3)) hσ.le hσθ).mul_right

/-- The actual extension agrees with the whole-ball potential on the entire inner ball. -/
theorem fullBallSpatialCutoffPressure_eqOn (hσ : 0 < σ) (hσθ : σ < θ)
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    EqOn (fullBallSpatialCutoffPressure σ θ F) (fullBallSpatialPressureRepresentative F)
      (vec3Ball 0 σ) := by
  intro x hx
  simp only [fullBallSpatialCutoffPressure, fullBallSpatialCutoff_one hσ hσθ hx, one_mul]

/-- The genuine cutoff potential retains the actual inner harmonic equation. -/
theorem fullBallSpatialCutoffPressure_weaklyHarmonic
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1) (F : StokesEnergyForce (vec3Ball 0 1)) :
    WeaklyHarmonicOn (vec3Ball 0 σ) (fullBallSpatialCutoffPressure σ θ F) := by
  apply localWeaklyHarmonicOn_congr_ae
    (ae_restrict_mem (isOpen_vec3Ball 0 σ).measurableSet |>.mono
      fun x hx ↦ (fullBallSpatialCutoffPressure_eqOn hσ hσθ F hx).symm)
  exact localWeaklyHarmonicOn_restrict (vec3Ball_mono (hσθ.trans hθ).le)
    (unitBallFullHarmonicForcePressureRepresentative_weaklyHarmonic _)

/-- Genuine convolution of the actual compact C² potential. -/
def fullBallSpatialSmoothPressure (σ θ : ℝ) (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) : Vec3 → ℝ := mollify (fullBallSpatialCutoffPressure σ θ F) ε hε

/-- The literal gradient of that same smoothed pressure. -/
def fullBallSpatialSmoothGradient (σ θ : ℝ) (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) : Vec3 → Vec3 :=
  classicalGradient (fullBallSpatialSmoothPressure σ θ F hε)

/-- The actual pressure convolution is globally smooth. -/
theorem fullBallSpatialSmoothPressure_contDiff (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fullBallSpatialSmoothPressure σ θ F hε) :=
  mollify_contDiff hε
    ((fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).continuous.locallyIntegrable)

/-- The literal actual gradient convolution is globally smooth. -/
theorem fullBallSpatialSmoothGradient_contDiff (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fullBallSpatialSmoothGradient σ θ F hε) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_spatialDeriv_smooth (fullBallSpatialSmoothPressure_contDiff hσ hσθ hθ F hε) i

private theorem fullBallSpatial_mollify_eq_of_closedBall_eq
    {f g : Vec3 → ℝ} {ε : ℝ} (hε : 0 < ε) {x : Vec3}
    (heq : EqOn f g (Metric.closedBall x ε)) : mollify f ε hε x = mollify g ε hε x := by
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Metric.closedBall (0 : Vec3) ε
  · have hxy : x - y ∈ Metric.closedBall x ε := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
        sub_zero] using hy
    rw [heq hxy]
  · have hz : mollifier (d := 3) ε hε y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (mollifier_tsupp_eq_closedBall hε ▸ h))
    simp only [hz, ContinuousLinearMap.map_zero, zero_apply]

/-- The real smoothing neighborhoods fit strictly inside the larger harmonic ball. -/
theorem fullBallSpatial_closedBall_inner {ρ ε : ℝ} (hρσ : ρ < σ)
    {x : Vec3} (hx : x ∈ vec3Ball 0 ρ) (hε : ε ≤ (σ - ρ) / 6) :
    Metric.closedBall x ε ⊆ vec3Ball 0 σ := by
  intro y hy
  rw [mem_vec3Ball] at hx ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have hn : vec3EuclideanNorm (y - x) ≤ 3 * ε :=
    (euclideanNorm_le_three_mul_space_norm (y - x)).trans
    (mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 3))
  have ht := vec3EuclideanNorm_add_le (y - x) x
  rw [sub_add_cancel] at ht
  norm_num only [sub_zero] at hx ⊢
  linarith

/-- Actual smoothing preserves the harmonic equation throughout any smaller ball. -/
theorem fullBallSpatialSmoothPressure_laplacian
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1) (F : StokesEnergyForce (vec3Ball 0 1))
    {ρ ε : ℝ} (hρσ : ρ < σ) (hε : 0 < ε) (hsmall : ε ≤ (σ - ρ) / 6) :
    ∀ x ∈ vec3Ball 0 ρ, spatialLaplacian (fullBallSpatialSmoothPressure σ θ F hε) x = 0 := by
  let U := vec3Ball (0 : Vec3) σ
  let g := fullBallSpatialCutoffPressure σ θ F
  have heq : EqOn (mollify g ε hε) (mollify (U.indicator g) ε hε) (vec3Ball 0 ρ) := by
    intro x hx
    apply fullBallSpatial_mollify_eq_of_closedBall_eq hε
    intro y hy
    exact (indicator_of_mem (fullBallSpatial_closedBall_inner hρσ hx hsmall hy) g).symm
  have hsec := mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 ρ) heq
  intro x hx
  have hlap : spatialLaplacian (mollify g ε hε) x =
      spatialLaplacian (mollify (U.indicator g) ε hε) x :=
    Finset.sum_congr rfl (fun i _ ↦ hsec i i hx)
  change spatialLaplacian (mollify g ε hε) x = 0
  rw [hlap]
  exact weaklyHarmonicOn_mollify_spatialLaplacian_eq_zero
    (isOpen_vec3Ball 0 σ).measurableSet
    (((fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).continuous.memLp_of_hasCompactSupport
      (fullBallSpatialCutoffPressure_hasCompactSupport hσ hσθ F)).mono_measure
        Measure.restrict_le_self)
    (fullBallSpatialCutoffPressure_weaklyHarmonic hσ hσθ hθ F) hε
    (fullBallSpatial_closedBall_inner hρσ hx hsmall)

/-- The actual smoothed gradient is divergence-free on every valid smaller ball. -/
theorem fullBallSpatialSmoothGradient_divergence
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1) (F : StokesEnergyForce (vec3Ball 0 1))
    {ρ ε : ℝ} (hρσ : ρ < σ) (hε : 0 < ε) (hsmall : ε ≤ (σ - ρ) / 6) :
    ∀ x ∈ vec3Ball 0 ρ,
      (∑ i : Fin 3, spatialDeriv (fun y ↦ fullBallSpatialSmoothGradient σ θ F hε y i) i x) = 0 :=
  fullBallSpatialSmoothPressure_laplacian hσ hσθ hθ F hρσ hε hsmall

/-- Every actual gradient component retains harmonicity on the chosen smaller ball. -/
theorem fullBallSpatialSmoothGradient_harmonic
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1) (F : StokesEnergyForce (vec3Ball 0 1))
    {ρ ε : ℝ} (hρσ : ρ < σ) (hε : 0 < ε) (hsmall : ε ≤ (σ - ρ) / 6) :
    ∀ i : Fin 3, ∀ x ∈ vec3Ball 0 ρ,
      spatialLaplacian (fun y ↦ fullBallSpatialSmoothGradient σ θ F hε y i) x = 0 := by
  intro i x hx
  have hz : EqOn (spatialLaplacian (fullBallSpatialSmoothPressure σ θ F hε))
      (fun _ ↦ (0 : ℝ)) (vec3Ball 0 ρ) :=
    fullBallSpatialSmoothPressure_laplacian hσ hσθ hθ F hρσ hε hsmall
  have hi := congrArg (fun v : Vec3 ↦ v i)
    (classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 ρ) hz hx)
  change spatialLaplacian (spatialDeriv (fullBallSpatialSmoothPressure σ θ F hε) i) x = 0
  rw [spatialLaplacian_spatialDeriv_commute
    (fullBallSpatialSmoothPressure_contDiff hσ hσθ hθ F hε) i]
  simpa only [classicalGradient, spatialDeriv, fderiv_const_apply, zero_apply] using hi

private theorem fullBallSpatial_partial_contDiff {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (i : Fin 3) : ContDiff ℝ (1 : ℕ∞) (spatialDeriv f i) := by
  have h := hf.contDiff_fderiv_apply (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) (by norm_num)
  exact h.comp (contDiff_id.prodMk contDiff_const)

/-- Actual convolution commutes with the first derivatives of the genuine compact pressure. -/
theorem fullBallSpatialSmoothPressure_spatialDeriv
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    spatialDeriv (fullBallSpatialSmoothPressure σ θ F hε) i =
      mollify (spatialDeriv (fullBallSpatialCutoffPressure σ θ F) i) ε hε := by
  funext x
  exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
    ((fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).continuous.locallyIntegrable)
    ((fullBallSpatial_partial_contDiff
      (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F) i).continuous.locallyIntegrable)
    (HasWeakPartialDerivOn.of_contDiff
      ((fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).of_le (by norm_num))) hε
    (subset_univ _)

/-- Actual convolution commutes with the literal second derivatives of that same pressure. -/
theorem fullBallSpatialSmoothPressure_mixedSecond
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    mixedSecond (fullBallSpatialSmoothPressure σ θ F hε) i j =
      mollify (mixedSecond (fullBallSpatialCutoffPressure σ θ F) i j) ε hε := by
  unfold mixedSecond
  rw [fullBallSpatialSmoothPressure_spatialDeriv hσ hσθ hθ]
  funext x
  have hj := fullBallSpatial_partial_contDiff
    (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F) j
  exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
    hj.continuous.locallyIntegrable
    ((hj.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable
    (HasWeakPartialDerivOn.of_contDiff hj) hε (subset_univ _)

/-- The actual pressure approximants converge uniformly to the compact potential. -/
theorem fullBallSpatialSmoothPressure_tendstoUniformly
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly (fun n ↦ fullBallSpatialSmoothPressure σ θ F (hpos n))
      (fullBallSpatialCutoffPressure σ θ F) atTop :=
  tendstoUniformly_mollify_of_compact_continuous
    (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).continuous
    (fullBallSpatialCutoffPressure_hasCompactSupport hσ hσθ F) hε hpos

/-- The true first derivatives converge uniformly, retaining the actual gradient. -/
theorem fullBallSpatialSmoothPressure_spatialDeriv_tendstoUniformly
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) (i : Fin 3)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly (fun n ↦ spatialDeriv (fullBallSpatialSmoothPressure σ θ F (hpos n)) i)
      (spatialDeriv (fullBallSpatialCutoffPressure σ θ F) i) atTop := by
  simp_rw [fullBallSpatialSmoothPressure_spatialDeriv hσ hσθ hθ]
  exact tendstoUniformly_mollify_of_compact_continuous
    (fullBallSpatial_partial_contDiff (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F)
      i).continuous
    ((fullBallSpatialCutoffPressure_hasCompactSupport hσ hσθ F).fderiv_apply (𝕜 := ℝ) (basisVec i))
    hε hpos

/-- The genuine Hessian approximants converge uniformly as well. -/
theorem fullBallSpatialSmoothPressure_mixedSecond_tendstoUniformly
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) (i j : Fin 3)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly (fun n ↦ mixedSecond (fullBallSpatialSmoothPressure σ θ F (hpos n)) i j)
      (mixedSecond (fullBallSpatialCutoffPressure σ θ F) i j) atTop := by
  simp_rw [fullBallSpatialSmoothPressure_mixedSecond hσ hσθ hθ]
  have hj := fullBallSpatial_partial_contDiff (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F) j
  exact tendstoUniformly_mollify_of_compact_continuous
    ((hj.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (((fullBallSpatialCutoffPressure_hasCompactSupport hσ hσθ F).fderiv_apply
      (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ) (basisVec i)) hε hpos


end FluidSingularSets
