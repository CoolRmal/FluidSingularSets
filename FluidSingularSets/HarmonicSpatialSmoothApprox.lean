-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableHarmonicGradientTime
public import CKN.Foundation.Sobolev.Mollify.Transport
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Spatial smoothing inside the genuine harmonic-pressure image

The actual gradient-free projection gives a genuine C² harmonic pressure
representative. A fixed compact cutoff extends that potential as a genuine
global C² function. Spatial convolution makes the potential globally smooth,
and its true gradient retains interior harmonicity and zero divergence.
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

local instance harmonicSpatialSmoothForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicSpatialSmoothForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- A fixed genuine compact smooth cutoff inside the pressure representative domain. -/
def harmonicSpatialCutoff : Vec3 → ℝ :=
  mollifiedBallCutoff 0 (by norm_num : (0 : ℝ) < 1 / 4)

private theorem harmonicSpatialCutoff_smooth :
    ContDiff ℝ (⊤ : ℕ∞) harmonicSpatialCutoff :=
  mollifiedBallCutoff_smooth 0 (by norm_num)

private theorem harmonicSpatialCutoff_support :
    tsupport harmonicSpatialCutoff ⊆ vec3Ball 0 (1 / 4) := by
  have h := mollifiedBallCutoff_tsupport_subset_outer 0
    (by norm_num : (0 : ℝ) < 1 / 4)
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 3 * (1 / 4) / 4)] at h
  exact h.trans (vec3Ball_mono (by norm_num))

private theorem harmonicSpatialCutoff_one {x : Vec3} (hx : x ∈ vec3Ball 0 (1 / 8)) :
    harmonicSpatialCutoff x = 1 := by
  apply mollifiedBallCutoff_eq_one_on_inner
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 13 * (1 / 4) / 20)]
  exact vec3Ball_mono (by norm_num) hx

/-- The genuine canonical harmonic potential of the actual projected energy force. -/
def harmonicSpatialPressureRepresentative (F : StokesEnergyForce (vec3Ball 0 1)) : Vec3 → ℝ :=
  unitBallHarmonicForcePressureRepresentative (unitBallGradientFreeForceProjection F)

/-- The genuine compact global C² extension of the canonical interior potential. -/
def harmonicSpatialCutoffPressure (F : StokesEnergyForce (vec3Ball 0 1)) : Vec3 → ℝ :=
  fun x ↦ harmonicSpatialCutoff x * harmonicSpatialPressureRepresentative F x

theorem harmonicSpatialCutoffPressure_contDiff (F : StokesEnergyForce (vec3Ball 0 1)) :
    ContDiff ℝ (2 : ℕ∞) (harmonicSpatialCutoffPressure F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ vec3Ball (0 : Vec3) (1 / 4)
  · exact (harmonicSpatialCutoff_smooth.contDiffAt.of_le (by norm_num)).mul
      ((unitBallHarmonicForcePressureRepresentative_contDiff _).contDiffAt
        ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hx))
  · have hnot : x ∉ tsupport harmonicSpatialCutoff :=
      fun h ↦ hx (harmonicSpatialCutoff_support h)
    have hz : harmonicSpatialCutoffPressure F =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
      ((isClosed_tsupport harmonicSpatialCutoff).isOpen_compl.eventually_mem hnot).mono
        fun y hy ↦ by
          simp only [harmonicSpatialCutoffPressure,
            image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem harmonicSpatialCutoffPressure_hasCompactSupport
    (F : StokesEnergyForce (vec3Ball 0 1)) : HasCompactSupport (harmonicSpatialCutoffPressure F) :=
  (mollifiedBallCutoff_hasCompactSupport 0 (by norm_num : (0 : ℝ) < 1 / 4)).mul_right

/-- The global extension agrees literally with the genuine potential on the inner ball. -/
theorem harmonicSpatialCutoffPressure_eqOn (F : StokesEnergyForce (vec3Ball 0 1)) :
    EqOn (harmonicSpatialCutoffPressure F) (harmonicSpatialPressureRepresentative F)
      (vec3Ball 0 (1 / 8)) := by
  intro x hx
  simp only [harmonicSpatialCutoffPressure, harmonicSpatialCutoff_one hx, one_mul]

theorem harmonicSpatialCutoffPressure_weaklyHarmonic
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    WeaklyHarmonicOn (vec3Ball 0 (1 / 8)) (harmonicSpatialCutoffPressure F) := by
  apply localWeaklyHarmonicOn_congr_ae
    (ae_restrict_mem (isOpen_vec3Ball 0 (1 / 8)).measurableSet |>.mono
      fun x hx ↦ (harmonicSpatialCutoffPressure_eqOn F hx).symm)
  exact localWeaklyHarmonicOn_restrict (vec3Ball_mono (by norm_num))
    (unitBallHarmonicForcePressureRepresentative_weaklyHarmonic _)

/-- Spatial convolution of the actual compact C² harmonic-pressure extension. -/
def harmonicSpatialSmoothPressure (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) : Vec3 → ℝ :=
  mollify (harmonicSpatialCutoffPressure F) ε hε

/-- The genuine smooth harmonic-gradient approximation. -/
def harmonicSpatialSmoothGradient (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) : Vec3 → Vec3 :=
  classicalGradient (harmonicSpatialSmoothPressure F hε)

theorem harmonicSpatialSmoothPressure_contDiff (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (harmonicSpatialSmoothPressure F hε) :=
  mollify_contDiff hε
    ((harmonicSpatialCutoffPressure_contDiff F).continuous.locallyIntegrable)

theorem harmonicSpatialSmoothGradient_contDiff (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (harmonicSpatialSmoothGradient F hε) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_spatialDeriv_smooth (harmonicSpatialSmoothPressure_contDiff F hε) i

private theorem harmonicSpatial_mollify_eq_of_closedBall_eq
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

private theorem harmonicSpatial_closedBall_inner {x : Vec3}
    (hx : x ∈ vec3Ball 0 (1 / 12)) {ε : ℝ} (hε : ε ≤ 1 / 100) :
    Metric.closedBall x ε ⊆ vec3Ball 0 (1 / 8) := by
  intro y hy
  rw [mem_vec3Ball] at hx ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have hnorm := euclideanNorm_le_three_mul_space_norm (y - x)
  have hsum := vec3EuclideanNorm_add_le (y - x) x
  have heq : y = (y - x) + x := sub_add_cancel y x |>.symm
  rw [heq, sub_zero]
  have hn : vec3EuclideanNorm (y - x) ≤ 3 * ε := by
    exact hnorm.trans (mul_le_mul_of_nonneg_left hy (by norm_num))
  norm_num only [sub_zero] at hx
  linarith

/-- Spatial smoothing preserves the genuine interior harmonic equation exactly. -/
theorem harmonicSpatialSmoothPressure_laplacian (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) :
    ∀ x ∈ vec3Ball 0 (1 / 12), spatialLaplacian (harmonicSpatialSmoothPressure F hε) x = 0 := by
  let U := vec3Ball (0 : Vec3) (1 / 8)
  let g := harmonicSpatialCutoffPressure F
  have heq : EqOn (mollify g ε hε) (mollify (U.indicator g) ε hε)
      (vec3Ball 0 (1 / 12)) := by
    intro x hx
    apply harmonicSpatial_mollify_eq_of_closedBall_eq hε
    intro y hy
    exact (indicator_of_mem (harmonicSpatial_closedBall_inner hx hsmall hy) g).symm
  have hsec := mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 12)) heq
  intro x hx
  have hlap : spatialLaplacian (mollify g ε hε) x =
      spatialLaplacian (mollify (U.indicator g) ε hε) x := by
    exact Finset.sum_congr rfl (fun i _ ↦ hsec i i hx)
  change spatialLaplacian (mollify g ε hε) x = 0
  rw [hlap]
  exact weaklyHarmonicOn_mollify_spatialLaplacian_eq_zero
    (isOpen_vec3Ball 0 (1 / 8)).measurableSet
    (((harmonicSpatialCutoffPressure_contDiff F).continuous.memLp_of_hasCompactSupport
      (harmonicSpatialCutoffPressure_hasCompactSupport F)).mono_measure Measure.restrict_le_self)
    (harmonicSpatialCutoffPressure_weaklyHarmonic F) hε
    (harmonicSpatial_closedBall_inner hx hsmall)

/-- The actual smoothed gradient is divergence-free on the fixed interior ball. -/
theorem harmonicSpatialSmoothGradient_divergence (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) :
    ∀ x ∈ vec3Ball 0 (1 / 12),
      (∑ i : Fin 3, spatialDeriv (fun y ↦ harmonicSpatialSmoothGradient F hε y i) i x) = 0 :=
  harmonicSpatialSmoothPressure_laplacian F hε hsmall

/-- Every component of the genuine gradient approximation is harmonic on the inner ball. -/
theorem harmonicSpatialSmoothGradient_harmonic (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) :
    ∀ i : Fin 3, ∀ x ∈ vec3Ball 0 (1 / 12),
      spatialLaplacian (fun y ↦ harmonicSpatialSmoothGradient F hε y i) x = 0 := by
  intro i x hx
  have hz : EqOn (spatialLaplacian (harmonicSpatialSmoothPressure F hε))
      (fun _ ↦ (0 : ℝ)) (vec3Ball 0 (1 / 12)) :=
    harmonicSpatialSmoothPressure_laplacian F hε hsmall
  have hd := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 12)) hz hx
  have hi := congrArg (fun v : Vec3 ↦ v i) hd
  change spatialLaplacian (spatialDeriv (harmonicSpatialSmoothPressure F hε) i) x = 0
  rw [spatialLaplacian_spatialDeriv_commute (harmonicSpatialSmoothPressure_contDiff F hε) i]
  simpa only [classicalGradient, spatialDeriv, fderiv_const_apply, zero_apply] using hi

private theorem harmonicSpatial_partial_contDiff {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (i : Fin 3) : ContDiff ℝ (1 : ℕ∞) (spatialDeriv f i) := by
  have h := hf.contDiff_fderiv_apply (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) (by norm_num)
  exact h.comp (contDiff_id.prodMk contDiff_const)

/-- Convolution of the actual compact C² potential commutes with its true first derivatives. -/
theorem harmonicSpatialSmoothPressure_spatialDeriv
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    spatialDeriv (harmonicSpatialSmoothPressure F hε) i =
      mollify (spatialDeriv (harmonicSpatialCutoffPressure F) i) ε hε := by
  funext x
  exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
    ((harmonicSpatialCutoffPressure_contDiff F).continuous.locallyIntegrable)
    ((harmonicSpatial_partial_contDiff
      (harmonicSpatialCutoffPressure_contDiff F) i).continuous.locallyIntegrable)
    (HasWeakPartialDerivOn.of_contDiff
      ((harmonicSpatialCutoffPressure_contDiff F).of_le (by norm_num))) hε (subset_univ _)

/-- The actual Hessians commute with the same genuine spatial convolution. -/
theorem harmonicSpatialSmoothPressure_mixedSecond
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    mixedSecond (harmonicSpatialSmoothPressure F hε) i j =
      mollify (mixedSecond (harmonicSpatialCutoffPressure F) i j) ε hε := by
  unfold mixedSecond
  rw [harmonicSpatialSmoothPressure_spatialDeriv]
  funext x
  have hj := harmonicSpatial_partial_contDiff (harmonicSpatialCutoffPressure_contDiff F) j
  exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
    hj.continuous.locallyIntegrable
    ((hj.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable
    (HasWeakPartialDerivOn.of_contDiff hj) hε (subset_univ _)

/-- Compact continuous functions converge uniformly under the genuine normalized mollifiers. -/
theorem tendstoUniformly_mollify_of_compact_continuous
    {f : Vec3 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly (fun n ↦ mollify f (ε n) (hpos n)) f atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  obtain ⟨r, hr, hdist⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hf) (δ / 2) (by positivity)
  filter_upwards [(tendsto_order.mp hε).2 r hr] with n hn x
  have hb := (standardMollifier (d := 3) (ε n) (hpos n)).dist_normed_convolution_le
    (μ := volume) hf.aestronglyMeasurable (x₀ := x) (ε := δ / 2) (by
      intro y hy
      exact (hdist ((Metric.mem_ball.mp hy).trans hn)).le)
  rw [dist_comm]
  exact hb.trans_lt (half_lt_self hδ)

/-- The actual pressure approximants converge uniformly to the compact potential. -/
theorem harmonicSpatialSmoothPressure_tendstoUniformly
    (F : StokesEnergyForce (vec3Ball 0 1))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly (fun n ↦ harmonicSpatialSmoothPressure F (hpos n))
      (harmonicSpatialCutoffPressure F) atTop :=
  tendstoUniformly_mollify_of_compact_continuous
    (harmonicSpatialCutoffPressure_contDiff F).continuous
    (harmonicSpatialCutoffPressure_hasCompactSupport F) hε hpos

/-- The true first derivatives converge uniformly, retaining the actual gradient. -/
theorem harmonicSpatialSmoothPressure_spatialDeriv_tendstoUniformly
    (F : StokesEnergyForce (vec3Ball 0 1)) (i : Fin 3)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly (fun n ↦ spatialDeriv (harmonicSpatialSmoothPressure F (hpos n)) i)
      (spatialDeriv (harmonicSpatialCutoffPressure F) i) atTop := by
  simp_rw [harmonicSpatialSmoothPressure_spatialDeriv]
  exact tendstoUniformly_mollify_of_compact_continuous
    (harmonicSpatial_partial_contDiff (harmonicSpatialCutoffPressure_contDiff F) i).continuous
    ((harmonicSpatialCutoffPressure_hasCompactSupport F).fderiv_apply (𝕜 := ℝ) (basisVec i))
    hε hpos

/-- The genuine Hessian approximants converge uniformly as well. -/
theorem harmonicSpatialSmoothPressure_mixedSecond_tendstoUniformly
    (F : StokesEnergyForce (vec3Ball 0 1)) (i j : Fin 3)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly (fun n ↦ mixedSecond (harmonicSpatialSmoothPressure F (hpos n)) i j)
      (mixedSecond (harmonicSpatialCutoffPressure F) i j) atTop := by
  simp_rw [harmonicSpatialSmoothPressure_mixedSecond]
  have hj := harmonicSpatial_partial_contDiff (harmonicSpatialCutoffPressure_contDiff F) j
  exact tendstoUniformly_mollify_of_compact_continuous
    ((hj.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (((harmonicSpatialCutoffPressure_hasCompactSupport F).fderiv_apply
      (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ) (basisVec i)) hε hpos

/-- On the real compact interior, the limit is the canonical force-gradient image itself. -/
theorem harmonicSpatialSmoothGradient_component_tendstoUniformly
    (F : StokesEnergyForce (vec3Ball 0 1)) (i : Fin 3)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    TendstoUniformly
      (fun n (x : unitBallPressureCompactInterior) ↦ harmonicSpatialSmoothGradient F (hpos n) x i)
      (fun x ↦ unitBallHarmonicForceGradientExtended F x i) atTop := by
  have h := (harmonicSpatialSmoothPressure_spatialDeriv_tendstoUniformly F i hε hpos).comp
    (Subtype.val : unitBallPressureCompactInterior → Vec3)
  have heq : (fun x : unitBallPressureCompactInterior ↦
      spatialDeriv (harmonicSpatialCutoffPressure F) i x) =
      fun x ↦ unitBallHarmonicForceGradientExtended F x i := by
    funext x
    have hx : x.1 ∈ vec3Ball 0 (1 / 8) := by
      have hk := x.property
      change x.1 ∈ closure (vec3Ball 0 (1 / 16)) at hk
      rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)] at hk
      change vec3EuclideanNorm (x.1 - 0) ≤ 1 / 16 at hk
      exact hk.trans_lt (by norm_num)
    have hd := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 8))
      (harmonicSpatialCutoffPressure_eqOn F) hx
    exact congrArg (fun v : Vec3 ↦ v i) hd
  exact heq ▸ h

/-- The compact scalar potential is approximated strongly at every finite exponent at least one. -/
theorem harmonicSpatialSmoothPressure_strongLp
    (F : StokesEnergyForce (vec3Ball 0 1)) {P : ℝ≥0∞} (hP : 1 ≤ P) (hPfin : P ≠ ⊤)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ harmonicSpatialSmoothPressure F (hpos n) x -
      harmonicSpatialCutoffPressure F x) P volume) atTop (𝓝 0) :=
  tendsto_eLpNorm_sub_zero_mollify hP hPfin
    ((harmonicSpatialCutoffPressure_contDiff F).continuous.memLp_of_hasCompactSupport
      (harmonicSpatialCutoffPressure_hasCompactSupport F)) hε hpos

/-- The genuine gradient coordinates converge strongly at the same finite exponents. -/
theorem harmonicSpatialSmoothPressure_spatialDeriv_strongLp
    (F : StokesEnergyForce (vec3Ball 0 1)) (i : Fin 3)
    {P : ℝ≥0∞} (hP : 1 ≤ P) (hPfin : P ≠ ⊤)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦
      spatialDeriv (harmonicSpatialSmoothPressure F (hpos n)) i x -
        spatialDeriv (harmonicSpatialCutoffPressure F) i x) P volume) atTop (𝓝 0) := by
  simp_rw [harmonicSpatialSmoothPressure_spatialDeriv]
  have hc :=
    (harmonicSpatial_partial_contDiff (harmonicSpatialCutoffPressure_contDiff F) i).continuous
  have hs := (harmonicSpatialCutoffPressure_hasCompactSupport F).fderiv_apply
    (𝕜 := ℝ) (basisVec i)
  exact tendsto_eLpNorm_sub_zero_mollify hP hPfin
    (hc.memLp_of_hasCompactSupport hs) hε hpos

/-- Actual Hessian coordinates also converge strongly at every such exponent. -/
theorem harmonicSpatialSmoothPressure_mixedSecond_strongLp
    (F : StokesEnergyForce (vec3Ball 0 1)) (i j : Fin 3)
    {P : ℝ≥0∞} (hP : 1 ≤ P) (hPfin : P ≠ ⊤)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦
      mixedSecond (harmonicSpatialSmoothPressure F (hpos n)) i j x -
        mixedSecond (harmonicSpatialCutoffPressure F) i j x) P volume) atTop (𝓝 0) := by
  simp_rw [harmonicSpatialSmoothPressure_mixedSecond]
  have hj := harmonicSpatial_partial_contDiff (harmonicSpatialCutoffPressure_contDiff F) j
  have hc : Continuous (mixedSecond (harmonicSpatialCutoffPressure F) i j) :=
    (hj.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hs := ((harmonicSpatialCutoffPressure_hasCompactSupport F).fderiv_apply
    (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact tendsto_eLpNorm_sub_zero_mollify hP hPfin
    (hc.memLp_of_hasCompactSupport hs) hε hpos

end FluidSingularSets
