-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCylinderCutoff
public import FluidSingularSets.FullBallProjectedLocalEnergy
public import CKN.Core.Caccioppoli.I1
public import CKN.Foundation.Heat.GaussianDisplayFaithful

/-!
# Actual Gaussian tests on the original projected time interval

The Gaussian is centered at time zero. Its smooth compact cutoff ends strictly
before zero and equals one on terminally truncated inner cylinders. The final
time ramp has nonpositive derivative, so quantitative upper heat bounds do not
depend on its width. All Gaussian formulas and bounds are reused from CKN.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Heat
open scoped Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The genuine time cutoff has its lower plateau at `-ρ²/4` and top at `-δ`. -/
def projectedGaussianTimeCutoff (ρ δ : ℝ) : ℝ → ℝ :=
  projectedCylinderTimeCutoff (-ρ ^ 2 / 2) (-δ / 2) (ρ ^ 2 / 4) (δ / 2)

/-- The actual compact spatial and temporal multiplier of the Gaussian. -/
def projectedGaussianMultiplier (ρ δ : ℝ) (hρ : 0 < ρ) : Vec3 × ℝ → ℝ :=
  fun z ↦ mollifiedBallCutoff 0 hρ z.1 * projectedGaussianTimeCutoff ρ δ z.2

/-- The genuine globally smooth truncated backward Gaussian test. -/
def projectedGaussianTest (r ρ δ : ℝ) (hρ : 0 < ρ) : Vec3 × ℝ → ℝ :=
  backwardHeat_cutoff (projectedGaussianMultiplier ρ δ hρ) 0 0 r

/-- The literal multiplier is smooth in space and time. -/
theorem projectedGaussianMultiplier_smooth {ρ δ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ ∞ (projectedGaussianMultiplier ρ δ hρ) :=
  ((mollifiedBallCutoff_smooth 0 hρ).comp contDiff_fst).mul
    ((projectedCylinderTimeCutoff_smooth _ _ _ _).comp contDiff_snd)

/-- The literal multiplier lies between zero and one. -/
theorem projectedGaussianMultiplier_bounds {ρ δ : ℝ} (hρ : 0 < ρ)
    (z : Vec3 × ℝ) :
    0 ≤ projectedGaussianMultiplier ρ δ hρ z ∧
      projectedGaussianMultiplier ρ δ hρ z ≤ 1 := by
  have hb := mollifiedBallCutoff_nonneg (0 : Vec3) hρ z.1
  have ht := projectedCylinderTimeCutoff_nonneg (-ρ ^ 2 / 2) (-δ / 2)
    (ρ ^ 2 / 4) (δ / 2) z.2
  refine ⟨mul_nonneg hb ht, ?_⟩
  exact (mul_le_mul_of_nonneg_right (mollifiedBallCutoff_le_one 0 hρ z.1) ht).trans
    (by simpa using (projectedCylinderTimeCutoff_le_one (-ρ ^ 2 / 2) (-δ / 2)
      (ρ ^ 2 / 4) (δ / 2) z.2))

/-- Actual topological support keeps a strict spatial margin and a strict future margin. -/
theorem projectedGaussianMultiplier_tsupport {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) :
    tsupport (projectedGaussianMultiplier ρ δ hρ) ⊆
      tsupport (mollifiedBallCutoff 0 hρ) ×ˢ Icc (-ρ ^ 2 / 2) (-δ / 2) := by
  apply closure_minimal _ ((isClosed_tsupport _).prod isClosed_Icc)
  intro z hz
  constructor
  · by_contra hx
    exact hz (by simp [projectedGaussianMultiplier, image_eq_zero_of_notMem_tsupport hx])
  · by_contra ht
    exact hz (by simp only [projectedGaussianMultiplier, projectedGaussianTimeCutoff,
      projectedCylinderTimeCutoff_eq_zero_off (by positivity : 0 < ρ ^ 2 / 4)
        (by positivity : 0 < δ / 2) ht, mul_zero])

/-- Both compact factors give genuine compact spacetime support. -/
theorem projectedGaussianMultiplier_hasCompactSupport {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) :
    HasCompactSupport (projectedGaussianMultiplier ρ δ hρ) := by
  have hc : IsCompact (tsupport (mollifiedBallCutoff 0 hρ) ×ˢ
      Icc (-ρ ^ 2 / 2) (-δ / 2)) :=
    (mollifiedBallCutoff_hasCompactSupport 0 hρ).isCompact.prod isCompact_Icc
  exact hc.of_isClosed_subset (isClosed_tsupport _) (projectedGaussianMultiplier_tsupport hρ hδ)

/-- The cutoff support is genuinely inside the projection ball and original interval. -/
theorem projectedGaussianMultiplier_support_original {ρ δ : ℝ}
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ) :
    tsupport (projectedGaussianMultiplier ρ δ hρ) ⊆
      fullBallCompactInterior ρ ×ˢ Ioo (-1) 0 := by
  intro z hz
  have h := projectedGaussianMultiplier_tsupport hρ hδ hz
  have hx := mollifiedBallCutoff_tsupport_subset_outer 0 hρ h.1
  rw [euclideanBall_eq_vec3Ball (by positivity : 0 < 3 * ρ / 4)] at hx
  have hxρ : z.1 ∈ vec3Ball 0 ρ := by
    exact (mem_vec3Ball.mp hx).trans (by linarith)
  refine ⟨subset_closure hxρ, ?_, ?_⟩
  · have hsq : ρ ^ 2 < 1 / 4 := by nlinarith
    linarith only [h.2.1, hsq]
  · linarith only [h.2.2, hδ]

/-- CKN's genuine Gaussian admissibility theorem applies on the original interval. -/
theorem projectedGaussianTest_admissible {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ) :
    projectedGaussianTest r ρ δ hρ ∈
        spaceTimeTestFunction (V := ℝ) (vec3Ball 0 1) (Ioo (-1) 0) ∧
      (∀ z, 0 ≤ projectedGaussianTest r ρ δ hρ z) ∧
      tsupport (projectedGaussianTest r ρ δ hρ) ⊆
        fullBallCompactInterior ρ ×ˢ Ioo (-1) 0 := by
  have hs := projectedGaussianMultiplier_support_original hρ hρhalf hδ
  have htime : tsupport (projectedGaussianMultiplier ρ δ hρ) ⊆
      {z : Vec3 × ℝ | z.2 < 0 + r ^ 2} := by
    intro z hz
    have h := (hs hz).2.2
    change z.2 < 0 + r ^ 2
    nlinarith only [h, sq_pos_of_pos hr]
  have htest := backwardHeat_cutoff_testFunction
    (projectedGaussianMultiplier ρ δ hρ) 0 0 r hr
    (projectedGaussianMultiplier_smooth hρ)
    (projectedGaussianMultiplier_hasCompactSupport hρ hδ)
    (hs.trans (Set.prod_mono (fullBallCompactInterior_subset_unit hρ (by linarith))
      Subset.rfl)) htime (fun z ↦ (projectedGaussianMultiplier_bounds hρ z).1)
  refine ⟨htest.1, htest.2, ?_⟩
  exact tsupport_mul_subset_left.trans hs

/-- Before zero the actual truncated test is the literal Gaussian product. -/
theorem projectedGaussianTest_eq_product {r ρ δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    {z : ParabolicPoint} (ht : z.2 ≤ 0) :
    projectedGaussianTest r ρ δ hρ z =
      projectedGaussianMultiplier ρ δ hρ z * centeredBackwardHeatTest 0 0 r z := by
  have hp : z.2 - 0 < r ^ 2 := by nlinarith only [ht, sq_pos_of_pos hr]
  simp only [projectedGaussianTest, backwardHeat_cutoff, hp, ↓reduceIte,
    centeredBackwardHeatTest]

/-- The actual multiplier equals one on the terminally truncated inner cylinder. -/
theorem projectedGaussianMultiplier_eq_one_inner {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r < ρ / 4) (hδ : 0 < δ)
    {z : ParabolicPoint} (hz : z ∈ parabolicCylinder 0 0 r) (ht : z.2 ≤ -δ) :
    projectedGaussianMultiplier ρ δ hρ z = 1 := by
  have h := mem_parabolicCylinder.mp hz
  have hx : z.1 ∈ euclideanBall 0 (13 * ρ / 20) := by
    rw [euclideanBall_eq_vec3Ball (by positivity : 0 < 13 * ρ / 20)]
    exact h.1.trans (by linarith)
  have hs : -ρ ^ 2 / 2 + ρ ^ 2 / 4 ≤ z.2 := by
    have hsq : r ^ 2 < (ρ / 4) ^ 2 := (sq_lt_sq₀ hr.le (by positivity)).mpr hscale
    nlinarith only [h.2.1, hsq, sq_pos_of_pos hρ]
  have he : z.2 ≤ -δ / 2 - δ / 2 := by linarith only [ht]
  simp only [projectedGaussianMultiplier, projectedGaussianTimeCutoff,
    mollifiedBallCutoff_eq_one_on_inner 0 hρ hx,
    projectedCylinderTimeCutoff_eq_one (by positivity : 0 < ρ ^ 2 / 4)
      (by positivity : 0 < δ / 2) hs he, one_mul]

/-- The genuine Gaussian lower bound survives terminal truncation. -/
theorem projectedGaussianTest_lower_inner {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r < ρ / 4) (hδ : 0 < δ)
    {z : ParabolicPoint} (hz : z ∈ parabolicCylinder 0 0 r) (ht : z.2 ≤ -δ) :
    1 / (2000 * r) ≤ projectedGaussianTest r ρ δ hρ z := by
  rw [projectedGaussianTest_eq_product hr hρ (by linarith only [ht, hδ]),
    projectedGaussianMultiplier_eq_one_inner hr hρ hscale hδ hz ht, one_mul]
  exact centeredBackwardHeatTest_lower_on_cylinder hr hz

/-- The final time ramp contributes a nonpositive derivative after the lower plateau. -/
theorem projectedGaussianTimeCutoff_deriv_nonpos_inner {ρ δ t : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (ht : -ρ ^ 2 / 4 < t) :
    deriv (projectedGaussianTimeCutoff ρ δ) t ≤ 0 := by
  have hev : projectedGaussianTimeCutoff ρ δ =ᶠ[𝓝 t]
      backwardTimeCutoff (-δ / 2) (δ / 2) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    change -ρ ^ 2 / 4 < s at hs
    have hs' : -ρ ^ 2 / 2 + ρ ^ 2 / 4 ≤ s := by linarith only [hs]
    simp only [projectedGaussianTimeCutoff, projectedCylinderTimeCutoff,
      backwardTimeCutoff_eq_zero_of_ge (by positivity : 0 < ρ ^ 2 / 4) hs',
      sub_zero, one_mul]
  rw [hev.deriv_eq]
  exact backwardTimeCutoff_deriv_nonpos (by positivity : 0 < δ / 2)

/-- The genuine signed time derivative bound does not depend on the future cap. -/
theorem projectedGaussianTimeCutoff_deriv_le {ρ δ t : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) :
    deriv (projectedGaussianTimeCutoff ρ δ) t ≤ 64 / ρ ^ 2 := by
  have h := projectedCylinderTimeCutoff_deriv_le
    (a := -ρ ^ 2 / 2) (b := -δ / 2) (s := t)
    (by positivity : 0 < ρ ^ 2 / 4) (by positivity : 0 < δ / 2)
  change deriv (projectedCylinderTimeCutoff (-ρ ^ 2 / 2) (-δ / 2)
    (ρ ^ 2 / 4) (δ / 2)) t ≤ 64 / ρ ^ 2
  exact h.trans_eq (by field_simp [hρ.ne']; ring)

/-- The genuine multiplier's first spatial derivative keeps the literal time factor. -/
theorem projectedGaussianMultiplier_spatialPartial {ρ δ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) (i : Fin 3) :
    spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z =
      classicalGradient (mollifiedBallCutoff 0 hρ) z.1 i *
        projectedGaussianTimeCutoff ρ δ z.2 := by
  exact spatialPartial_mul_time ((mollifiedBallCutoff_smooth 0 hρ).comp contDiff_fst) i z

private theorem gaussian_spatialSecondPartial_spatial {g : Vec3 → ℝ}
    (hg : ContDiff ℝ ∞ g) (z : ParabolicPoint) (i j : Fin 3) :
    spatialSecondPartial (fun w : ParabolicPoint ↦ g w.1) i j z =
      (fderiv ℝ (classicalGradient g) z.1 (basisVec j)) i := by
  unfold spatialSecondPartial
  change (fderiv ℝ (fun x : Vec3 ↦ classicalGradient g x i) z.1) (basisVec j) = _
  have hgrad : ContDiff ℝ ∞ (classicalGradient g) := by
    unfold classicalGradient
    refine contDiff_pi.2 ?_
    intro k
    have hfg := hg.contDiff_fderiv_apply (m := ∞) (n := ∞) (by simp)
    convert hfg.comp (contDiff_id.prodMk (contDiff_const (c := basisVec k))) using 1
    funext x
    rfl
  rw [fderiv_apply (hgrad.differentiable (by simp) z.1) i]
  rfl

/-- The genuine multiplier's second spatial derivative keeps the literal time factor. -/
theorem projectedGaussianMultiplier_spatialSecondPartial {ρ δ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) (i j : Fin 3) :
    spatialSecondPartial (projectedGaussianMultiplier ρ δ hρ) i j z =
      (fderiv ℝ (classicalGradient (mollifiedBallCutoff 0 hρ)) z.1 (basisVec j)) i *
        projectedGaussianTimeCutoff ρ δ z.2 := by
  have hf := spatialSecondPartial_mul_time
    (ψ := fun w : Vec3 × ℝ ↦ mollifiedBallCutoff 0 hρ w.1)
    (χ := projectedGaussianTimeCutoff ρ δ)
    ((mollifiedBallCutoff_smooth 0 hρ).comp contDiff_fst) i j (z.1, z.2)
  have hc := gaussian_spatialSecondPartial_spatial (mollifiedBallCutoff_smooth 0 hρ) z i j
  exact hf.trans (congrArg (fun a : ℝ ↦ a * projectedGaussianTimeCutoff ρ δ z.2) hc)

/-- The genuine multiplier's time derivative keeps the actual nonnegative spatial cutoff. -/
theorem projectedGaussianMultiplier_timePartial {ρ δ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) :
    timePartial (projectedGaussianMultiplier ρ δ hρ) z =
      mollifiedBallCutoff 0 hρ z.1 * deriv (projectedGaussianTimeCutoff ρ δ) z.2 := by
  exact (((projectedCylinderTimeCutoff_smooth _ _ _ _).differentiable
    (by simp) z.2).hasDerivAt.const_mul (mollifiedBallCutoff 0 hρ z.1)).deriv

/-- The actual spatial cutoff derivative is bounded uniformly in the terminal cap. -/
theorem projectedGaussianMultiplier_spatialPartial_bound {ρ δ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) (i : Fin 3) :
    |spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z| ≤
      cutoffGradientConstant / ρ := by
  have ht : 0 ≤ projectedGaussianTimeCutoff ρ δ z.2 :=
    projectedCylinderTimeCutoff_nonneg _ _ _ _ _
  rw [projectedGaussianMultiplier_spatialPartial, abs_mul, abs_of_nonneg ht]
  have hg := (abs_apply_le_vecEuclideanNorm
    (classicalGradient (mollifiedBallCutoff 0 hρ) z.1) i).trans
    (caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ z.1)
  calc
    _ ≤ |classicalGradient (mollifiedBallCutoff 0 hρ) z.1 i| * 1 :=
      mul_le_mul_of_nonneg_left (projectedCylinderTimeCutoff_le_one _ _ _ _ _) (abs_nonneg _)
    _ ≤ cutoffGradientConstant / ρ := by simpa using hg

/-- The actual spatial Hessian bound is uniform in the terminal cap. -/
theorem projectedGaussianMultiplier_spatialSecondPartial_bound {ρ δ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) (i j : Fin 3) :
    |spatialSecondPartial (projectedGaussianMultiplier ρ δ hρ) i j z| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  have ht : 0 ≤ projectedGaussianTimeCutoff ρ δ z.2 :=
    projectedCylinderTimeCutoff_nonneg _ _ _ _ _
  rw [projectedGaussianMultiplier_spatialSecondPartial, abs_mul, abs_of_nonneg ht]
  calc
    _ ≤ |(fderiv ℝ (classicalGradient (mollifiedBallCutoff 0 hρ)) z.1
        (basisVec j)) i| * 1 :=
      mul_le_mul_of_nonneg_left (projectedCylinderTimeCutoff_le_one _ _ _ _ _) (abs_nonneg _)
    _ ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
      simpa using caccioppoli_spatial_cutoff_second_derivative_bound 0 ρ hρ z.1 i j

/-- The actual signed multiplier heat derivative is bounded independently of the future cap. -/
theorem projectedGaussianMultiplier_heat_upper {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (z : ParabolicPoint) :
    timePartial (projectedGaussianMultiplier ρ δ hρ) z +
      ∑ i, spatialSecondPartial (projectedGaussianMultiplier ρ δ hρ) i i z ≤
        (64 + 3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
  have ht : timePartial (projectedGaussianMultiplier ρ δ hρ) z ≤ 64 / ρ ^ 2 := by
    rw [projectedGaussianMultiplier_timePartial]
    calc
      _ ≤ mollifiedBallCutoff 0 hρ z.1 * (64 / ρ ^ 2) :=
        mul_le_mul_of_nonneg_left (projectedGaussianTimeCutoff_deriv_le hρ hδ)
          (mollifiedBallCutoff_nonneg 0 hρ z.1)
      _ ≤ 1 * (64 / ρ ^ 2) :=
        mul_le_mul_of_nonneg_right (mollifiedBallCutoff_le_one 0 hρ z.1) (by positivity)
      _ = 64 / ρ ^ 2 := one_mul _
  have hl : (∑ i, spatialSecondPartial (projectedGaussianMultiplier ρ δ hρ) i i z) ≤
      3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
    calc
      _ ≤ ∑ i : Fin 3, |spatialSecondPartial (projectedGaussianMultiplier ρ δ hρ) i i z| :=
        Finset.sum_le_sum fun _ _ ↦ le_abs_self _
      _ ≤ ∑ _i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦
          projectedGaussianMultiplier_spatialSecondPartial_bound hρ z i i
      _ = 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by simp
  exact (add_le_add ht hl).trans_eq (by ring)

/-- The absolute Gaussian gradient constant retains the true ball-cutoff constant. -/
def projectedGaussianGradientConstant : ℝ := 1000 * cutoffGradientConstant + 300000

/-- The genuine test's individual spatial derivatives have the required inverse-square bound. -/
theorem projectedGaussianTest_spatialPartial_bound {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ)
    {z : ParabolicPoint} (ht : z.2 ≤ 0) (i : Fin 3) :
    |spatialPartial (projectedGaussianTest r ρ δ hρ) i z| ≤
      projectedGaussianGradientConstant / r ^ 2 := by
  have hCG : 0 ≤ cutoffGradientConstant := cutoffGradientConstant_nonneg_global
  have hzt : z.2 - 0 < r ^ 2 := by nlinarith only [ht, sq_pos_of_pos hr]
  have hformula := caccioppoli_cutoff_heat_spatialPartial
    (η := projectedGaussianMultiplier ρ δ hρ) (x₀ := 0) (t₀ := 0)
    (r := r) (z := z) (projectedGaussianMultiplier_smooth hρ) hzt i
  have hformula' : spatialPartial (projectedGaussianTest r ρ δ hρ) i z =
      spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z *
        centeredBackwardHeatTest 0 0 r z +
      projectedGaussianMultiplier ρ δ hρ z *
        spatialPartial (centeredBackwardHeatTest 0 0 r) i z := by
    simpa only [projectedGaussianTest, centeredBackwardHeatTest,
      centeredBackwardHeatTest_spatialPartial_eq] using hformula
  have hG0 : 0 ≤ centeredBackwardHeatTest 0 0 r z :=
    (centeredBackwardHeatTest_pos hr (by nlinarith only [ht, sq_pos_of_pos hr])).le
  have hGi : |spatialPartial (centeredBackwardHeatTest 0 0 r) i z| ≤ 300000 / r ^ 2 := by
    have hcoord := Finset.single_le_sum
      (fun (j : Fin 3) (_ : j ∈ Finset.univ) ↦
        abs_nonneg (spatialPartial (centeredBackwardHeatTest 0 0 r) j z))
      (Finset.mem_univ i)
    rw [← centeredBackwardHeatTestGradientNorm_eq_sum_abs_spatialPartial] at hcoord
    exact hcoord.trans (centeredBackwardHeatTestGradientNorm_le_of_le hr ht)
  have hηi : |spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z| ≤
      cutoffGradientConstant / r :=
    (projectedGaussianMultiplier_spatialPartial_bound hρ z i).trans
      (div_le_div_of_nonneg_left hCG hr hscale)
  have hη := projectedGaussianMultiplier_bounds (δ := δ) hρ z
  rw [hformula']
  calc
    _ ≤ |spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z *
          centeredBackwardHeatTest 0 0 r z| +
        |projectedGaussianMultiplier ρ δ hρ z *
          spatialPartial (centeredBackwardHeatTest 0 0 r) i z| := abs_add_le _ _
    _ = |spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z| *
          centeredBackwardHeatTest 0 0 r z + projectedGaussianMultiplier ρ δ hρ z *
          |spatialPartial (centeredBackwardHeatTest 0 0 r) i z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hG0, abs_of_nonneg hη.1]
    _ ≤ (cutoffGradientConstant / r) * (1000 / r) + 1 * (300000 / r ^ 2) :=
      add_le_add (mul_le_mul hηi (centeredBackwardHeatTest_le_of_le hr ht)
        hG0 (by positivity)) (mul_le_mul hη.2 hGi (abs_nonneg _) (by norm_num))
    _ = projectedGaussianGradientConstant / r ^ 2 := by
      unfold projectedGaussianGradientConstant
      field_simp [hr.ne']

/-- The actual Euclidean spatial gradient satisfies the required inverse-square bound. -/
theorem projectedGaussianTest_gradient_bound {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ)
    {z : ParabolicPoint} (ht : z.2 ≤ 0) :
    vec3EuclideanNorm (fun i ↦ spatialPartial (projectedGaussianTest r ρ δ hρ) i z) ≤
      3 * projectedGaussianGradientConstant / r ^ 2 := by
  calc
    _ ≤ ∑ i : Fin 3, |spatialPartial (projectedGaussianTest r ρ δ hρ) i z| :=
      vec3EuclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin 3, projectedGaussianGradientConstant / r ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ projectedGaussianTest_spatialPartial_bound hr hρ hscale ht i
    _ = 3 * projectedGaussianGradientConstant / r ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- CKN's exact backward heat product rule applies to the actual compact test. -/
theorem projectedGaussianTest_heat_identity {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) {z : ParabolicPoint} (ht : z.2 ≤ 0) :
    timePartial (projectedGaussianTest r ρ δ hρ) z +
      ∑ i, spatialSecondPartial (projectedGaussianTest r ρ δ hρ) i i z =
    (timePartial (projectedGaussianMultiplier ρ δ hρ) z +
      ∑ i, spatialSecondPartial (projectedGaussianMultiplier ρ δ hρ) i i z) *
        centeredBackwardHeatTest 0 0 r z +
      2 * ∑ i, spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z *
        spatialPartial (centeredBackwardHeatTest 0 0 r) i z := by
  have hzt : z.2 - 0 < r ^ 2 := by nlinarith only [ht, sq_pos_of_pos hr]
  simp only [centeredBackwardHeatTest_spatialPartial_eq]
  exact caccioppoli_I1_heat_operator (projectedGaussianMultiplier_smooth hρ) hzt

/-- The actual spatial derivatives vanish throughout the strict inner spatial ball. -/
theorem projectedGaussianMultiplier_spatial_derivatives_zero_inner {ρ δ : ℝ}
    (hρ : 0 < ρ) {z : ParabolicPoint} (hx : z.1 ∈ vec3Ball 0 (ρ / 2)) :
    (∀ i, spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z = 0) ∧
      (∀ i j, spatialSecondPartial (projectedGaussianMultiplier ρ δ hρ) i j z = 0) := by
  have hxi : z.1 ∈ euclideanClosedBall 0 (13 * ρ / 20) := by
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).mpr
    have hn : vecEuclideanNorm (z.1 - 0) < ρ / 2 := by
      have he := euclideanBall_eq_vec3Ball (x₀ := (0 : Vec3)) (by positivity : 0 < ρ / 2)
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mp (he.symm ▸ hx)
    linarith only [hn, hρ]
  have hv := mollifiedBallCutoff_derivatives_vanish_outside_annulus 0 hρ
    (show z.1 ∉ euclideanBall 0 (3 * ρ / 4) \ euclideanClosedBall 0 (13 * ρ / 20)
      from fun h ↦ h.2 hxi)
  refine ⟨?_, ?_⟩
  · intro i
    rw [projectedGaussianMultiplier_spatialPartial, hv.1]
    simp
  · intro i j
    rw [projectedGaussianMultiplier_spatialSecondPartial, hv.2]
    simp

/-- Inside the inner cylinder, only the decreasing final time ramp remains. -/
theorem projectedGaussianTest_heat_nonpos_inner {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hδ : 0 < δ)
    {z : ParabolicPoint} (hz : z ∈ parabolicCylinder 0 0 (ρ / 2)) :
    timePartial (projectedGaussianTest r ρ δ hρ) z +
      ∑ i, spatialSecondPartial (projectedGaussianTest r ρ δ hρ) i i z ≤ 0 := by
  have h := mem_parabolicCylinder.mp hz
  have ht : -ρ ^ 2 / 4 < z.2 := by nlinarith only [h.2.1]
  have hv := projectedGaussianMultiplier_spatial_derivatives_zero_inner (δ := δ) hρ h.1
  have htime : timePartial (projectedGaussianMultiplier ρ δ hρ) z ≤ 0 := by
    rw [projectedGaussianMultiplier_timePartial]
    exact mul_nonpos_of_nonneg_of_nonpos (mollifiedBallCutoff_nonneg 0 hρ z.1)
      (projectedGaussianTimeCutoff_deriv_nonpos_inner hρ hδ ht)
  have hG0 : 0 ≤ centeredBackwardHeatTest 0 0 r z :=
    (centeredBackwardHeatTest_pos hr (by nlinarith only [h.2.2, sq_pos_of_pos hr])).le
  rw [projectedGaussianTest_heat_identity hr hρ (by simpa using h.2.2)]
  simp only [hv.1, hv.2, zero_mul, Finset.sum_const_zero, add_zero, mul_zero]
  exact mul_nonpos_of_nonpos_of_nonneg htime hG0

/-- The absolute collar constant depends only on the genuine CKN cutoff constants. -/
def projectedGaussianHeatConstant : ℝ :=
  8000000 * (64 + 3 * cutoffSecondDerivativeConstant) + 30000000 * cutoffGradientConstant

/-- The actual signed heat derivative has the correct fifth-power collar estimate. -/
theorem projectedGaussianTest_heat_upper_collar {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ / 2) (hδ : 0 < δ)
    {z : ParabolicPoint}
    (hz : z ∈ parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    timePartial (projectedGaussianTest r ρ δ hρ) z +
      ∑ i, spatialSecondPartial (projectedGaussianTest r ρ δ hρ) i i z ≤
        projectedGaussianHeatConstant * r ^ 2 / ρ ^ 5 := by
  have ht : z.2 ≤ 0 := by simpa using (mem_parabolicCylinder.mp hz.1).2.2
  have hCG : 0 ≤ cutoffGradientConstant := cutoffGradientConstant_nonneg_global
  have hCS : 0 ≤ cutoffSecondDerivativeConstant := cutoffSecondDerivativeConstant_nonneg_global
  have hG0 : 0 ≤ centeredBackwardHeatTest 0 0 r z :=
    (centeredBackwardHeatTest_pos hr (by nlinarith only [ht, sq_pos_of_pos hr])).le
  have hG := centeredBackwardHeatTest_upper_on_annulus hr hρ hscale hz
  have hgrad := centeredBackwardHeatTestGradient_upper_on_annulus hr hρ hscale hz
  have hGi (i : Fin 3) :
      |spatialPartial (centeredBackwardHeatTest 0 0 r) i z| ≤ 5000000 * r ^ 2 / ρ ^ 4 := by
    have hcoord := Finset.single_le_sum
      (fun (j : Fin 3) (_ : j ∈ Finset.univ) ↦
        abs_nonneg (spatialPartial (centeredBackwardHeatTest 0 0 r) j z))
      (Finset.mem_univ i)
    rw [← centeredBackwardHeatTestGradientNorm_eq_sum_abs_spatialPartial] at hcoord
    exact hcoord.trans hgrad
  have hcross : (∑ i, spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z *
      spatialPartial (centeredBackwardHeatTest 0 0 r) i z) ≤
      3 * ((cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4)) := by
    calc
      _ ≤ ∑ _i : Fin 3, (cutoffGradientConstant / ρ) *
          (5000000 * r ^ 2 / ρ ^ 4) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ |spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z *
              spatialPartial (centeredBackwardHeatTest 0 0 r) i z| := le_abs_self _
          _ = |spatialPartial (projectedGaussianMultiplier ρ δ hρ) i z| *
              |spatialPartial (centeredBackwardHeatTest 0 0 r) i z| := abs_mul _ _
          _ ≤ (cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4) :=
            mul_le_mul (projectedGaussianMultiplier_spatialPartial_bound hρ z i)
              (hGi i) (abs_nonneg _) (by positivity)
      _ = _ := by simp
  rw [projectedGaussianTest_heat_identity hr hρ ht]
  calc
    _ ≤ ((64 + 3 * cutoffSecondDerivativeConstant) / ρ ^ 2) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        2 * (3 * ((cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4))) :=
      add_le_add (mul_le_mul (projectedGaussianMultiplier_heat_upper hρ hδ z)
        hG hG0 (by positivity)) (mul_le_mul_of_nonneg_left hcross (by norm_num))
    _ = projectedGaussianHeatConstant * r ^ 2 / ρ ^ 5 := by
      unfold projectedGaussianHeatConstant
      field_simp [hρ.ne']
      ring

/-- The decreasing future ramp allows the same signed heat bound on the whole cylinder. -/
theorem projectedGaussianTest_heat_upper {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ / 2) (hδ : 0 < δ)
    {z : ParabolicPoint} (hz : z ∈ parabolicCylinder 0 0 ρ) :
    timePartial (projectedGaussianTest r ρ δ hρ) z +
      ∑ i, spatialSecondPartial (projectedGaussianTest r ρ δ hρ) i i z ≤
        projectedGaussianHeatConstant * r ^ 2 / ρ ^ 5 := by
  by_cases hi : z ∈ parabolicCylinder 0 0 (ρ / 2)
  · exact (projectedGaussianTest_heat_nonpos_inner hr hρ hδ hi).trans (by
      have hCG : 0 ≤ cutoffGradientConstant := cutoffGradientConstant_nonneg_global
      have hCS : 0 ≤ cutoffSecondDerivativeConstant :=
        cutoffSecondDerivativeConstant_nonneg_global
      unfold projectedGaussianHeatConstant
      positivity)
  · exact projectedGaussianTest_heat_upper_collar hr hρ hscale hδ ⟨hz, hi⟩

/-- Actual suitable data can be tested by the Gaussian on the original time interval. -/
theorem suitable_fullBall_projected_gaussian_local_energy
    {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ) :
    Integrable (fullBallProjectedLocalEnergyDensity ρ u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ))
        ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo (-1) 0))) ∧
      (∫ z, fullBallProjectedLocalEnergyDensity ρ u D p (-1) 0 c
        (projectedGaussianTest r ρ δ hρ) z
          ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo (-1) 0))) ≤ 0 := by
  obtain ⟨htest, hnonneg, hs⟩ := projectedGaussianTest_admissible hr hρ hρhalf hδ
  have htest' : projectedGaussianTest r ρ δ hρ ∈
      spaceTimeTestFunction (V := ℝ) Ω I := by
    refine ⟨htest.1, htest.2.1, htest.2.2.trans ?_⟩
    exact Set.prod_mono (subset_closure.trans hbox.2.2.1)
      (subset_closure.trans hbox.2.2.2.2.2)
  exact suitable_fullBall_projected_local_energy_localBox ρ hρ (by linarith)
    hsol hbox (by norm_num) hc htest' hnonneg hs

/-- The actual compact test has support strictly inside the outer backward cylinder. -/
theorem projectedGaussianTest_tsupport_cylinder {r ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) :
    tsupport (projectedGaussianTest r ρ δ hρ) ⊆
      vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0 := by
  intro z hz
  have hm : z ∈ tsupport (projectedGaussianMultiplier ρ δ hρ) :=
    tsupport_mul_subset_left hz
  have hs := projectedGaussianMultiplier_tsupport hρ hδ hm
  have hx := mollifiedBallCutoff_tsupport_subset_outer 0 hρ hs.1
  rw [euclideanBall_eq_vec3Ball (by positivity : 0 < 3 * ρ / 4)] at hx
  refine ⟨(mem_vec3Ball.mp hx).trans (by linarith), ?_, ?_⟩
  · nlinarith only [hs.2.1, sq_pos_of_pos hρ]
  · linarith only [hs.2.2, hδ]

/-- Actual compact support extends the signed heat estimate to every space-time point. -/
theorem projectedGaussianTest_heat_upper_global {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ / 2) (hδ : 0 < δ)
    (z : ParabolicPoint) :
    timePartial (projectedGaussianTest r ρ δ hρ) z +
      ∑ i, spatialSecondPartial (projectedGaussianTest r ρ δ hρ) i i z ≤
        projectedGaussianHeatConstant * r ^ 2 / ρ ^ 5 := by
  by_cases hz : z ∈ parabolicCylinder 0 0 ρ
  · exact projectedGaussianTest_heat_upper hr hρ hscale hδ hz
  · have hn : (z.1, z.2) ∉ tsupport (projectedGaussianTest r ρ δ hρ) := by
      intro hs
      have hc := projectedGaussianTest_tsupport_cylinder hρ hδ hs
      exact hz (mem_parabolicCylinder.mpr
        ⟨mem_vec3Ball.mp hc.1, by simpa using hc.2.1, hc.2.2.le⟩)
    have htime := timePartial_eq_zero_off_tsupport hn
    have hsecond (i : Fin 3) := spatialSecondPartial_eq_zero_off_tsupport hn i i
    have htime' : timePartial (projectedGaussianTest r ρ δ hρ) z = 0 := htime
    have hsum : (∑ i, spatialSecondPartial (projectedGaussianTest r ρ δ hρ) i i z) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ hsecond i
    have heq : timePartial (projectedGaussianTest r ρ δ hρ) z +
        (∑ i, spatialSecondPartial (projectedGaussianTest r ρ δ hρ) i i z) = 0 :=
      (congrArg₂ (fun a b : ℝ ↦ a + b) htime' hsum).trans (zero_add 0)
    have hCG : 0 ≤ cutoffGradientConstant := cutoffGradientConstant_nonneg_global
    have hCS : 0 ≤ cutoffSecondDerivativeConstant := cutoffSecondDerivativeConstant_nonneg_global
    exact heq.le.trans (by unfold projectedGaussianHeatConstant; positivity)

/-- Before zero the genuine cutoff only decreases the nonnegative Gaussian. -/
theorem projectedGaussianTest_le_gaussian {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) {z : ParabolicPoint} (ht : z.2 ≤ 0) :
    projectedGaussianTest r ρ δ hρ z ≤ centeredBackwardHeatTest 0 0 r z := by
  have hG0 : 0 ≤ centeredBackwardHeatTest 0 0 r z :=
    (centeredBackwardHeatTest_pos hr (by nlinarith only [ht, sq_pos_of_pos hr])).le
  calc
    _ = projectedGaussianMultiplier ρ δ hρ z * centeredBackwardHeatTest 0 0 r z :=
      projectedGaussianTest_eq_product hr hρ ht
    _ ≤ 1 * centeredBackwardHeatTest 0 0 r z :=
      mul_le_mul_of_nonneg_right (projectedGaussianMultiplier_bounds hρ z).2 hG0
    _ = centeredBackwardHeatTest 0 0 r z := one_mul _

/-- The actual Gaussian test has the required inverse-radius value bound. -/
theorem projectedGaussianTest_upper {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) {z : ParabolicPoint} (ht : z.2 ≤ 0) :
    projectedGaussianTest r ρ δ hρ z ≤ 1000 / r :=
  (projectedGaussianTest_le_gaussian hr hρ ht).trans (centeredBackwardHeatTest_le_of_le hr ht)

/-- The actual Gaussian test has the genuine cubic far-field decay on the collar. -/
theorem projectedGaussianTest_upper_collar {r ρ δ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ / 2) {z : ParabolicPoint}
    (hz : z ∈ parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    projectedGaussianTest r ρ δ hρ z ≤ 8000000 * r ^ 2 / ρ ^ 3 :=
  (projectedGaussianTest_le_gaussian hr hρ (by
    simpa using (mem_parabolicCylinder.mp hz.1).2.2)).trans
      (centeredBackwardHeatTest_upper_on_annulus hr hρ hscale hz)

end FluidSingularSets
