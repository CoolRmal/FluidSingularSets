-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicOperators
public import FluidSingularSets.ProjectedCylinderCutoff
public import FluidSingularSets.CanonicalBallCutoffSecondBounds

/-!
# Genuine canonical unit-cylinder cutoff data

The actual midpoint spatial cutoff and two-sided smooth time ramp are supported
inside the original unit box. Their upper time derivative bound does not depend
on the arbitrary terminal truncation, and their test equals one on the literal
truncated inner cylinder.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual outer radius of the spatial cutoff. -/
def fullBallCanonicalOuterRadius (r : ℝ) : ℝ := (r + 1) / 2

/-- The strictly larger compact pressure radius. -/
def fullBallCanonicalPressureRadius (r : ℝ) : ℝ := (r + 3) / 4

/-- The genuine spatial cutoff from the pinned CKN construction. -/
def fullBallCanonicalSpatialCutoff (r : ℝ) : Vec3 → ℝ :=
  canonicalBallCutoff 0 r (fullBallCanonicalOuterRadius r)

/-- The actual time cutoff with an arbitrary strictly positive terminal truncation. -/
def fullBallCanonicalTimeCutoff (r δ : ℝ) : ℝ → ℝ :=
  projectedCylinderTimeCutoff (-(fullBallCanonicalOuterRadius r) ^ 2) (-δ / 2)
    ((fullBallCanonicalOuterRadius r) ^ 2 - r ^ 2) (δ / 2)

/-- The genuine sixth-power spatial and time product test. -/
def fullBallCanonicalTest (r δ : ℝ) : Vec3 × ℝ → ℝ :=
  projectedCylinderTest (fullBallCanonicalSpatialCutoff r)
    (-(fullBallCanonicalOuterRadius r) ^ 2) (-δ / 2)
    ((fullBallCanonicalOuterRadius r) ^ 2 - r ^ 2) (δ / 2)

/-- All actual collar radii and the lower ramp width are strictly positive. -/
theorem fullBallCanonical_radii {r : ℝ} (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) :
    0 < r ∧ r < fullBallCanonicalOuterRadius r ∧
      0 < fullBallCanonicalOuterRadius r ∧
      fullBallCanonicalOuterRadius r < fullBallCanonicalPressureRadius r ∧
      0 < fullBallCanonicalPressureRadius r ∧ fullBallCanonicalPressureRadius r < 1 ∧
      0 < (fullBallCanonicalOuterRadius r) ^ 2 - r ^ 2 := by
  dsimp only [fullBallCanonicalOuterRadius, fullBallCanonicalPressureRadius]
  refine ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, ?_⟩
  nlinarith

/-- The true spatial and pressure collar widths are exact fixed fractions. -/
theorem fullBallCanonical_gap_eq (r : ℝ) :
    fullBallCanonicalOuterRadius r - r = (1 - r) / 2 ∧
      1 - fullBallCanonicalPressureRadius r = (1 - r) / 4 := by
  dsimp only [fullBallCanonicalOuterRadius, fullBallCanonicalPressureRadius]
  constructor <;> ring

/-- The cutoff's actual spatial regularity, unit bounds and strict outer support. -/
theorem fullBallCanonical_spatial_data {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) :
    ContDiff ℝ ∞ (fullBallCanonicalSpatialCutoff r) ∧
      HasCompactSupport (fullBallCanonicalSpatialCutoff r) ∧
      (∀ x, 0 ≤ fullBallCanonicalSpatialCutoff r x ∧
        fullBallCanonicalSpatialCutoff r x ≤ 1) ∧
      tsupport (fullBallCanonicalSpatialCutoff r) ⊆
        vec3Ball 0 (fullBallCanonicalOuterRadius r) := by
  obtain ⟨hr0, hrR, hR0, _⟩ := fullBallCanonical_radii hr hrone
  refine ⟨canonicalBallCutoff_smooth 0 hr0.le hrR,
    canonicalBallCutoff_hasCompactSupport hr0.le hrR,
    fun x ↦ ⟨canonicalBallCutoff_nonneg 0 r _ x, canonicalBallCutoff_le_one 0 r _ x⟩, ?_⟩
  have hs := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec3)) hr0.le hrR
  rwa [euclideanBall_eq_vec3Ball hR0] at hs

/-- The genuine support fits strictly inside the pressure patch. -/
theorem fullBallCanonical_spatial_support {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) :
    tsupport (fullBallCanonicalSpatialCutoff r) ⊆
      vec3Ball 0 (fullBallCanonicalPressureRadius r) :=
  (fullBallCanonical_spatial_data hr hrone).2.2.2.trans
    (vec3Ball_mono (fullBallCanonical_radii hr hrone).2.2.2.1.le)

/-- The containing actual spatial patch lies in its own compact interior. -/
theorem fullBallCanonical_ball_subset_compact (r : ℝ) :
    vec3Ball (0 : Vec3) (fullBallCanonicalPressureRadius r) ⊆
      fullBallCompactInterior (fullBallCanonicalPressureRadius r) := subset_closure

/-- The actual support is contained in the Euclidean unit ball required by cutoff Sobolev. -/
theorem fullBallCanonical_spatial_support_unit {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) :
    tsupport (fullBallCanonicalSpatialCutoff r) ⊆ euclideanBall 0 1 := by
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)]
  exact (fullBallCanonical_spatial_support hr hrone).trans
    (vec3Ball_mono (fullBallCanonical_radii hr hrone).2.2.2.2.2.1.le)

/-- The true spatial cutoff is exactly one on the inner ball. -/
theorem fullBallCanonical_spatial_eq_one {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) {x : Vec3}
    (hx : x ∈ vec3Ball 0 r) : fullBallCanonicalSpatialCutoff r x = 1 := by
  obtain ⟨hr0, hrR, _⟩ := fullBallCanonical_radii hr hrone
  apply canonicalBallCutoff_eq_one_on_inner hr0.le hrR
  rwa [euclideanBall_eq_vec3Ball hr0]

/-- The actual spatial gradient has a fixed inverse collar bound. -/
theorem fullBallCanonical_gradient_bound {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (x : Vec3) :
    ‖classicalGradient (fullBallCanonicalSpatialCutoff r) x‖ ≤ 64 / (1 - r) := by
  obtain ⟨hr0, hrR, _⟩ := fullBallCanonical_radii hr hrone
  apply (pi_norm_le_vecEuclideanNorm _).trans
  apply (canonicalBallCutoff_gradient_bound hr0.le hrR x).trans_eq
  rw [(fullBallCanonical_gap_eq r).1, div_div_eq_mul_div]
  norm_num

/-- The actual gradient collar constant is at least one. -/
theorem fullBallCanonical_gradient_constant_ge_one {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) : 1 ≤ 64 / (1 - r) := by
  apply (le_div_iff₀ (sub_pos.mpr hrone)).mpr
  linarith

/-- The pressure radius is literally the midpoint of the outer radius and one. -/
theorem fullBallCanonical_pressureRadius_eq_midpoint (r : ℝ) :
    fullBallCanonicalPressureRadius r = (fullBallCanonicalOuterRadius r + 1) / 2 := by
  dsimp only [fullBallCanonicalPressureRadius, fullBallCanonicalOuterRadius]
  ring

/-- The actual lower time collar gives a terminal-margin-independent reciprocal bound. -/
theorem fullBallCanonical_time_width_bound {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) :
    16 / ((fullBallCanonicalOuterRadius r) ^ 2 - r ^ 2) ≤ 32 / (1 - r) := by
  have hgap : 0 < 1 - r := sub_pos.mpr hrone
  have hwidth : (1 - r) / 2 ≤ (fullBallCanonicalOuterRadius r) ^ 2 - r ^ 2 := by
    dsimp only [fullBallCanonicalOuterRadius]
    nlinarith [mul_nonneg hgap.le (show 0 ≤ 3 * r - 1 by linarith)]
  calc
    _ ≤ 16 / ((1 - r) / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hwidth
    _ = _ := by rw [div_div_eq_mul_div]; norm_num

/-- The actual time support is strictly interior to the original unit time interval. -/
theorem fullBallCanonical_closed_time_subset {r δ : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    Icc (-(fullBallCanonicalOuterRadius r) ^ 2) (-δ / 2) ⊆ Ioo (-1 : ℝ) 0 := by
  obtain ⟨_hr0, _hrR, hR0, hRρ, _hρ0, hρone, _⟩ := fullBallCanonical_radii hr hrone
  have hRone : fullBallCanonicalOuterRadius r < 1 := hRρ.trans hρone
  intro t ht
  constructor
  · nlinarith [ht.1, mul_pos hR0 (sub_pos.mpr hRone)]
  · linarith [ht.2]

/-- All actual time-cutoff regularity, support, and pointwise bounds. -/
theorem fullBallCanonical_time_data {r δ : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fullBallCanonicalTimeCutoff r δ) ∧
      HasCompactSupport (fullBallCanonicalTimeCutoff r δ) ∧
      (∀ t, 0 ≤ fullBallCanonicalTimeCutoff r δ t ∧
        fullBallCanonicalTimeCutoff r δ t ≤ 1) ∧
      tsupport (fullBallCanonicalTimeCutoff r δ) ⊆ Ioo (-1 : ℝ) 0 ∧
      (∀ t, deriv (fullBallCanonicalTimeCutoff r δ) t ≤
        16 / ((fullBallCanonicalOuterRadius r) ^ 2 - r ^ 2)) ∧
      ∀ t, deriv (fullBallCanonicalTimeCutoff r δ) t ≤ 32 / (1 - r) := by
  have hw := (fullBallCanonical_radii hr hrone).2.2.2.2.2.2
  have hd : 0 < δ / 2 := by linarith
  refine ⟨projectedCylinderTimeCutoff_smooth _ _ _ _,
    projectedCylinderTimeCutoff_hasCompactSupport hw hd,
    fun t ↦ ⟨projectedCylinderTimeCutoff_nonneg _ _ _ _ t,
      projectedCylinderTimeCutoff_le_one _ _ _ _ t⟩,
    (projectedCylinderTimeCutoff_tsupport hw hd).trans
      (fullBallCanonical_closed_time_subset hr hrone hδ),
    fun _ ↦ projectedCylinderTimeCutoff_deriv_le hw hd,
    fun _ ↦ (projectedCylinderTimeCutoff_deriv_le hw hd).trans
      (fullBallCanonical_time_width_bound hr hrone)⟩

/-- The actual product test is nonnegative everywhere. -/
theorem fullBallCanonical_test_nonneg (r δ : ℝ) (z : Vec3 × ℝ) :
    0 ≤ fullBallCanonicalTest r δ z := projectedCylinderTest_nonneg _ _ _ _ _ z

/-- The actual unit-cylinder test support lies in the genuine open pressure patch. -/
theorem fullBallCanonical_test_support {r δ : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    tsupport (fullBallCanonicalTest r δ) ⊆
      vec3Ball 0 (fullBallCanonicalPressureRadius r) ×ˢ Ioo (-1 : ℝ) 0 :=
  (projectedCylinderTest_tsupport (fullBallCanonical_radii hr hrone).2.2.2.2.2.2
    (by linarith : 0 < δ / 2)).trans
      (prod_mono (fullBallCanonical_spatial_support hr hrone)
        (fullBallCanonical_closed_time_subset hr hrone hδ))

/-- The genuine test support satisfies the exact compact subtype energy hypothesis. -/
theorem fullBallCanonical_test_support_compact {r δ : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    tsupport (fullBallCanonicalTest r δ) ⊆
      fullBallCompactInterior (fullBallCanonicalPressureRadius r) ×ˢ Ioo (-1 : ℝ) 0 :=
  (fullBallCanonical_test_support hr hrone hδ).trans
    (prod_mono (fullBallCanonical_ball_subset_compact r) Subset.rfl)

/-- Every genuine local unit box admits this literal smooth compact test. -/
theorem fullBallCanonical_test_admissible {Ω : Set Vec3} {I : Set ℝ} {r δ : ℝ}
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    fullBallCanonicalTest r δ ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  obtain ⟨hφ, hφc, _hb, _hs⟩ := fullBallCanonical_spatial_data hr hrone
  have hsΩ : tsupport (fullBallCanonicalSpatialCutoff r) ⊆ Ω :=
    ((fullBallCanonical_spatial_support hr hrone).trans
      (vec3Ball_mono (fullBallCanonical_radii hr hrone).2.2.2.2.2.1.le)).trans
        (subset_closure.trans hbox.2.2.1)
  have htI : Icc (-(fullBallCanonicalOuterRadius r) ^ 2) (-δ / 2) ⊆ I :=
    (fullBallCanonical_closed_time_subset hr hrone hδ).trans
      (subset_closure.trans hbox.2.2.2.2.2)
  exact projectedCylinderTest_mem_spaceTimeTestFunction hφ hφc hsΩ htI
    (fullBallCanonical_radii hr hrone).2.2.2.2.2.2 (by linarith)

/-- The true unit test equals one on the actual truncated inner cylinder. -/
theorem fullBallCanonical_test_eq_one {r δ : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ)
    {z : Vec3 × ℝ} (hz : z ∈ vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ)) :
    fullBallCanonicalTest r δ z = 1 := by
  have hw := (fullBallCanonical_radii hr hrone).2.2.2.2.2.2
  have hs : -(fullBallCanonicalOuterRadius r) ^ 2 +
      ((fullBallCanonicalOuterRadius r) ^ 2 - r ^ 2) ≤ z.2 := by linarith [hz.2.1]
  have he : z.2 ≤ -δ / 2 - δ / 2 := by linarith [hz.2.2]
  simp only [fullBallCanonicalTest, projectedCylinderTest,
    fullBallCanonical_spatial_eq_one hr hrone hz.1,
    projectedCylinderTimeCutoff_eq_one hw (by linarith : 0 < δ / 2) hs he,
    one_pow, one_mul]

/-- The actual sixth-power diffusion cutoff has the correct fourth-power spatial weight. -/
theorem fullBallCanonical_laplacian_weighted_bound {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (x : Vec3) :
    |spatialLaplacian (fun y ↦ fullBallCanonicalSpatialCutoff r y ^ 6) x| ≤
      canonicalBallCutoffSixthLaplacianConstant * fullBallCanonicalSpatialCutoff r x ^ 4 /
        (fullBallCanonicalOuterRadius r - r) ^ 2 :=
  canonicalBallCutoff_zero_sixth_laplacian_weighted_bound hr
    (fullBallCanonical_radii hr hrone).2.1
    ((fullBallCanonical_radii hr hrone).2.2.2.1.trans
      (fullBallCanonical_radii hr hrone).2.2.2.2.2.1).le x

/-- The actual plain diffusion bound has the genuine universal inverse square collar. -/
theorem fullBallCanonical_laplacian_bound {r : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (x : Vec3) :
    |spatialLaplacian (fun y ↦ fullBallCanonicalSpatialCutoff r y ^ 6) x| ≤
      4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2 := by
  have h := canonicalBallCutoff_zero_sixth_laplacian_bound hr
    (fullBallCanonical_radii hr hrone).2.1
    ((fullBallCanonical_radii hr hrone).2.2.2.1.trans
      (fullBallCanonical_radii hr hrone).2.2.2.2.2.1).le x
  apply h.trans_eq
  rw [(fullBallCanonical_gap_eq r).1, div_pow, div_div_eq_mul_div]
  ring

end FluidSingularSets
