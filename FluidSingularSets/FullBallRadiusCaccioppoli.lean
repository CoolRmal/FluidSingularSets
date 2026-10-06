-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallCylinderCaccioppoli
public import FluidSingularSets.NestedProjectionBallRescaling
public import FluidSingularSets.FullBallGradientMomentFinite
public import FluidSingularSets.FullBallVelocityMomentFinite
public import FluidSingularSets.ProjectedRadiusIteration32

/-!
# Actual physical nested-radius endpoint energy iteration

Suitability and the projection local box are genuinely transported at every
outer radius. Exact inner-cylinder scaling then gives a physical contraction
with one common unit-cylinder source. Finite actual energy supplies the bounded
iteration hypothesis and removes the outer dissipation.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- Actual centered backward cylinders are nested for nonnegative radii. -/
theorem centered_backwardCylinder_subset {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0 ⊆ vec3Ball 0 R ×ˢ Ioo (-(R ^ 2)) 0 := by
  intro z hz
  refine ⟨vec3Ball_mono hrR hz.1, ?_, hz.2.2⟩
  nlinarith [hz.2.1]

/-- Coordinate dissipation is genuinely monotone on the actual nested cylinders. -/
theorem coordinateCylinderMass_mono (D : ParabolicPoint → Fin 3 → Vec3)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    coordinateCylinderMass D r ≤ coordinateCylinderMass D R :=
  lintegral_mono_set (centered_backwardCylinder_subset hr hrR)

/-- The genuine endpoint velocity moment is monotone on the same nested cylinders. -/
theorem velocityCylinderSixMoment_mono (u : ParabolicPoint → Vec3)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    velocityCylinderSixMoment u r ≤ velocityCylinderSixMoment u R := by
  have htime : Ioo (-(r ^ 2)) 0 ⊆ Ioo (-(R ^ 2)) 0 := by
    intro t ht
    exact ⟨by nlinarith [ht.1], ht.2⟩
  calc
    _ ≤ ∫⁻ t in Ioo (-(r ^ 2)) 0, eLpNorm (fun x ↦ u (x, t)) 6
        (volume.restrict (vec3Ball 0 R)) ^ 2 := by
      apply lintegral_mono
      intro t
      exact pow_le_pow_left₀ (by positivity) (eLpNorm_mono_measure _
        (Measure.restrict_mono_set volume (vec3Ball_mono hrR))) 2
    _ ≤ _ := lintegral_mono_set htime

/-- The literal coordinate cylinder mass has the exact inverse outer-radius scaling. -/
theorem coordinateCylinderMass_rescale {μ : ℝ} (hμ : 0 < μ)
    (D : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) :
    coordinateCylinderMass (rescaleGradient μ (0, 0) D) (r / μ) =
      ENNReal.ofReal μ⁻¹ * coordinateCylinderMass D r := by
  have h := rescaleGradient_coordinate_energy_innerBall hμ (0, 0) D r (-(r ^ 2)) 0
  simpa only [coordinateCylinderMass, sub_zero, zero_div, neg_div, div_pow] using h

/-- The native unit mixed moment has the exact inverse physical projection radius. -/
theorem velocityCylinderSixMoment_rescale_unit {μ : ℝ} (hμ : 0 < μ)
    (u : ParabolicPoint → Vec3) :
    velocityCylinderSixMoment (rescaleVelocity μ (0, 0) u) 1 =
      ENNReal.ofReal μ⁻¹ * velocityCylinderSixMoment u μ := by
  have h := rescaleVelocity_mixed_two_six_projectionBall hμ (0, 0) u (-(μ ^ 2)) 0
  simpa only [velocityCylinderSixMoment, one_pow, sub_zero, zero_div, neg_div,
    div_self (pow_ne_zero 2 hμ.ne')] using h

/-- The real coordinate masses retain the exact scaling. -/
theorem coordinateCylinderMass_rescale_toReal {μ : ℝ} (hμ : 0 < μ)
    (D : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) :
    (coordinateCylinderMass (rescaleGradient μ (0, 0) D) (r / μ)).toReal =
      μ⁻¹ * (coordinateCylinderMass D r).toReal := by
  rw [coordinateCylinderMass_rescale hμ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hμ.le)]

/-- Genuine suitable unit-box data give finite actual coordinate dissipation. -/
theorem suitable_coordinateCylinderMass_unit_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    coordinateCylinderMass D 1 < ⊤ := by
  simpa only [coordinateCylinderMass, one_pow] using
    suitable_fullBall_gradient_coordinate_moment_lt_top hsol hbox

/-- Genuine suitable unit-box data give a finite actual endpoint velocity moment. -/
theorem suitable_velocityCylinderSixMoment_unit_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    velocityCylinderSixMoment u 1 < ⊤ := by
  simpa only [velocityCylinderSixMoment, one_pow, ENNReal.rpow_ofNat] using
    suitable_fullBall_velocity_six_moment_lt_top hsol hbox

/-- The rescaled endpoint source is uniformly controlled on the actual iteration radii. -/
theorem velocityCylinderSixMoment_rescale_toReal_le_two
    (u : ParabolicPoint → Vec3) {μ : ℝ} (hμ : (3 / 4 : ℝ) ≤ μ) (hμone : μ ≤ 1)
    (hfin : velocityCylinderSixMoment u 1 < ⊤) :
    (velocityCylinderSixMoment (rescaleVelocity μ (0, 0) u) 1).toReal ≤
      2 * (velocityCylinderSixMoment u 1).toReal := by
  have hμpos : 0 < μ := by linarith
  have hmono := velocityCylinderSixMoment_mono u hμpos.le hμone
  have hreal := ENNReal.toReal_mono hfin.ne hmono
  have hinv : μ⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hμpos]
    linarith
  rw [velocityCylinderSixMoment_rescale_unit hμpos, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hμpos.le)]
  exact mul_le_mul hinv hreal ENNReal.toReal_nonneg (by norm_num)

/-- Uniform mixed-moment control preserves the true endpoint polynomial. -/
theorem endpoint_source_polynomial_le_sixteen {x X : ℝ}
    (hx : 0 ≤ x) (hX : 0 ≤ X) (hxX : x ≤ 2 * X) :
    x + x ^ 2 + x ^ 4 ≤ 16 * (X + X ^ 2 + X ^ 4) := by
  calc
    _ ≤ 2 * X + (2 * X) ^ 2 + (2 * X) ^ 4 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg X]

/-- A common finite coefficient for the true physical nested-radius forcing. -/
def physicalCylinderEndpointForcingConstant : ℝ := 16 * fullCylinderEndpointForcingConstant

theorem physicalCylinderEndpointForcingConstant_nonneg :
    0 ≤ physicalCylinderEndpointForcingConstant :=
  mul_nonneg (by norm_num) fullCylinderEndpointForcingConstant_nonneg

/-- Actual physical projection-ball rescaling gives the genuine radius contraction. -/
theorem suitable_physical_cylinder_radius_step
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {s t : ℝ} (hs : (3 / 4 : ℝ) ≤ s) (hst : s < t) (htone : t ≤ 1) :
    let X := (velocityCylinderSixMoment u 1).toReal
    (coordinateCylinderMass D s).toReal ≤ (3 / 4) * (coordinateCylinderMass D t).toReal +
      physicalCylinderEndpointForcingConstant * (X + X ^ 2 + X ^ 4) / (t - s) ^ 32 := by
  let X := (velocityCylinderSixMoment u 1).toReal
  let x := (velocityCylinderSixMoment (rescaleVelocity t (0, 0) u) 1).toReal
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := by linarith
  have hr : (3 / 4 : ℝ) ≤ s / t := by
    rw [le_div_iff₀ htpos]
    nlinarith
  have hrone : s / t < 1 := (div_lt_one htpos).mpr hst
  have hscaledsol := suitable_unforced_rescale hsol (0, 0) htpos
  have hscaledbox := localBox_rescaled_subunit_backwardCylinder hbox htpos htone
  have hest := (suitable_fullBall_cylinder_caccioppoli hscaledsol hscaledbox hr hrone).2
  have hinner := coordinateCylinderMass_rescale_toReal htpos D s
  have houter : (coordinateCylinderMass (rescaleGradient t (0, 0) D) 1).toReal =
      t⁻¹ * (coordinateCylinderMass D t).toReal := by
    simpa only [div_self htpos.ne'] using coordinateCylinderMass_rescale_toReal htpos D t
  rw [hinner, houter] at hest
  have hm := mul_le_mul_of_nonneg_left hest htpos.le
  have hmass : (coordinateCylinderMass D s).toReal ≤
      (3 / 4) * (coordinateCylinderMass D t).toReal +
        t * (fullCylinderEndpointForcingConstant / (1 - s / t) ^ 12 *
          (x + x ^ 2 + x ^ 4)) := by
    have he : t * (t⁻¹ * (coordinateCylinderMass D s).toReal) =
        (coordinateCylinderMass D s).toReal := by rw [← mul_assoc, mul_inv_cancel₀ htpos.ne',
      one_mul]
    rw [he] at hm
    convert hm using 1
    dsimp [x]
    field_simp [htpos.ne']
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  have hxX : x ≤ 2 * X := velocityCylinderSixMoment_rescale_toReal_le_two u
    (by linarith) htone (suitable_velocityCylinderSixMoment_unit_lt_top hsol hbox)
  have hpoly := endpoint_source_polynomial_le_sixteen hx hX hxX
  have ht13 : t ^ 13 ≤ 1 := pow_le_one₀ htpos.le htone
  have hgap : 0 < t - s := sub_pos.mpr hst
  have hK := fullCylinderEndpointForcingConstant_nonneg
  have hforce : t * (fullCylinderEndpointForcingConstant / (1 - s / t) ^ 12 *
        (x + x ^ 2 + x ^ 4)) ≤
      physicalCylinderEndpointForcingConstant * (X + X ^ 2 + X ^ 4) / (t - s) ^ 32 := by
    calc
      _ = (fullCylinderEndpointForcingConstant * t ^ 13 / (t - s) ^ 12) *
          (x + x ^ 2 + x ^ 4) := by
        field_simp [htpos.ne', hgap.ne', (sub_pos.mpr hrone).ne']
      _ ≤ (fullCylinderEndpointForcingConstant / (t - s) ^ 12) *
          (16 * (X + X ^ 2 + X ^ 4)) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hK ht13) (by positivity)
        · exact hpoly
        · positivity
        · positivity
      _ = physicalCylinderEndpointForcingConstant * (X + X ^ 2 + X ^ 4) /
          (t - s) ^ 12 := by unfold physicalCylinderEndpointForcingConstant; ring
      _ ≤ _ := projected_gap_power32_le hgap (by linarith)
        (mul_nonneg physicalCylinderEndpointForcingConstant_nonneg (by positivity)) (by norm_num)
  exact hmass.trans (add_le_add le_rfl hforce)

/-- Bounded genuine energy iteration removes all outer dissipation from the inner estimate. -/
theorem suitable_fullBall_endpoint_coordinate_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    let X := (velocityCylinderSixMoment u 1).toReal
    (coordinateCylinderMass D (3 / 4)).toReal ≤
      projectedUnitCaccioppoliConstant32 * physicalCylinderEndpointForcingConstant *
        (X + X ^ 2 + X ^ 4) := by
  let X := (velocityCylinderSixMoment u 1).toReal
  have hfin := suitable_coordinateCylinderMass_unit_lt_top hsol hbox
  have hbound : ∀ s ∈ Icc (3 / 4 : ℝ) 1,
      (coordinateCylinderMass D s).toReal ≤ (coordinateCylinderMass D 1).toReal := by
    intro s hs
    exact ENNReal.toReal_mono hfin.ne (coordinateCylinderMass_mono D (by linarith [hs.1]) hs.2)
  have h := bounded_projected_unit_radius_iteration32
    (E := fun s ↦ (coordinateCylinderMass D s).toReal)
    (A := physicalCylinderEndpointForcingConstant * (X + X ^ 2 + X ^ 4))
    (by exact mul_nonneg physicalCylinderEndpointForcingConstant_nonneg (by positivity))
    hbound (fun s t hs hst ht ↦ suitable_physical_cylinder_radius_step hsol hbox hs hst ht)
  simpa only [mul_assoc] using h

end FluidSingularSets
