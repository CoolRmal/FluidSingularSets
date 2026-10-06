-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.EndpointInteriorRescaling
public import FluidSingularSets.CompactRegularVelocity

/-!
# Compact regularity geometry for the endpoint criterion

Genuine quarter-cylinder rescaling sends the origin to every point of the
closed inner cylinder. The resulting pointwise regularity gives an actual
common essential velocity bound after physical parabolic scaling.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine positive scaling sends every native cylinder to its physical cylinder. -/
theorem endpoint_scalingHomeomorph_image_cylinder {r : ℝ} (hr : 0 < r)
    (z₀ : ParabolicPoint) (s : ℝ) :
    parabolicScalingHomeomorph r hr z₀ '' parabolicCylinder 0 0 s =
      parabolicCylinder z₀.1 z₀.2 (r * s) := by
  change (parabolicTranslate z₀.1 z₀.2 ∘ parabolicScale r) ''
    parabolicCylinder 0 0 s = _
  rw [Set.image_comp]
  exact CKN.Foundation.Parabolic.Integration.parabolicCylinder_rescale_image
    hr z₀.1 z₀.2 s

/-- The actual parabolic topology makes every closed positive-radius cylinder compact. -/
theorem endpoint_isCompact_closure_cylinder (x : Vec3) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    IsCompact (closure (parabolicCylinder x t r)) := by
  rw [closure_parabolicCylinder hr, ← closure_vec3Ball hr]
  exact parabolicHomeomorph.isCompact_preimage.mpr
    ((isCompact_closure_vec3Ball hr).prod isCompact_Icc)

/-- Actual regularity on the closed native inner cylinder gives a physical inner bound. -/
theorem endpoint_physical_inner_bound_of_native_regular
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {r : ℝ} (hr : 0 < r) (z₀ : ParabolicPoint)
    (hreg : ∀ z ∈ closure (parabolicCylinder 0 0 (1 / 8)),
      CKN.IsRegularPoint (rescaledSpace r z₀.1 Ω) (rescaledTime r z₀.2 I)
        (rescaleVelocity r z₀ u) z) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ w ∂volume.restrict
      (parabolicCylinder z₀.1 z₀.2 ((1 / 8) * r)), vec3EuclideanNorm (u w) ≤ A := by
  let H := parabolicScalingHomeomorph r hr z₀
  have he : H '' closure (parabolicCylinder 0 0 (1 / 8)) =
      closure (parabolicCylinder z₀.1 z₀.2 ((1 / 8) * r)) := by
    rw [H.image_closure, endpoint_scalingHomeomorph_image_cylinder, mul_comm]
  have hphysical : ∀ w ∈ closure (parabolicCylinder z₀.1 z₀.2 ((1 / 8) * r)),
      CKN.IsRegularPoint Ω I u w := by
    intro w hw
    rw [← he] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact isRegularPoint_of_rescaled hr z₀ z (hreg z hz)
  obtain ⟨A, hA, hbound⟩ := compact_ae_velocity_bound_of_regular_points
    (endpoint_isCompact_closure_cylinder z₀.1 z₀.2 (by positivity)) hphysical
  exact ⟨A, hA, ae_restrict_of_ae_restrict_of_subset subset_closure hbound⟩

/-- A genuine native origin criterion yields regularity at every closed inner point. -/
theorem endpoint_inner_regular_of_origin_threshold
    {q ε : ℝ}
    (horigin : ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ),
      IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0) →
      localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) →
      velocityCylinderSixMoment u 1 ≤ ENNReal.ofReal ε → CKN.IsRegularPoint Ω I u (0, 0))
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {D : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    (hsmall : velocityCylinderSixMoment u 1 ≤ ENNReal.ofReal (ε / 4))
    {z : ParabolicPoint} (hz : z ∈ closure (parabolicCylinder 0 0 (1 / 8))) :
    CKN.IsRegularPoint Ω I u z := by
  have hs := suitable_unforced_rescale hsol z (by norm_num : (0 : ℝ) < 1 / 4)
  have hb := localBox_endpoint_interior_quarter_rescaled hbox hz
  have hx : velocityCylinderSixMoment (rescaleVelocity (1 / 4) z u) 1 ≤
      ENNReal.ofReal ε := by
    calc
      _ ≤ 4 * velocityCylinderSixMoment u 1 :=
        endpoint_interior_rescaled_six_moment_le_four u hz
      _ ≤ 4 * ENNReal.ofReal (ε / 4) := mul_le_mul' le_rfl hsmall
      _ = _ := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        ring
  have hreg := horigin _ _ _ _ _ hs hb hx
  have hh := isRegularPoint_of_rescaled (by norm_num : (0 : ℝ) < 1 / 4) z (0, 0) hreg
  simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale] using hh

end FluidSingularSets
