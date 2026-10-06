-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureMixedBounds
public import FluidSingularSets.FullBallGradientMomentFinite

/-!
# Genuine native Stokes pressure classes on original suitable intervals

Full-ball weak Sobolev and suitable energy supply the actual nonlinear time
L¹ and viscous time L² spatial Hilbert curves without added moment premises.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- Genuine suitable full-ball H¹ slices belong to spatial L⁶ on a common full time set. -/
theorem suitable_fullBall_velocity_memLp_six_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) := by
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)] with t ht hwt
  exact fullUnitBallH1Vector_memLp_six ht.1 ht.2 hwt

/-- The actual native nonlinear pressure curve is time L¹ directly from suitability. -/
theorem suitable_fullBall_native_convective_pressure_memLp_one
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    MemLp (unitBallConvectivePressureCurve u) 1 (volume.restrict (Ioo a b)) := by
  have hu : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_velocity hbox
  exact unitBallConvectivePressureCurve_memLp_one_of_six_moment hu
    (suitable_fullBall_velocity_memLp_six_ae hsol hbox)
    (by simpa only [ENNReal.rpow_ofNat] using
      suitable_fullBall_velocity_six_moment_lt_top hsol hbox)

/-- The actual native viscous pressure curve is time L² directly from suitability. -/
theorem suitable_fullBall_native_viscous_pressure_memLp_two
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    MemLp (unitBallViscousPressureCurve D) 2 (volume.restrict (Ioo a b)) := by
  have hD : AEStronglyMeasurable D
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_gradient hbox
  apply unitBallViscousPressureCurve_memLp_two_of_gradient_moment hD
    ((slice_memLp_ae_of_sws hsol hbox).mono fun _ ht ↦ ht.2)
  rw [lintegral_spatial_two_sq_eq (hsol.toData.aestronglyMeasurable_gradient hbox)]
  exact suitable_fullBall_gradient_norm_moment_lt_top hsol hbox

end Suitable

end FluidSingularSets
