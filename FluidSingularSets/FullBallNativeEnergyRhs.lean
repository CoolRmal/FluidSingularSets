-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallCylinderEnergyRhs

/-!
# Genuine native-coordinate projected right hand side

The literal projected right hand side is supported on the actual test.
Its source-derived compact integrability therefore gives true native joint
integrability, and all native, compact and iterated integrals agree.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual ambient coordinate density of the genuine projected right hand side. -/
def fullBallNativeProjectedRhsDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  2 * projectedGradientSquare (fullBallProjectedVelocityDerivativeAmbient u D p a b c z) *
    ψ z - projectedEnergyDeficitPolynomial (u z)
      (fullBallProjectedHarmonicGradientAmbient u D p a b c z)
      (fun j ↦ spatialPartial ψ j z) (D z)
      (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z)
      (p z - fullBallProjectedMomentumPressure u D p z.2 z.1)
      (ψ z) (timePartial ψ z) (∑ j, spatialSecondPartial ψ j j z)

/-- The compact right hand side is literally the actual native density. -/
theorem fullBallProjectedRhsDensity_eq_native (ρ : ℝ)
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : fullBallCompactInterior ρ × ℝ) :
    fullBallProjectedRhsDensity ρ u D p a b c ψ z =
      fullBallNativeProjectedRhsDensity u D p a b c ψ (z.1.1, z.2) := rfl

/-- The literal native right hand side vanishes outside the actual smooth test support. -/
theorem fullBallNativeProjectedRhsDensity_zero_off_tsupport
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : ParabolicPoint) (hz : z ∉ tsupport ψ) :
    fullBallNativeProjectedRhsDensity u D p a b c ψ z = 0 := by
  have hψ : ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport (x := ((z.1, z.2) : Vec3 × ℝ)) hz
  have hp := projectedEnergyDeficitPolynomial_zero_off_tsupport u
    (fullBallProjectedHarmonicGradientAmbient u D p a b c) D
    (fullBallProjectedHarmonicDerivativeAmbient u D p a b c)
    (fun w ↦ p w - fullBallProjectedMomentumPressure u D p w.2 w.1) ψ z hz
  change 2 * projectedGradientSquare
    (fullBallProjectedVelocityDerivativeAmbient u D p a b c z) * ψ z - _ = 0
  rw [hp, hψ]
  ring

/-- The literal projected compact integral equals its true native joint integral. -/
theorem integral_fullBallProjectedRhsDensity_eq_native
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {ψ : Vec3 × ℝ → ℝ}
    (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b) :
    (∫ z, fullBallProjectedRhsDensity ρ u D p a b c ψ z
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) =
      ∫ z : ParabolicPoint, fullBallNativeProjectedRhsDensity u D p a b c ψ z := by
  exact integral_fullBallInterior_product_eq_integral ρ
    (fullBallNativeProjectedRhsDensity u D p a b c ψ)
    (fun z hz ↦ fullBallNativeProjectedRhsDensity_zero_off_tsupport
      u D p a b c ψ z (fun h ↦ hz (hsupp h)))

/-- Genuine suitability gives actual joint integrability of the native projected RHS. -/
theorem suitable_fullBall_native_projected_rhs_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z) (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b) :
    Integrable (fullBallNativeProjectedRhsDensity u D p a b c ψ) volume := by
  have hR := (suitable_fullBall_projected_time_energy_integrable_localBox
    ρ hρ hρone hsol hbox hab hc hψ hnψ hsupp).2.2
  have hm : MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦
      fullBallNativeProjectedRhsDensity u D p a b c ψ (z.1.1, z.2)) 1
      ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) :=
    memLp_one_iff_integrable.mpr hR
  have hr : IntegrableOn (fullBallNativeProjectedRhsDensity u D p a b c ψ)
      (fullBallCompactInterior ρ ×ˢ Ioo a b) volume :=
    memLp_one_iff_integrable.mp
      ((memLp_fullBallInterior_product_ambient_iff ρ _ 1 (Ioo a b)).mpr hm)
  exact hr.integrable_of_forall_notMem_eq_zero
    (fun z hz ↦ fullBallNativeProjectedRhsDensity_zero_off_tsupport
      u D p a b c ψ z (fun h ↦ hz (hsupp h)))

/-- The genuinely supported native RHS has the exact iterated spatial and time integral. -/
theorem suitable_fullBall_native_projected_rhs_integral_prod
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z) (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b)
    {B : Set Vec3} (hB : tsupport ψ ⊆ B ×ˢ Ioo a b) :
    (∫ z : ParabolicPoint, fullBallNativeProjectedRhsDensity u D p a b c ψ z) =
      ∫ t in Ioo a b, ∫ x in B, fullBallNativeProjectedRhsDensity u D p a b c ψ (x, t) := by
  have hR := suitable_fullBall_native_projected_rhs_integrable
    hρ hρone hsol hbox hab hc hψ hnψ hsupp
  have he : (∫ z : ParabolicPoint, fullBallNativeProjectedRhsDensity u D p a b c ψ z) =
      ∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeProjectedRhsDensity u D p a b c ψ z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz ↦ fullBallNativeProjectedRhsDensity_zero_off_tsupport
      u D p a b c ψ z (fun h ↦ hz (hB h)))).symm
  calc
    _ = ∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeProjectedRhsDensity u D p a b c ψ z := he
    _ = _ := by
      rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
      exact integral_prod_symm _ (by
        rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
        exact hR.restrict)

end FluidSingularSets
