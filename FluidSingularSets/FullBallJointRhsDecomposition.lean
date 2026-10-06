-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallJointErrorIntegrability

/-!
# Genuine integral decomposition for joint projected-energy tests

The actual native integrability and compact-support transport identify the
literal tested RHS with its heat, convection, pressure, and Hessian integrals.
True Fubini connects the pressure flux to its centered mixed-class estimates.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Every actual joint test has the literal four-family integral decomposition. -/
theorem suitable_fullBall_joint_rhs_integral_eq_errors
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {B : Set Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z) (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b)
    (hsuppB : tsupport ψ ⊆ B ×ˢ Ioo a b)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    (∫ z, fullBallProjectedRhsDensity ρ u D p a b c ψ z * χ z.2
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) =
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b, fullBallJointHeatError u D p a b c ψ χ z) +
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallJointConvectionError u D p a b c ψ χ z) +
      2 * (∫ t in Ioo a b, ∫ x in B, fullBallJointPressureError u D p a b c ψ χ (x, t)) +
      2 * (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallJointHarmonicError u D p a b c ψ χ z) := by
  let R : ParabolicPoint → ℝ := fun z ↦ fullBallNativeProjectedRhsDensity u D p a b c ψ z * χ z.2
  let HE := fullBallJointHeatError u D p a b c ψ χ
  let CE := fullBallJointConvectionError u D p a b c ψ χ
  let PE := fullBallJointPressureError u D p a b c ψ χ
  let BE := fullBallJointHarmonicError u D p a b c ψ χ
  let μ : Measure ParabolicPoint := volume.restrict (B ×ˢ Ioo a b)
  obtain ⟨hHE, hCE, hPE, hBE⟩ := suitable_fullBall_joint_errors_integrable
    hsol hbox hab hc hρ hρone hψ hnψ hsupp hχ hbχ
  have hcompact : (∫ z, fullBallProjectedRhsDensity ρ u D p a b c ψ z * χ z.2
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) =
        ∫ z : ParabolicPoint, R z :=
    integral_fullBallInterior_product_eq_integral ρ R (fun z hz ↦ by
      change fullBallNativeProjectedRhsDensity u D p a b c ψ z * χ z.2 = 0
      rw [fullBallNativeProjectedRhsDensity_zero_off_tsupport
        u D p a b c ψ z (fun h ↦ hz (hsupp h)), zero_mul])
  have hrestrict : (∫ z : ParabolicPoint, R z) = ∫ z, R z ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦ by
      change fullBallNativeProjectedRhsDensity u D p a b c ψ z * χ z.2 = 0
      rw [fullBallNativeProjectedRhsDensity_zero_off_tsupport
        u D p a b c ψ z (fun h ↦ hz (hsuppB h)), zero_mul])).symm
  have hsplit : (∫ z, R z ∂μ) =
      (∫ z, HE z ∂μ) + (∫ z, CE z ∂μ) + 2 * (∫ z, PE z ∂μ) +
        2 * (∫ z, BE z ∂μ) := by
    have heq : R = fun z ↦ HE z + CE z + 2 * PE z + 2 * BE z :=
      funext fun z ↦ fullBallNativeProjectedRhsDensity_joint_errors_eq u D p a b c ψ χ z
    rw [heq,
      integral_add (f := fun z ↦ HE z + CE z + 2 * PE z) (g := fun z ↦ 2 * BE z)
        ((hHE.restrict.add hCE.restrict).add (hPE.restrict.const_mul 2))
          (hBE.restrict.const_mul 2),
      integral_add (f := fun z ↦ HE z + CE z) (g := fun z ↦ 2 * PE z)
        (hHE.restrict.add hCE.restrict) (hPE.restrict.const_mul 2),
      integral_add hHE.restrict hCE.restrict, integral_const_mul, integral_const_mul]
  have hPfubini : (∫ z, PE z ∂μ) = ∫ t in Ioo a b, ∫ x in B, PE (x, t) := by
    change (∫ z : ParabolicPoint in B ×ˢ Ioo a b, PE z) = _
    rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm _ (by
      rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
      exact hPE.restrict)
  exact (hcompact.trans hrestrict).trans (hsplit.trans (by rw [hPfubini]))

end FluidSingularSets
