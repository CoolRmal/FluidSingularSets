-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicValues
public import FluidSingularSets.FullBallProjectedWeakGradient

/-!
# Genuine full-ball projected field classes

The actual force primitive is transported through the proved pressure, gradient,
and Hessian operators at each compact inner radius. This supplies genuine joint
correction classes and the actual mixed pressure class on the original interval.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance fullBallProjectedDataForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallProjectedDataForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The genuine gradient operator at the actual intermediate boundary margin. -/
def fullBallProjectedGradientOperator {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, Vec3) :=
  fullBallHarmonicGradientExtended (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ hρone)
    (show (ρ + 1) / 2 < 1 by linarith)
    (fullBallCompactInterior_subset hρ (show ρ < (ρ + 1) / 2 by linarith))

/-- The genuine pressure value operator at the same actual boundary margin. -/
def fullBallProjectedValuesOperator {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, ℝ) :=
  fullBallHarmonicValuesExtended (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ hρone)
    (show (ρ + 1) / 2 < 1 by linarith)
    (fullBallCompactInterior_subset hρ (show ρ < (ρ + 1) / 2 by linarith))

/-- The genuine derivative-first Hessian operator on the same compact radius. -/
def fullBallProjectedHessianOperator {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
      C(fullBallCompactInterior ρ, StokesGradientMatrix) :=
  fullBallHarmonicHessianExtended (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ hρone)
    (show (ρ + 1) / 2 < 1 by linarith)
    (fullBallCompactInterior_subset hρ (show ρ < (ρ + 1) / 2 by linarith))

/-- The actual compact continuous harmonic gradient of the negative force primitive. -/
def fullBallProjectedGradientCompact
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) (t : ℝ) :
    C(fullBallCompactInterior ρ, Vec3) :=
  fullBallProjectedGradientOperator hρ hρone (-localBoxForcePrimitive u D p a b c t)

/-- The actual compact continuous Hessian of that same force primitive. -/
def fullBallProjectedHessianCompact
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) (t : ℝ) :
    C(fullBallCompactInterior ρ, StokesGradientMatrix) :=
  fullBallProjectedHessianOperator hρ hρone (-localBoxForcePrimitive u D p a b c t)

/-- The actual compact pressure values of the negative momentum derivative force. -/
def fullBallProjectedPressureCompact
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) (t : ℝ) :
    C(fullBallCompactInterior ρ, ℝ) :=
  fullBallProjectedValuesOperator hρ hρone (-unitBallMomentumForceCurve u D p t)

/-- The genuine compact gradient is literally the full-ball ambient correction. -/
theorem fullBallProjectedGradientCompact_apply
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) (x : fullBallCompactInterior ρ) (t : ℝ) :
    fullBallProjectedGradientCompact u D p a b c hρ hρone t x =
      fullBallProjectedHarmonicGradientAmbient u D p a b c (x.1, t) := rfl

/-- Literal Hessian evaluation uses the actual velocity-component/derivative order. -/
theorem fullBallProjectedHessianCompact_apply
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) (x : fullBallCompactInterior ρ)
    (t : ℝ) (i j : Fin 3) :
    fullBallProjectedHessianCompact u D p a b c hρ hρone t x (j, i) =
      fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x.1, t) i j := rfl

/-- The compact pressure value is the genuine full-ball scalar representative. -/
theorem fullBallProjectedPressureCompact_apply
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1)
    (x : fullBallCompactInterior ρ) (t : ℝ) :
    fullBallProjectedPressureCompact u D p hρ hρone t x =
      unitBallFullHarmonicForcePressureRepresentative
        (unitBallGradientFreeForceProjection (-unitBallMomentumForceCurve u D p t)) x.1 := rfl

/-- Actual original suitable slice energy gives both genuine correction curve classes. -/
theorem fullBallProjected_correction_curves_memLp_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    MemLp (fullBallProjectedGradientCompact u D p a b c hρ hρone) ⊤
        (volume.restrict (Ioo a b)) ∧
      MemLp (fullBallProjectedHessianCompact u D p a b c hρ hρone) ⊤
        (volume.restrict (Ioo a b)) := by
  have hM := (suitable_velocityForceCurve_memLp_top hsol hbox).ae_eq
    (suitable_unitBall_velocityForce_ae_primitive_localBox hsol hbox hab hc)
  exact ⟨hM.neg.continuousLinearMap_comp (fullBallProjectedGradientOperator hρ hρone),
    hM.neg.continuousLinearMap_comp (fullBallProjectedHessianOperator hρ hρone)⟩

/-- The actual compact correction and every true Hessian entry have genuine joint bounds. -/
theorem fullBallProjected_correction_joint_memLp_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦
      fullBallProjectedGradientCompact u D p a b c hρ hρone z.2 z.1) ⊤
      ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ∧
      ∀ i j, MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦
        fullBallProjectedHessianCompact u D p a b c hρ hρone z.2 z.1 (j, i)) ⊤
        ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) := by
  obtain ⟨hH, hB⟩ :=
    fullBallProjected_correction_curves_memLp_top hsol hbox hab hc hρ hρone
  refine ⟨memLp_continuousMap_field hH, ?_⟩
  have hBj := memLp_continuousMap_field (μ := fullBallInteriorMeasure ρ) hB
  intro i j
  exact hBj.eval_piLp (j, i)

/-- Genuine momentum integrability gives the actual mixed pressure class on the same interval. -/
theorem fullBallProjected_pressure_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q a b ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    ProjectedEnergySliceData (fullBallInteriorMeasure ρ) (volume.restrict (Ioo a b)) 1
      (fun z : fullBallCompactInterior ρ × ℝ ↦
        fullBallProjectedPressureCompact u D p hρ hρone z.2 z.1) := by
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  exact projectedEnergySliceData_one_continuousMap
    ((memLp_one_iff_integrable.mpr hg).neg.continuousLinearMap_comp
      (fullBallProjectedValuesOperator hρ hρone))

/-- Literal ambient compatibility gives genuine joint bounds on every compact radius. -/
theorem fullBallProjected_correction_ambient_joint_memLp_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    MemLp (fullBallProjectedHarmonicGradientAmbient u D p a b c) ⊤
        (volume.restrict (fullBallCompactInterior ρ ×ˢ Ioo a b)) ∧
      MemLp (fullBallProjectedHarmonicDerivativeAmbient u D p a b c) ⊤
        (volume.restrict (fullBallCompactInterior ρ ×ˢ Ioo a b)) := by
  obtain ⟨hH, hB⟩ :=
    fullBallProjected_correction_joint_memLp_top hsol hbox hab hc hρ hρone
  refine ⟨(memLp_fullBallInterior_product_ambient_iff ρ _ _ _).mpr hH, ?_⟩
  apply memLp_pi_iff.mpr
  intro i
  apply memLp_pi_iff.mpr
  intro j
  exact (memLp_fullBallInterior_product_ambient_iff ρ _ _ _).mpr (hB i j)

/-- The genuine corrected velocity and its true gradient have finite joint energy. -/
theorem fullBallProjectedVelocityAmbient_joint_memLp_two
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) {B : Set Vec3} (hBK : B ⊆ fullBallCompactInterior ρ) :
    MemLp (fullBallProjectedVelocityAmbient u D p a b c) 2
        (volume.restrict (B ×ˢ Ioo a b)) ∧
      MemLp (fullBallProjectedVelocityDerivativeAmbient u D p a b c) 2
        (volume.restrict (B ×ˢ Ioo a b)) := by
  let J := Ioo a b
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    simp only [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top)
  obtain ⟨hU, hD, _hp⟩ := fullBallProjected_memLp hsol hbox hab hρ hρone
  obtain ⟨hH, hB⟩ :=
    fullBallProjected_correction_ambient_joint_memLp_top hsol hbox hab hc hρ hρone
  have hU2 := (memLp_fullBallInterior_product_ambient_iff ρ u 2 J).mpr
    (hU.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3))
  have hD2 := (memLp_fullBallInterior_product_ambient_iff ρ D 2 J).mpr hD
  have hH2 := (memLp_fullBallInterior_product_ambient_iff ρ
    (fullBallProjectedHarmonicGradientAmbient u D p a b c) 2 J).mpr
    (((memLp_fullBallInterior_product_ambient_iff ρ
      (fullBallProjectedHarmonicGradientAmbient u D p a b c) ⊤ J).mp hH).mono_exponent le_top)
  have hB2 := (memLp_fullBallInterior_product_ambient_iff ρ
    (fullBallProjectedHarmonicDerivativeAmbient u D p a b c) 2 J).mpr
    (((memLp_fullBallInterior_product_ambient_iff ρ
      (fullBallProjectedHarmonicDerivativeAmbient u D p a b c) ⊤ J).mp hB).mono_exponent le_top)
  have hsub : B ×ˢ J ⊆ fullBallCompactInterior ρ ×ˢ J := prod_mono hBK le_rfl
  exact ⟨(hU2.add hH2).mono_measure (Measure.restrict_mono_set volume hsub),
    (hD2.add hB2).mono_measure (Measure.restrict_mono_set volume hsub)⟩

set_option maxHeartbeats 1000000 in
/-- The actual corrected velocity has good spatial energy slices and a true time bound. -/
theorem fullBallProjected_corrected_velocity_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    (∀ᵐ t ∂volume.restrict (Ioo a b), MemLp
      (fun x : fullBallCompactInterior ρ ↦
        fullBallProjectedVelocityAmbient u D p a b c (x.1, t)) 2
          (fullBallInteriorMeasure ρ)) ∧
      MemLp (actualSliceLp (μ := fullBallInteriorMeasure ρ) (p := 2)
        (fun z : fullBallCompactInterior ρ × ℝ ↦
          fullBallProjectedVelocityAmbient u D p a b c (z.1.1, z.2))) ⊤
        (volume.restrict (Ioo a b)) := by
  obtain ⟨hu, huC⟩ := fullBallProjected_velocity_slice_data hsol hbox hab hρ hρone
  have hH := (fullBallProjected_correction_curves_memLp_top hsol hbox hab hc hρ hρone).1
  have h := actual_velocity_slice_data_add_continuousMap hu huC hH
  simpa only [fullBallProjectedGradientCompact_apply, fullBallProjectedVelocityAmbient] using h

end FluidSingularSets
