-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedWeakGradient
public import FluidSingularSets.SuitablePressureMeanPairings

/-!
# Full-ball pressure mean cancellation on the original interval

The actual harmonic pressure representative agrees with its Stokes pressure
class on the whole projection ball. The genuine corrected divergence test
therefore cancels the original spatial pressure mean on every compact inner
carrier. Both remaining pressures are the literal native Stokes operators.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The genuine full-ball scalar pressure of the negative momentum force. -/
def fullBallProjectedMomentumPressure
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t : ℝ) : Vec3 → ℝ :=
  unitBallFullHarmonicForcePressureRepresentative
    (unitBallGradientFreeForceProjection (-unitBallMomentumForceCurve u D p t))

/-- Gradient-annihilating forces have their literal full-ball pressure representative. -/
theorem fullBallPressureRepresentative_ae_of_gradientFree
    (F : StokesEnergyForce (vec3Ball 0 1)) (hF : F ∈ unitBallGradientFreeForce) :
    unitBallFullHarmonicForcePressureRepresentative (unitBallGradientFreeForceProjection F)
      =ᵐ[volume.restrict (vec3Ball 0 1)]
        (unitBallStokesPressure F : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := by
  let G : unitBallGradientFreeForce := ⟨F, hF⟩
  have he : unitBallGradientFreeForceProjection F = G :=
    unitBallGradientFreeForceProjection_of_gradientFree G
  rw [he]
  exact (unitBallFullHarmonicForcePressureRepresentative_ae G).symm

/-- The actual momentum pressure difference has its two-pressure form on the whole ball. -/
theorem fullBall_projected_pressure_identification_ae
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t : ℝ)
    (hp : MemLp (centeredPressureSlice p 0 1 t) 2 (volume.restrict (vec3Ball 0 1)))
    (hG : unitBallMomentumForceCurve u D p t ∈ unitBallGradientFreeForce) :
    (fun x ↦ p (x, t) - fullBallProjectedMomentumPressure u D p t x)
      =ᵐ[volume.restrict (vec3Ball 0 1)]
    (fun x ↦ (unitBallConvectivePressureCurve u t).val x +
      (unitBallViscousPressureCurve D t).val x +
        average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t))) := by
  let P0 := (unitBallActualPressureCurve p t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
  let P1 := (unitBallConvectivePressureCurve u t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
  let P2 := (unitBallViscousPressureCurve D t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
  have hpress : (unitBallStokesPressure (-unitBallMomentumForceCurve u D p t) :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) = P0 - P1 - P2 := by
    exact congrArg Subtype.val (unitBallMomentumForceCurve_negative_pressure u D p t)
  have hrep := fullBallPressureRepresentative_ae_of_gradientFree
    (-unitBallMomentumForceCurve u D p t) (unitBallGradientFreeForce.neg_mem hG)
  rw [hpress] at hrep
  filter_upwards [hrep, unitBallActualPressureCurve_ae hp,
    Lp.coeFn_sub P0 P1, Lp.coeFn_sub (P0 - P1) P2] with x hx h0x h1x h2x
  change P0 x = p (x, t) - average (volume.restrict (vec3Ball 0 1))
    (fun y ↦ p (y, t)) at h0x
  change (P0 - P1) x = P0 x - P1 x at h1x
  change (P0 - P1 - P2) x = (P0 - P1) x - P2 x at h2x
  have he : fullBallProjectedMomentumPressure u D p t x = P0 x - P1 x - P2 x :=
    hx.trans (h2x.trans (congrArg (fun a : ℝ ↦ a - P2 x) h1x))
  change p (x, t) - fullBallProjectedMomentumPressure u D p t x = P1 x + P2 x + _
  linear_combination -h0x - he

/-- Actual suitable data identify the full-ball momentum pressure on one common time set. -/
theorem suitable_fullBall_projected_pressure_identification_ae_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ p (x, t) - fullBallProjectedMomentumPressure u D p t x)
        =ᵐ[volume.restrict (vec3Ball 0 1)]
      (fun x ↦ (unitBallConvectivePressureCurve u t).val x +
        (unitBallViscousPressureCurve D t).val x +
          average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t))) := by
  have hp := (suitable_centered_pressure_energy_dual_localBox (by norm_num) hsol hbox).1
  filter_upwards [hp, suitable_unitBall_momentumForce_gradientFree_ae_localBox hsol hbox]
    with t hpt hGt
  exact fullBall_projected_pressure_identification_ae u D p t hpt hGt

/-- The literal tested corrected velocity on the original local interval. -/
def fullBallProjectedPressureTest
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 → ℝ) (θ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  θ z.2 * ∑ i : Fin 3, fullBallProjectedVelocityAmbient u D p a b c z i *
    spatialDeriv ψ i z.1

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- The literal tested velocity has true spatial L² classes at almost every original time. -/
theorem fullBallProjectedPressureTest_memLp_two_slices_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), MemLp
      (fun x ↦ fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) 2
        (volume.restrict B) := by
  have hψd (i : Fin 3) : MemLp (spatialDeriv ψ.toFun i) ⊤ (volume.restrict B) :=
    ((stokesWeakTestDerivative ψ i).contDiff.continuous.memLp_of_hasCompactSupport
      (stokesWeakTestDerivative ψ i).hasCompactSupport).restrict B
  filter_upwards [fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p a b c hsol hbox hρ hρone hB hBK] with t ht
  have hs : MemLp (fun x ↦ ∑ i : Fin 3,
      fullBallProjectedVelocityAmbient u D p a b c (x, t) i * spatialDeriv ψ.toFun i x) 2
        (volume.restrict B) := memLp_finsetSum Finset.univ
    (fun i _ ↦ (ht.1.eval i).mul (hψd i))
  exact hs.const_mul (θ t)

/-- The actual common divergence set kills the true spatial test, including any time weight. -/
theorem fullBallProjectedPressureTest_spatial_integral_zero_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) = 0 := by
  filter_upwards [fullBallProjectedVelocityAmbient_divergenceFree_slices_ae
    u D p a b c hsol hbox hρ hρone hB hBK] with t ht
  simp only [fullBallProjectedPressureTest]
  rw [integral_const_mul, ht ψ, mul_zero]

/-- The literal mean-pressure spatial pairing vanishes on a common full set of times. -/
theorem suitable_fullBall_pressure_mean_pairing_zero_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t)) *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) = 0 := by
  filter_upwards [fullBallProjectedPressureTest_spatial_integral_zero_ae
    (c := c) hsol hbox hρ hρone hB hBK ψ θ] with t ht
  rw [integral_const_mul, ht, mul_zero]

/-- The true iterated mean-pressure pairing is integrable in time and has integral zero. -/
theorem suitable_fullBall_pressure_mean_iterated_pairing_integrable_zero_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    Integrable (fun t ↦ ∫ x in B,
      average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t)) *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t))
          (volume.restrict (Ioo a b)) ∧
    (∫ t in Ioo a b, ∫ x in B,
      average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t)) *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) = 0 := by
  have hz := suitable_fullBall_pressure_mean_pairing_zero_ae_localBox
    (c := c) hsol hbox hρ hρone hB hBK ψ θ
  exact ⟨(integrable_zero ℝ ℝ (volume.restrict (Ioo a b))).congr
    (hz.mono fun _ ht ↦ ht.symm),
    integral_eq_zero_of_ae hz⟩

/-- The actual projected pressure pairing equals the two true Stokes pressure pairings. -/
theorem suitable_fullBall_pressure_pairing_eq_stokes_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, (p (x, t) -
        fullBallProjectedMomentumPressure u D p t x) *
          fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) =
      (∫ x in B, (unitBallConvectivePressureCurve u t).val x *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) +
      (∫ x in B, (unitBallViscousPressureCurve D t).val x *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono hB1).trans_lt volume_vec3Ball_lt_top).ne
  filter_upwards [suitable_fullBall_projected_pressure_identification_ae_localBox hsol hbox,
    fullBallProjectedPressureTest_memLp_two_slices_ae (c := c) hsol hbox hρ hρone hB hBK ψ θ,
    fullBallProjectedPressureTest_spatial_integral_zero_ae (c := c) hsol hbox hρ hρone hB hBK ψ θ]
    with t hp ht hz
  let G : Vec3 → ℝ := fun x ↦ fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)
  let m := average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t))
  have hP1 := ((Lp.memLp (unitBallConvectivePressureCurve u t).val).mono_measure
    (Measure.restrict_mono_set volume hB1)).integrable_mul ht
  have hP2 := ((Lp.memLp (unitBallViscousPressureCurve D t).val).mono_measure
    (Measure.restrict_mono_set volume hB1)).integrable_mul ht
  change Integrable (fun x ↦ (unitBallConvectivePressureCurve u t).val x * G x)
    (volume.restrict B) at hP1
  change Integrable (fun x ↦ (unitBallViscousPressureCurve D t).val x * G x)
    (volume.restrict B) at hP2
  have hm : Integrable (fun x ↦ m * G x) (volume.restrict B) :=
    (ht.integrable (by norm_num)).const_mul m
  calc
    _ = ∫ x in B, ((unitBallConvectivePressureCurve u t).val x +
        (unitBallViscousPressureCurve D t).val x + m) * G x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hB1 hp] with x hx
      exact congrArg (fun r : ℝ ↦ r * G x) hx
    _ = _ := by
      simp_rw [add_mul]
      have hmean : (∫ x in B, m * G x) = 0 := by
        calc
          _ = m * ∫ x in B, G x := integral_const_mul _ _
          _ = 0 := by simpa only [mul_zero] using congrArg (fun r : ℝ ↦ m * r) hz
      have hs := integral_add (hP1.add hP2) hm
      have hh := congrArg₂ (fun r s : ℝ ↦ r + s) (integral_add hP1 hP2) hmean
      exact hs.trans (hh.trans (add_zero _))

/-- The original iterated projected pressure integral has its literal two-pressure form. -/
theorem suitable_fullBall_pressure_iterated_pairing_eq_stokes_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    (∫ t in Ioo a b, ∫ x in B, (p (x, t) -
      fullBallProjectedMomentumPressure u D p t x) *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) =
    ∫ t in Ioo a b,
      (∫ x in B, (unitBallConvectivePressureCurve u t).val x *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) +
      (∫ x in B, (unitBallViscousPressureCurve D t).val x *
        fullBallProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) :=
  integral_congr_ae
    (suitable_fullBall_pressure_pairing_eq_stokes_ae_localBox hsol hbox hρ hρone hB hBK ψ θ)

end LocalBox

end FluidSingularSets
