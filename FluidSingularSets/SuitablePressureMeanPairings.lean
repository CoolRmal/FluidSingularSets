-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxProjectedWeakGradient
public import FluidSingularSets.SuitableProjectedPressureIdentification
public import FluidSingularSets.MixedSpatialMeans

/-!
# Actual pressure mean cancellation on the original local interval

The original pressure has an integrable spatial average on every genuine
local box. The actual corrected velocity annihilates this mean in compact
spatial divergence tests, and the remaining pressure is exactly the two
native Stokes pressures. All identities use the original time interval.
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

/-- The actual pressure average is integrable in time on any original suitable local box. -/
theorem suitable_original_pressure_spatial_average_integrable_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    Integrable (fun t ↦ average (volume.restrict (vec3Ball 0 1)) (fun x ↦ p (x, t)))
      (volume.restrict J) := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr
    ((measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top).ne
  have hp : MemLp (fun z : Vec3 × ℝ ↦ p z) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.memLp_pressure hbox
  exact integrable_spatial_average_of_joint_integrable (hp.integrable (by norm_num))

/-- The actual momentum pressure is identified on the unchanged suitable local interval. -/
theorem suitable_unitBall_projected_pressure_identification_ae_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ p (x, t) -
        harmonicSpatialPressureRepresentative (-unitBallMomentumForceCurve u D p t) x)
        =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      (fun x ↦ (unitBallConvectivePressureCurve u t).val x +
        (unitBallViscousPressureCurve D t).val x +
          average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t))) := by
  have hp := (suitable_centered_pressure_energy_dual_localBox (by norm_num) hsol hbox).1
  filter_upwards [hp, suitable_unitBall_momentumForce_gradientFree_ae_localBox hsol hbox]
    with t hpt hGt
  exact unitBall_projected_pressure_identification_ae u D p t hpt hGt

/-- The literal tested corrected velocity on the original local interval. -/
def localBoxProjectedPressureTest
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 → ℝ) (θ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  θ z.2 * ∑ i : Fin 3, localBoxProjectedVelocityAmbient u D p a b c z i *
    spatialDeriv ψ i z.1

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- The literal tested velocity has true spatial L² classes at almost every original time. -/
theorem localBoxProjectedPressureTest_memLp_two_slices_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), MemLp
      (fun x ↦ localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) 2
        (volume.restrict B) := by
  have hψd (i : Fin 3) : MemLp (spatialDeriv ψ.toFun i) ⊤ (volume.restrict B) :=
    ((stokesWeakTestDerivative ψ i).contDiff.continuous.memLp_of_hasCompactSupport
      (stokesWeakTestDerivative ψ i).hasCompactSupport).restrict B
  filter_upwards [localBoxProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p a b c hsol hbox hB hBK] with t ht
  have hs : MemLp (fun x ↦ ∑ i : Fin 3,
      localBoxProjectedVelocityAmbient u D p a b c (x, t) i * spatialDeriv ψ.toFun i x) 2
        (volume.restrict B) := memLp_finsetSum Finset.univ
    (fun i _ ↦ (ht.1.eval i).mul (hψd i))
  exact hs.const_mul (θ t)

/-- The actual common divergence set kills the true spatial test, including any time weight. -/
theorem localBoxProjectedPressureTest_spatial_integral_zero_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) = 0 := by
  filter_upwards [localBoxProjectedVelocityAmbient_divergenceFree_slices_ae
    u D p a b c hsol hbox hB hBK] with t ht
  simp only [localBoxProjectedPressureTest]
  rw [integral_const_mul, ht ψ, mul_zero]

/-- The literal mean-pressure spatial pairing vanishes on a common full set of times. -/
theorem suitable_original_pressure_mean_pairing_zero_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t)) *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) = 0 := by
  filter_upwards [localBoxProjectedPressureTest_spatial_integral_zero_ae
    (c := c) hsol hbox hB hBK ψ θ] with t ht
  rw [integral_const_mul, ht, mul_zero]

/-- The true iterated mean-pressure pairing is integrable in time and has integral zero. -/
theorem suitable_original_pressure_mean_iterated_pairing_integrable_zero_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    Integrable (fun t ↦ ∫ x in B,
      average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t)) *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t))
          (volume.restrict (Ioo a b)) ∧
    (∫ t in Ioo a b, ∫ x in B,
      average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t)) *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) = 0 := by
  have hz := suitable_original_pressure_mean_pairing_zero_ae_localBox
    (c := c) hsol hbox hB hBK ψ θ
  exact ⟨(integrable_zero ℝ ℝ (volume.restrict (Ioo a b))).congr
    (hz.mono fun _ ht ↦ ht.symm),
    integral_eq_zero_of_ae hz⟩

/-- The actual projected pressure pairing equals the two true Stokes pressure pairings. -/
theorem suitable_projected_pressure_pairing_eq_stokes_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, (p (x, t) -
        harmonicSpatialPressureRepresentative (-unitBallMomentumForceCurve u D p t) x) *
          localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) =
      (∫ x in B, (unitBallConvectivePressureCurve u t).val x *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) +
      (∫ x in B, (unitBallViscousPressureCurve D t).val x *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hBq : B ⊆ vec3Ball 0 (1 / 4) := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono hB1).trans_lt volume_vec3Ball_lt_top).ne
  filter_upwards [suitable_unitBall_projected_pressure_identification_ae_localBox hsol hbox,
    localBoxProjectedPressureTest_memLp_two_slices_ae (c := c) hsol hbox hB hBK ψ θ,
    localBoxProjectedPressureTest_spatial_integral_zero_ae (c := c) hsol hbox hB hBK ψ θ]
    with t hp ht hz
  let G : Vec3 → ℝ := fun x ↦ localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)
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
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hBq hp] with x hx
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
theorem suitable_projected_pressure_iterated_pairing_eq_stokes_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (ψ : WeakTestFunction B) (θ : ℝ → ℝ) :
    (∫ t in Ioo a b, ∫ x in B, (p (x, t) -
      harmonicSpatialPressureRepresentative (-unitBallMomentumForceCurve u D p t) x) *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) =
    ∫ t in Ioo a b,
      (∫ x in B, (unitBallConvectivePressureCurve u t).val x *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) +
      (∫ x in B, (unitBallViscousPressureCurve D t).val x *
        localBoxProjectedPressureTest u D p a b c ψ.toFun θ (x, t)) :=
  integral_congr_ae
    (suitable_projected_pressure_pairing_eq_stokes_ae_localBox hsol hbox hB hBK ψ θ)

end LocalBox

end FluidSingularSets
