-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PressureForceTime
public import FluidSingularSets.UnitBallPressureProjection

/-!
# The genuine centered suitable pressure curve

The actual spatial L² class of pressure minus its mean has zero integral at
every time, including the conditional zero class at an exceptional slice.
It is therefore a genuine curve in the mean-zero pressure space. The actual
Stokes pressure operator recovers this class from the pressure force. Its
test pairing is the original pressure-divergence term in suitable momentum,
with the mean cancellation proved from compact interior tests.
-/

@[expose] public section

open MeasureTheory Set CKN Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance actualPressureCurveNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

private theorem actualPressure_partialDeriv_memLp {U : Set Vec3}
    (φ : WeakTestFunction U) (i : Fin 3) :
    MemLp (φ.partialDeriv i) 2 (volume.restrict U) := by
  have hcont : Continuous (φ.partialDeriv i) :=
    (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : HasCompactSupport (φ.partialDeriv i) :=
    φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hcont.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self

/-- The actual pressure force pairs by the original pressure, with the spatial
mean removed only in the energy-space representation. -/
theorem pressureEnergyForce_pressure_test
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {r t : ℝ}
    (hp : MemLp (centeredPressureSlice p x₀ r t) 2 (volume.restrict (vec3Ball x₀ r)))
    (φ : StokesVectorTest (vec3Ball x₀ r)) :
    pressureEnergyForce p x₀ r t (stokesEnergyTest φ) =
      -(∑ i : Fin 3, ∫ x in vec3Ball x₀ r, p (x, t) * (φ i).partialDeriv i x) := by
  let U := vec3Ball x₀ r
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  let c := average (volume.restrict U) (fun x ↦ p (x, t))
  have hc : MemLp (fun _ : Vec3 ↦ c) 2 (volume.restrict U) := memLp_const c
  have hpraw : MemLp (fun x ↦ p (x, t)) 2 (volume.restrict U) := by
    exact (memLp_congr_ae (Eventually.of_forall (fun x ↦ by
      change centeredPressureSlice p x₀ r t x + c = p (x, t)
      simp [centeredPressureSlice, c, U]))).mp (hp.add hc)
  have hdi (i : Fin 3) : MemLp ((φ i).partialDeriv i) 2 (volume.restrict U) :=
    actualPressure_partialDeriv_memLp (φ i) i
  have hcp (i : Fin 3) : Integrable
      (fun x ↦ centeredPressureSlice p x₀ r t x * (φ i).partialDeriv i x)
      (volume.restrict U) := hp.integrable_mul (hdi i)
  have hmean (i : Fin 3) :
      (∫ x in U, centeredPressureSlice p x₀ r t x * (φ i).partialDeriv i x) =
        ∫ x in U, p (x, t) * (φ i).partialDeriv i x := by
    simp only [centeredPressureSlice, sub_mul]
    have hraw : Integrable (fun x ↦ p (x, t) * (φ i).partialDeriv i x)
        (volume.restrict U) := hpraw.integrable_mul (hdi i)
    have hconst : Integrable (fun x ↦ c * (φ i).partialDeriv i x)
        (volume.restrict U) := ((hdi i).integrable (by norm_num)).const_mul c
    rw [integral_sub hraw hconst, integral_const_mul,
      weakTest_partialDeriv_integral_eq_zero_on (φ i) i, mul_zero, sub_zero]
  unfold pressureEnergyForce
  rw [dite_eq_left hp, stokesL2PressureGradient_test]
  have heq : (∫ x in U, hp.toLp (centeredPressureSlice p x₀ r t) x *
      ∑ i : Fin 3, (φ i).partialDeriv i x) =
      ∫ x in U, ∑ i : Fin 3, centeredPressureSlice p x₀ r t x * (φ i).partialDeriv i x := by
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with x hx
    rw [hx, Finset.mul_sum]
  change -(∫ x in U, hp.toLp (centeredPressureSlice p x₀ r t) x *
    ∑ i : Fin 3, (φ i).partialDeriv i x) = _
  rw [heq, integral_finsetSum Finset.univ (fun i _ ↦ hcp i)]
  simp_rw [hmean]
  rfl

/-- The original pressure-divergence test pairing holds at almost every actual
suitable slice, without a pressure-gradient or centered-L² premise. -/
theorem suitable_pressureEnergyForce_pressure_tests_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hdom : Metric.ball z (8 * r) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2)),
      ∀ φ : StokesVectorTest (vec3Ball z.1 r),
        pressureEnergyForce p z.1 r t (stokesEnergyTest φ) =
          -(∑ i : Fin 3, ∫ x in vec3Ball z.1 r, p (x, t) * (φ i).partialDeriv i x) := by
  obtain ⟨_, _, _, _, hp, _⟩ := exists_suitable_pressure_energy_dual hsol z hr hdom
  filter_upwards [hp] with t ht
  intro φ
  exact pressureEnergyForce_pressure_test ht φ

/-- The actual conditional centered-pressure class has literal zero integral. -/
theorem actual_centeredPressureSlice_integral_zero
    (p : ParabolicPoint → ℝ) (x₀ : Vec3) (r t : ℝ) :
    (∫ x in vec3Ball x₀ r,
      actualSliceLp (μ := volume.restrict (vec3Ball x₀ r)) (p := 2)
        (fun w : Vec3 × ℝ ↦ centeredPressureSlice p x₀ r w.2 w.1) t x) = 0 := by
  classical
  let : IsFiniteMeasure (volume.restrict (vec3Ball x₀ r)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  unfold actualSliceLp
  split_ifs with h
  · rw [integral_congr_ae h.coeFn_toLp]
    exact integral_sub_average (volume.restrict (vec3Ball x₀ r)) (fun x ↦ p (x, t))
  · rw [integral_congr_ae (Lp.coeFn_zero ℝ 2 (volume.restrict (vec3Ball x₀ r)))]
    simp

/-- The actual suitable pressure modulo its spatial mean, in the true mean-zero
Hilbert pressure space. -/
def unitBallActualPressureCurve (p : ParabolicPoint → ℝ) (t : ℝ) : unitBallMeanZeroL2 :=
  unitBallMeanZeroProjection
    (actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2)
      (fun w : Vec3 × ℝ ↦ centeredPressureSlice p 0 1 w.2 w.1) t)

/-- Mean-zero projection leaves the actual centered-pressure class unchanged. -/
theorem unitBallActualPressureCurve_val_eq_actualSliceLp
    (p : ParabolicPoint → ℝ) (t : ℝ) :
    (unitBallActualPressureCurve p t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) =
      actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2)
        (fun w : Vec3 × ℝ ↦ centeredPressureSlice p 0 1 w.2 w.1) t := by
  change unitBallRemoveMean _ = _
  rw [unitBallRemoveMean_apply]
  have hz := actual_centeredPressureSlice_integral_zero p (0 : Vec3) 1 t
  rw [← unitBallL2Integral_apply] at hz
  simp only [hz, mul_zero, zero_smul, sub_zero]

/-- At every good time the mean-zero curve is the literal centered pressure. -/
theorem unitBallActualPressureCurve_ae
    {p : ParabolicPoint → ℝ} {t : ℝ}
    (hp : MemLp (centeredPressureSlice p 0 1 t) 2 (volume.restrict (vec3Ball 0 1))) :
    (unitBallActualPressureCurve p t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) =ᵐ[
      volume.restrict (vec3Ball 0 1)] centeredPressureSlice p 0 1 t := by
  rw [unitBallActualPressureCurve_val_eq_actualSliceLp]
  exact actualSliceLp_ae _ t hp

/-- The actual Stokes pressure operator recovers the genuine centered-pressure
curve from its canonical gradient force, at every time. -/
theorem pressureEnergyForce_eq_unitBallActualPressureCurve_gradient
    (p : ParabolicPoint → ℝ) (t : ℝ) :
    pressureEnergyForce p 0 1 t = stokesL2PressureGradient
      (unitBallActualPressureCurve p t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := by
  rw [unitBallActualPressureCurve_val_eq_actualSliceLp,
    pressureEnergyForce_eq_actualSliceLp, stokesPressureGradientL_apply]

/-- The genuine mean-zero Stokes pressure of the pressure force is the literal
centered-pressure curve, including at exceptional slices. -/
theorem unitBallStokesPressure_pressureEnergyForce
    (p : ParabolicPoint → ℝ) (t : ℝ) :
    unitBallStokesPressure (pressureEnergyForce p 0 1 t) = unitBallActualPressureCurve p t := by
  rw [pressureEnergyForce_eq_unitBallActualPressureCurve_gradient]
  exact unitBallStokesPressure_pressureGradient _

/-- The genuine mean-zero pressure curve has the actual 5/4 time class supplied
by suitable pressure regularity. -/
theorem memLp_unitBallActualPressureCurve_of_time_moment
    {p : ParabolicPoint → ℝ} {J : Set ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict (vec3Ball 0 1 ×ˢ J)))
    (hfin : (∫⁻ t in J, eLpNorm (centeredPressureSlice p 0 1 t) 2
      (volume.restrict (vec3Ball 0 1)) ^ (5 / 4 : ℝ)) < ∞) :
    MemLp (unitBallActualPressureCurve p) (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict J) := by
  have hF := memLp_pressureEnergyForce_of_time_moment hp hfin
  have hP := hF.continuousLinearMap_comp (𝕜 := ℝ) unitBallStokesPressureL
  apply (memLp_congr_ae (Eventually.of_forall (fun t ↦ ?_))).mp hP
  change unitBallStokesPressure (pressureEnergyForce p 0 1 t) = unitBallActualPressureCurve p t
  exact unitBallStokesPressure_pressureEnergyForce p t

end FluidSingularSets
