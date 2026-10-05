-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PressureEnergyDual
public import FluidSingularSets.StokesPressureProjection
public import CKN.Foundation.Euclidean.SmoothIBP
public import FluidSingularSets.SliceLpMeasurable

/-!
# Actual pressure gradients in the Stokes energy dual

The suitable pressure is square integrable modulo its spatial mean on almost
every interior slice. Its genuine weak gradient therefore defines an energy
functional. The literal weak-gradient test pairing is proved here, including
the cancellation of the spatial mean, and the actual Stokes pressure
projection fixes this functional.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A compact interior scalar test derivative has zero spatial integral. -/
theorem weakTest_partialDeriv_integral_eq_zero_on {U : Set Vec3}
    (φ : WeakTestFunction U) (i : Fin 3) :
    (∫ x in U, φ.partialDeriv i x) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have h := integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
      (u := fun _ : Vec3 ↦ (1 : ℝ)) contDiff_const φ.contDiff φ.hasCompactSupport i
    simpa [spatialDeriv, WeakTestFunction.partialDeriv] using h
  · intro x hx
    have hout : x ∉ tsupport φ.toFun := fun h ↦ hx (φ.tsupport_subset h)
    change (fderiv ℝ φ.toFun x) (basisVec i) = 0
    rw [fderiv_of_notMem_tsupport ℝ hout]
    rfl

private theorem weakTest_partialDeriv_memLp {U : Set Vec3}
    (φ : WeakTestFunction U) (i : Fin 3) (P : ℝ≥0∞) :
    MemLp (φ.partialDeriv i) P (volume.restrict U) := by
  have hcont : Continuous (φ.partialDeriv i) :=
    (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : HasCompactSupport (φ.partialDeriv i) :=
    φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hcont.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self

/-- Subtracting a spatial constant preserves the genuine weak pressure gradient. -/
theorem pressure_sub_const_hasWeakGradient {U : Set Vec3}
    [IsFiniteMeasure (volume.restrict U)] {p : Vec3 → ℝ} {Dp : Vec3 → Vec3}
    (hp : MemLp p 2 (volume.restrict U)) (hweak : HasWeakGradientOn U p Dp) (c : ℝ) :
    HasWeakGradientOn U (fun x ↦ p x - c) Dp := by
  intro i φ hφ hφc hφU
  let ψ : WeakTestFunction U := ⟨φ, hφ, hφc, hφU⟩
  have hd : MemLp (ψ.partialDeriv i) 2 (volume.restrict U) :=
    weakTest_partialDeriv_memLp ψ i 2
  have hid : Integrable (ψ.partialDeriv i) (volume.restrict U) := hd.integrable (by norm_num)
  have hpd : Integrable (fun x ↦ p x * ψ.partialDeriv i x) (volume.restrict U) :=
    hp.integrable_mul hd
  change (∫ x in U, (p x - c) * ψ.partialDeriv i x) = -∫ x in U, Dp x i * ψ x
  simp_rw [sub_mul]
  rw [integral_sub hpd (hid.const_mul c), integral_const_mul,
    weakTest_partialDeriv_integral_eq_zero_on ψ i, mul_zero, sub_zero]
  exact (hweak i) ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset

/-- The true energy-dual pressure gradient has its quantitative operator bound. -/
theorem stokesL2PressureGradient_norm_le {U : Set Vec3}
    (p : Lp ℝ 2 (volume.restrict U)) :
    ‖stokesL2PressureGradient p‖ ≤ ‖stokesEnergyDivergence U‖ * ‖p‖ := by
  refine (stokesL2PressureGradient p).opNorm_le_bound (by positivity) ?_
  intro v
  change ‖-(inner ℝ p (stokesEnergyDivergence U v))‖ ≤ _
  rw [norm_neg]
  exact (norm_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left ((stokesEnergyDivergence U).le_opNorm v)
      (norm_nonneg p)).trans_eq (by ring))

/-- The actual weak gradient pairs with a Stokes test by its literal integral. -/
theorem stokesL2PressureGradient_weakGradient_test {U : Set Vec3}
    [IsFiniteMeasure (volume.restrict U)] {p : Vec3 → ℝ} {Dp : Vec3 → Vec3}
    (hp : MemLp p 2 (volume.restrict U))
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict U))
    (hweak : HasWeakGradientOn U p Dp) (φ : StokesVectorTest U) :
    stokesL2PressureGradient (hp.toLp p) (stokesEnergyTest φ) =
      ∫ x in U, ∑ i : Fin 3, Dp x i * φ i x := by
  have hpi (i : Fin 3) : Integrable (fun x ↦ p x * (φ i).partialDeriv i x)
      (volume.restrict U) := hp.integrable_mul (weakTest_partialDeriv_memLp (φ i) i 2)
  have hDi (i : Fin 3) : Integrable (fun x ↦ Dp x i * φ i x)
      (volume.restrict U) := by
    have hi := hDp.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
    have hφ : MemLp (φ i).toFun ⊤ (volume.restrict U) :=
      (((φ i).contDiff.continuous.memLp_of_hasCompactSupport
        (φ i).hasCompactSupport).mono_measure Measure.restrict_le_self)
    have hh := (hi.integrable (by norm_num)).mul_of_top_right hφ
    change Integrable (fun x ↦ φ i x * Dp x i) (volume.restrict U) at hh
    exact hh.congr (Filter.Eventually.of_forall (fun x ↦ mul_comm _ _))
  rw [stokesL2PressureGradient_test]
  have heq : (∫ x in U, hp.toLp p x * ∑ i : Fin 3, (φ i).partialDeriv i x) =
      ∫ x in U, ∑ i : Fin 3, p x * (φ i).partialDeriv i x := by
    apply integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with x hx
    rw [hx, Finset.mul_sum]
  rw [heq, integral_finsetSum Finset.univ (fun i _ ↦ hpi i),
    integral_finsetSum Finset.univ (fun i _ ↦ hDi i)]
  have hw (i : Fin 3) : (∫ x in U, p x * (φ i).partialDeriv i x) =
      -(∫ x in U, Dp x i * φ i x) :=
    (hweak i) (φ i).toFun (φ i).contDiff (φ i).hasCompactSupport (φ i).tsupport_subset
  simp_rw [hw]
  simp

/-- The literal pressure-minus-mean energy functional on every time slice.
The zero branch only defines the function on the exceptional non-L² slices. -/
def pressureEnergyForce (p : ParabolicPoint → ℝ) (x₀ : Vec3) (r t : ℝ) :
    StokesEnergyForce (vec3Ball x₀ r) := by
  classical
  exact if h : MemLp (centeredPressureSlice p x₀ r t) 2 (volume.restrict (vec3Ball x₀ r)) then
    stokesL2PressureGradient (h.toLp (centeredPressureSlice p x₀ r t))
  else 0

/-- The actual pressure projection fixes the canonical pressure functional. -/
theorem stokesPressureProjection_pressureEnergyForce
    (p : ParabolicPoint → ℝ) (x₀ : Vec3) (r t : ℝ) :
    stokesPressureProjection (vec3Ball x₀ r) (pressureEnergyForce p x₀ r t) =
      pressureEnergyForce p x₀ r t := by
  unfold pressureEnergyForce
  split_ifs with h
  · exact stokesPressureProjection_pressureGradient _
  · exact (stokesPressureProjection _).map_zero

/-- On an actual L² slice the canonical force is the genuine pressure gradient. -/
theorem pressureEnergyForce_weakGradient_test
    {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3}
    {x₀ : Vec3} {r t : ℝ}
    (hp : MemLp (centeredPressureSlice p x₀ r t) 2 (volume.restrict (vec3Ball x₀ r)))
    (hDp : MemLp (fun x ↦ Dp (x, t)) (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (vec3Ball x₀ r)))
    (hweak : HasWeakGradientOn (vec3Ball x₀ r) (fun x ↦ p (x, t))
      (fun x ↦ Dp (x, t))) (φ : StokesVectorTest (vec3Ball x₀ r)) :
    pressureEnergyForce p x₀ r t (stokesEnergyTest φ) =
      ∫ x in vec3Ball x₀ r, ∑ i : Fin 3, Dp (x, t) i * φ i x := by
  let U := vec3Ball x₀ r
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  let c := average (volume.restrict U) (fun x ↦ p (x, t))
  have hc : MemLp (fun _ : Vec3 ↦ c) 2 (volume.restrict U) := memLp_const c
  have hpraw : MemLp (fun x ↦ p (x, t)) 2 (volume.restrict U) := by
    have h := hp.add hc
    exact (memLp_congr_ae (Filter.Eventually.of_forall (fun x ↦ by
      change centeredPressureSlice p x₀ r t x + c = p (x, t)
      simp [centeredPressureSlice, c, U]))).mp h
  have hw : HasWeakGradientOn U (centeredPressureSlice p x₀ r t) (fun x ↦ Dp (x, t)) :=
    pressure_sub_const_hasWeakGradient hpraw hweak c
  unfold pressureEnergyForce
  rw [dite_eq_left hp]
  exact stokesL2PressureGradient_weakGradient_test hp hDp hw φ

/-- Actual suitable data construct a joint weak pressure gradient whose canonical
energy force has the literal gradient pairing and is fixed by the projection. -/
theorem exists_suitable_pressure_energy_force
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hdom : Metric.ball z (8 * r) ⊆ spaceTimeSet Ω I) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (vec3Ball z.1 (2 * r) ×ˢ Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2))) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2)),
        ∀ φ : StokesVectorTest (vec3Ball z.1 r),
          pressureEnergyForce p z.1 r t (stokesEnergyTest φ) =
            ∫ x in vec3Ball z.1 r, ∑ i : Fin 3, Dp (x, t) i * φ i x) ∧
      (∀ t, stokesPressureProjection (vec3Ball z.1 r) (pressureEnergyForce p z.1 r t) =
        pressureEnergyForce p z.1 r t) ∧
      (∫⁻ t in Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2),
        eLpNorm (centeredPressureSlice p z.1 r t) 2
          (volume.restrict (vec3Ball z.1 r)) ^ (5 / 4 : ℝ)) < ∞ := by
  obtain ⟨Dp, hm, hD, hw, hp, hfin⟩ := exists_suitable_pressure_energy_dual hsol z hr hdom
  refine ⟨Dp, hm, hD, ?_, fun t ↦ stokesPressureProjection_pressureEnergyForce p z.1 r t, hfin⟩
  have hDs := spatial_memLp_ae_of_joint_memLp (by norm_num : (0 : ℝ) < 5 / 4) hD
  have hsub : vec3Ball z.1 r ⊆ vec3Ball z.1 (2 * r) := by
    intro x hx
    change vec3EuclideanNorm (x - z.1) < r at hx
    change vec3EuclideanNorm (x - z.1) < 2 * r
    exact lt_of_lt_of_le hx (by linarith)
  filter_upwards [hw, hp, hDs] with t hwt hpt hDt
  intro φ
  exact pressureEnergyForce_weakGradient_test hpt
    (hDt.mono_measure (Measure.restrict_mono_set volume hsub))
    (hwt.mono (isOpen_vec3Ball _ _) hsub) φ

end FluidSingularSets
