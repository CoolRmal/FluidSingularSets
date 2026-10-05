-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesForceCurves
public import FluidSingularSets.StokesMomentumTime
public import FluidSingularSets.ActualPressureCurve

/-!
# Genuine suitable momentum and projected pressure evolution

The actual velocity, convection, viscosity, and pressure energy forces have
the literal compact-test pairings in suitable momentum. Their genuine time
integrability therefore yields the full energy-dual weak time derivative.
Applying the constructed ball Stokes pressure then gives the actual harmonic
pressure correction's evolution, with the physical pressure signs.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance projectedPressureTimeForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance projectedPressureTimeForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

private theorem projectedPressureTime_ball_eq {r : ℝ} (hr : 0 < r) :
    euclideanBall (0 : Vec3) r = vec3Ball 0 r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

private theorem projectedPressureTime_test_memLp {U : Set Vec3}
    (φ : WeakTestFunction U) (P : ℝ≥0∞) : MemLp φ.toFun P (volume.restrict U) :=
  (φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).mono_measure
    Measure.restrict_le_self

private theorem projectedPressureTime_deriv_memLp {U : Set Vec3}
    (φ : WeakTestFunction U) (i : Fin 3) (P : ℝ≥0∞) :
    MemLp (φ.partialDeriv i) P (volume.restrict U) := by
  have hcont : Continuous (φ.partialDeriv i) :=
    (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : HasCompactSupport (φ.partialDeriv i) :=
    φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hcont.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self

/-- The true suitable momentum source, including the original pressure gradient. -/
def unitBallMomentumForceCurve (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (t : ℝ) :
    StokesEnergyForce (vec3Ball 0 1) :=
  unitBallConvectiveForceCurve u t + unitBallViscousForceCurve D t - pressureEnergyForce p 0 1 t

/-- The actual harmonic pressure correction, with the conventional negative projection. -/
def unitBallHarmonicPressureCurve (u : ParabolicPoint → Vec3) (t : ℝ) : unitBallMeanZeroL2 :=
  -unitBallStokesPressure (unitBallVelocityForceCurve u t)

/-- Genuine velocity data give the exact weighted-mean source pairing. -/
theorem unitBallVelocityForceCurve_weightedMean_pair (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun x ↦ u (x, t)) 2 (volume.restrict (vec3Ball 0 1)))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    unitBallVelocityForceCurve u t (stokesEnergyTest φ) =
      ∑ i : Fin 3, weightedVelocityMean (vec3Ball 0 1) (φ i).toFun u i t := by
  rw [(unitBallVelocityForceCurve_compactTest u t hu φ).2]
  exact integral_finsetSum Finset.univ (fun i _ ↦
    (hu.eval i).integrable_mul (projectedPressureTime_test_memLp (φ i) 2))

/-- Actual good-slice data supply the literal suitable momentum-flux pairing. -/
theorem unitBallMomentumForceCurve_weightedFlux_pair
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t : ℝ)
    (hu : MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1)))
    (hD : MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1)))
    (hp : MemLp (centeredPressureSlice p 0 1 t) 2 (volume.restrict (vec3Ball 0 1)))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    unitBallMomentumForceCurve u D p t (stokesEnergyTest φ) =
      ∑ i : Fin 3, ∫ x in vec3Ball 0 1, weightedMomentumFlux (φ i).toFun u D p i (x, t) := by
  let μ := (volume : Measure Vec3).restrict (vec3Ball 0 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  let : ENNReal.HolderTriple 4 4 2 := by
    have h : Real.HolderTriple 4 4 2 := by rw [Real.holderTriple_iff]; norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  have hconv (i j : Fin 3) : Integrable
      (fun x ↦ u (x, t) i * u (x, t) j * (φ i).partialDeriv j x) μ := by
    have hij : MemLp (fun x ↦ u (x, t) i * u (x, t) j) 2 μ :=
      (hu.eval i).mul (hu.eval j)
    exact hij.integrable_mul (projectedPressureTime_deriv_memLp (φ i) j 2)
  have hvisc (i j : Fin 3) : Integrable
      (fun x ↦ D (x, t) i j * (φ i).partialDeriv j x) μ :=
    ((hD.eval i).eval j).integrable_mul (projectedPressureTime_deriv_memLp (φ i) j 2)
  let c := average μ (fun x ↦ p (x, t))
  have hpraw : MemLp (fun x ↦ p (x, t)) 2 μ := by
    have hc : MemLp (fun _ : Vec3 ↦ c) 2 μ := memLp_const c
    exact (memLp_congr_ae (ae_of_all _ (fun x ↦ by
      change centeredPressureSlice p 0 1 t x + c = p (x, t)
      simp only [centeredPressureSlice, c, μ, sub_add_cancel]))).mp (hp.add hc)
  have hpress (i : Fin 3) : Integrable (fun x ↦ p (x, t) * (φ i).partialDeriv i x) μ :=
    hpraw.integrable_mul (projectedPressureTime_deriv_memLp (φ i) i 2)
  have hconvSum (i : Fin 3) : Integrable
      (fun x ↦ ∑ j : Fin 3, u (x, t) i * u (x, t) j * (φ i).partialDeriv j x) μ :=
    integrable_finsetSum Finset.univ (fun j _ ↦ hconv i j)
  have hviscSum (i : Fin 3) : Integrable
      (fun x ↦ ∑ j : Fin 3, D (x, t) i j * (φ i).partialDeriv j x) μ :=
    integrable_finsetSum Finset.univ (fun j _ ↦ hvisc i j)
  have hC : unitBallConvectiveForceCurve u t (stokesEnergyTest φ) =
      ∑ i : Fin 3, ∫ x in vec3Ball 0 1,
        ∑ j : Fin 3, u (x, t) i * u (x, t) j * (φ i).partialDeriv j x := by
    rw [(unitBallConvectiveForceCurve_compactTest u t hu φ).2]
    have heq (x : Vec3) : (∑ ij : Fin 3 × Fin 3,
        (u (x, t) ij.1 * u (x, t) ij.2) * (φ ij.2).partialDeriv ij.1 x) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          u (x, t) i * u (x, t) j * (φ i).partialDeriv j x := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm (u (x, t) j) (u (x, t) i)]
    simp_rw [heq]
    exact integral_finsetSum Finset.univ (fun i _ ↦ hconvSum i)
  have hV : unitBallViscousForceCurve D t (stokesEnergyTest φ) =
      -(∑ i : Fin 3, ∫ x in vec3Ball 0 1,
        ∑ j : Fin 3, D (x, t) i j * (φ i).partialDeriv j x) := by
    rw [(unitBallViscousForceCurve_compactTest D t hD φ).2]
    have heq (x : Vec3) : (∑ ij : Fin 3 × Fin 3,
        D (x, t) ij.2 ij.1 * (φ ij.2).partialDeriv ij.1 x) =
        ∑ i : Fin 3, ∑ j : Fin 3, D (x, t) i j * (φ i).partialDeriv j x := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [heq]
    congr 1
    exact integral_finsetSum Finset.univ (fun i _ ↦ hviscSum i)
  change unitBallConvectiveForceCurve u t (stokesEnergyTest φ) +
    unitBallViscousForceCurve D t (stokesEnergyTest φ) -
      pressureEnergyForce p 0 1 t (stokesEnergyTest φ) = _
  rw [hC, hV]
  rw [pressureEnergyForce_pressure_test hp φ]
  have hflux (i : Fin 3) : (∫ x in vec3Ball 0 1,
      weightedMomentumFlux (φ i).toFun u D p i (x, t)) =
      (∫ x in vec3Ball 0 1, ∑ j : Fin 3,
        u (x, t) i * u (x, t) j * (φ i).partialDeriv j x) -
      (∫ x in vec3Ball 0 1, ∑ j : Fin 3, D (x, t) i j * (φ i).partialDeriv j x) +
      (∫ x in vec3Ball 0 1, p (x, t) * (φ i).partialDeriv i x) := by
    change (∫ x in vec3Ball 0 1,
      ((∑ j : Fin 3, u (x, t) i * u (x, t) j * (φ i).partialDeriv j x) -
        (∑ j : Fin 3, D (x, t) i j * (φ i).partialDeriv j x)) +
          p (x, t) * (φ i).partialDeriv i x) = _
    exact (integral_add ((hconvSum i).sub (hviscSum i)) (hpress i)).trans
      (congrArg (fun z : ℝ ↦ z + ∫ x in vec3Ball 0 1, p (x, t) * (φ i).partialDeriv i x)
        (integral_sub (hconvSum i) (hviscSum i)))
  simp_rw [hflux]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

private theorem projectedPressureTime_localBoxes
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    localBox Ω I (euclideanBall 0 2) (Ioo (t₀ - 4) (t₀ + 4)) ∧
      localBox Ω I (vec3Ball 0 1) (Ioo (t₀ - 4) (t₀ + 4)) := by
  have hb := CKN.Core.Endgame.localBox_of_parabolic_ball
    (z₀ := ((0, t₀) : ParabolicPoint)) (by norm_num : (0 : ℝ) < 2)
    ((Metric.ball_subset_ball (by norm_num : (2 : ℝ) * 2 ≤ 8)).trans hdom)
  have hB : localBox Ω I (euclideanBall 0 2) (Ioo (t₀ - 4) (t₀ + 4)) := by
    simpa only [projectedPressureTime_ball_eq (by norm_num : (0 : ℝ) < 2),
      Prod.fst, Prod.snd, show (2 : ℝ) ^ 2 = 4 by norm_num] using hb
  have hsub : vec3Ball (0 : Vec3) 1 ⊆ euclideanBall 0 2 := by
    rw [projectedPressureTime_ball_eq (by norm_num : (0 : ℝ) < 2)]
    exact vec3Ball_mono (by norm_num)
  refine ⟨hB, (isOpen_vec3Ball 0 1), ?_, ?_, hB.2.2.2⟩
  · exact hB.2.1.of_isClosed_subset isClosed_closure (closure_mono hsub)
  · exact (closure_mono hsub).trans hB.2.2.1

/-- Genuine suitability and an interior native parabolic ball give both actual
velocity-force and full momentum-force Bochner integrability. -/
theorem suitable_unitBall_momentumForces_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    IntegrableOn (unitBallVelocityForceCurve u) (Ioo (t₀ - 4) (t₀ + 4)) volume ∧
      IntegrableOn (unitBallMomentumForceCurve u Du p) (Ioo (t₀ - 4) (t₀ + 4)) volume := by
  have hbox := (projectedPressureTime_localBoxes hdom).1
  obtain ⟨hF, hC, hV⟩ := suitable_energyForceCurves_integrable hsol hbox
  obtain ⟨_, _, _, hPF, _, _⟩ := exists_suitable_memLp_pressure_energy_force hsol
    ((0, t₀) : ParabolicPoint) (by norm_num : (0 : ℝ) < 1)
    (by simpa only [mul_one] using hdom)
  have hP : MemLp (pressureEnergyForce p 0 1) (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) := by
    simpa only [Prod.fst, Prod.snd, mul_one, show (2 : ℝ) ^ 2 = 4 by norm_num] using hPF
  let : IsFiniteMeasure (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact ⟨hF, (hC.add hV).sub (hP.integrable (by norm_num))⟩

/-- The actual suitable momentum equation gives the genuine complete energy-dual
weak time derivative, without an evolution or test-pairing hypothesis. -/
theorem suitable_unitBall_momentum_hasWeakTimeDerivativeOn
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    HasWeakTimeDerivativeOn (Ioo (t₀ - 4) (t₀ + 4)) (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u Du p) := by
  obtain ⟨hbox2, hbox1⟩ := projectedPressureTime_localBoxes hdom
  obtain ⟨hF, hG⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  apply suitable_energyDual_hasWeakTimeDerivativeOn_of_literal_pairings hsol hbox1 hF hG
  have hsub : vec3Ball (0 : Vec3) 1 ⊆ euclideanBall 0 2 := by
    rw [projectedPressureTime_ball_eq (by norm_num : (0 : ℝ) < 2)]
    exact vec3Ball_mono (by norm_num)
  obtain ⟨_, _, _, _, hp, _⟩ := exists_suitable_pressure_energy_dual hsol
    ((0, t₀) : ParabolicPoint) (by norm_num : (0 : ℝ) < 1)
    (by simpa only [mul_one] using hdom)
  have hpAE : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      MemLp (centeredPressureSlice p 0 1 t) 2 (volume.restrict (vec3Ball 0 1)) := by
    simpa only [Prod.fst, Prod.snd, mul_one, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp
  intro φ
  constructor
  · filter_upwards [slice_memLp_ae_of_sws hsol hbox2] with t ht
    exact unitBallVelocityForceCurve_weightedMean_pair u t
      (ht.1.mono_measure (Measure.restrict_mono hsub le_rfl)) φ
  · filter_upwards [suitable_unitBall_memLp_four_ae hsol hbox2,
      slice_memLp_ae_of_sws hsol hbox2, hpAE] with t hut hDt hpt
    rw [projectedPressureTime_ball_eq (by norm_num : (0 : ℝ) < 1)] at hut
    exact unitBallMomentumForceCurve_weightedFlux_pair u Du p t hut
      (hDt.2.mono_measure (Measure.restrict_mono hsub le_rfl)) hpt φ

/-- The genuine projected harmonic-pressure correction obeys the actual pressure
time equation with its literal centered, nonlinear, and viscous pressures. -/
theorem suitable_unitBall_harmonicPressure_hasWeakTimeDerivativeOn
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    HasWeakTimeDerivativeOn (Ioo (t₀ - 4) (t₀ + 4)) (unitBallHarmonicPressureCurve u)
      (fun t ↦ unitBallActualPressureCurve p t - unitBallConvectivePressureCurve u t -
        unitBallViscousPressureCurve Du t) := by
  obtain ⟨hF, hG⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  have h := suitable_unitBall_momentum_hasWeakTimeDerivativeOn hsol hdom
  have hG_eq : unitBallMomentumForceCurve u Du p =
      fun t ↦ unitBallConvectiveForceCurve u t + unitBallViscousForceCurve Du t -
        stokesL2PressureGradient (unitBallActualPressureCurve p t :
          Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := by
    funext t
    unfold unitBallMomentumForceCurve
    rw [pressureEnergyForce_eq_unitBallActualPressureCurve_gradient]
  rw [hG_eq] at h hG
  have hpi := weakTimeDerivative_projected_ball_pressure h hF hG
  change HasWeakTimeDerivativeOn (Ioo (t₀ - 4) (t₀ + 4))
    (fun t ↦ -unitBallStokesPressure (unitBallVelocityForceCurve u t))
    (fun t ↦ unitBallActualPressureCurve p t - unitBallConvectivePressureCurve u t -
      unitBallViscousPressureCurve Du t)
  simpa only [unitBallConvectivePressureCurve_eq_projection,
    unitBallViscousPressureCurve_eq_projection, unitBallStokesPressureL_apply] using hpi

end Suitable

end FluidSingularSets
