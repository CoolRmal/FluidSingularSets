-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.CombinedWindowDecay
public import FluidSingularSets.ActualEnergyControl

/-!
# Symmetric cubic charge decay

The real velocity-pressure window estimate is identified with the actual symmetric
charge. Every required integrability statement comes from the suitable solution.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Fubini for a genuinely integrable function on a spatial and temporal rectangle. -/
theorem integral_spatialTimeRectangle_eq
    {U : Set Vec3} {J : Set ℝ} {f : ParabolicPoint → ℝ}
    (hf : IntegrableOn f (U ×ˢ J : Set ParabolicPoint) volume) :
    (∫ a in (U ×ˢ J : Set ParabolicPoint), f a) = ∫ s in J, ∫ x in U, f (x, s) := by
  have hprod : Integrable f ((volume.restrict U).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm _ hprod

/-- Integrability gives the genuine symmetric activity its ordinary real time-slice
representation. The hypotheses are finite-function data, with no decay estimate. -/
theorem rawSymmetricL3Activity_eq_timeIntegrals
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ}
    (hu : IntegrableOn (fun a ↦ vec3EuclideanNorm (u a) ^ (3 : ℕ))
      (rawSymmetricL3Cylinder z r) volume)
    (hp : IntegrableOn (fun a ↦ |p a| ^ (3 / 2 : ℝ))
      (rawSymmetricL3Cylinder z r) volume) :
    rawSymmetricL3Activity u p z r = r⁻¹ ^ 2 *
      ((∫ s in Ioo (z.2 - r ^ 2) (z.2 + r ^ 2), ∫ x in vec3Ball z.1 r,
        vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) +
        ∫ s in Ioo (z.2 - r ^ 2) (z.2 + r ^ 2), ∫ x in vec3Ball z.1 r,
          |p (x, s)| ^ (3 / 2 : ℝ)) := by
  have hpos (a : ParabolicPoint) :
      0 ≤ vec3EuclideanNorm (u a) ^ (3 : ℕ) + |p a| ^ (3 / 2 : ℝ) :=
    add_nonneg (pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
      (Real.rpow_nonneg (abs_nonneg _) _)
  have hmass : ENNReal.ofReal (∫ a in rawSymmetricL3Cylinder z r,
      vec3EuclideanNorm (u a) ^ (3 : ℕ) + |p a| ^ (3 / 2 : ℝ)) =
      ∫⁻ a in rawSymmetricL3Cylinder z r,
        ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
          ENNReal.ofReal |p a| ^ (3 / 2 : ℝ) := by
    have hsum : IntegrableOn
        (fun a ↦ vec3EuclideanNorm (u a) ^ (3 : ℕ) + |p a| ^ (3 / 2 : ℝ))
        (rawSymmetricL3Cylinder z r) volume := hu.add hp
    apply (ofReal_integral_eq_lintegral_ofReal hsum (Eventually.of_forall hpos)).trans
    apply lintegral_congr
    intro a
    rw [ENNReal.ofReal_add (pow_nonneg (vec3EuclideanNorm_nonneg _) 3) (by positivity),
      ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    norm_num only [ENNReal.rpow_ofNat]
  unfold rawSymmetricL3Activity
  rw [← hmass, ENNReal.toReal_ofReal (integral_nonneg hpos), integral_add hu hp]
  congr 1
  exact congrArg₂ (· + ·) (integral_spatialTimeRectangle_eq hu)
    (integral_spatialTimeRectangle_eq hp)

/-- A nonnegative integrable rectangle integral is controlled by a finite
dominating mass on every containing set. -/
theorem nonnegativeRectangleIntegral_le_lintegral
    {U : Set Vec3} {J : Set ℝ} {E : Set ParabolicPoint}
    {f : ParabolicPoint → ℝ} {g : ParabolicPoint → ℝ≥0∞}
    (hf : IntegrableOn f (U ×ˢ J : Set ParabolicPoint) volume) (hpos : ∀ a, 0 ≤ f a)
    (hpoint : ∀ a, ENNReal.ofReal (f a) ≤ g a) (hsub : U ×ˢ J ⊆ E)
    (hfinite : (∫⁻ a in E, g a) ≠ ⊤) :
    (∫ s in J, ∫ x in U, f (x, s)) ≤ (∫⁻ a in E, g a).toReal := by
  have hbound : ENNReal.ofReal (∫ a in (U ×ˢ J : Set ParabolicPoint), f a) ≤
      ∫⁻ a in E, g a := by
    calc
      _ = ∫⁻ a in U ×ˢ J, ENNReal.ofReal (f a) :=
        ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hpos)
      _ ≤ ∫⁻ a in U ×ˢ J, g a := lintegral_mono hpoint
      _ ≤ _ := lintegral_mono_set hsub
  have hnonnegative : 0 ≤ (∫ a in U ×ˢ J, f a) :=
    integral_nonneg (fun a : Vec3 × ℝ ↦ hpos a)
  have hreal := ENNReal.toReal_mono hfinite hbound
  have hint : (∫ a in U ×ˢ J, f a) ≤ (∫⁻ a in E, g a).toReal := by
    simpa only [ENNReal.toReal_ofReal hnonnegative] using hreal
  exact (integral_spatialTimeRectangle_eq hf) ▸ hint

/-- Any contained backward cylinder's actual real cubic and pressure masses
are controlled by the outer symmetric charge. -/
theorem suitableCylinderTimeMass_le_symmetricCharge
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z ζ : ParabolicPoint} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ spaceTimeSet Ω I)
    (hsub : parabolicCylinder ζ.1 ζ.2 ρ ⊆ rawSymmetricL3Cylinder z r) :
    (∫ s in Ioc (ζ.2 - ρ ^ 2) ζ.2, ∫ x in vec3Ball ζ.1 ρ,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) +
      (∫ s in Ioc (ζ.2 - ρ ^ 2) ζ.2, ∫ x in vec3Ball ζ.1 ρ,
        |p (x, s)| ^ (3 / 2 : ℝ)) ≤ 2 * r ^ 2 * rawSymmetricL3Activity u p z r := by
  let g := fun a ↦ ENNReal.ofReal (vec3EuclideanNorm (u a)) ^ (3 : ℝ) +
    ENNReal.ofReal |p a| ^ (3 / 2 : ℝ)
  let M := ∫⁻ a in rawSymmetricL3Cylinder z r, g a
  have hfinite : M ≠ ⊤ := (raw_symmetric_velocity_pressure_integral_lt_top hsol hr hdom).ne
  have hbackdom := (closure_mono hsub).trans hdom
  have hu := tsai_integrable_velocity_cube_on_cylinder hsol hρ hbackdom
  have hp := lin34_integrableOn_pressure_pow_cylinder hsol hρ hbackdom
  have hV : (∫ s in Ioc (ζ.2 - ρ ^ 2) ζ.2, ∫ x in vec3Ball ζ.1 ρ,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) ≤ M.toReal := by
    apply nonnegativeRectangleIntegral_le_lintegral hu
      (fun _ ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3) _ hsub hfinite
    intro a
    dsimp [g]
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
    norm_num only [ENNReal.rpow_ofNat]
    exact le_add_of_nonneg_right bot_le
  have hP : (∫ s in Ioc (ζ.2 - ρ ^ 2) ζ.2, ∫ x in vec3Ball ζ.1 ρ,
      |p (x, s)| ^ (3 / 2 : ℝ)) ≤ M.toReal := by
    apply nonnegativeRectangleIntegral_le_lintegral hp (fun _ ↦ by positivity) _ hsub hfinite
    intro a
    dsimp [g]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    exact le_add_of_nonneg_left bot_le
  have hmass : M.toReal = r ^ 2 * rawSymmetricL3Activity u p z r := by
    unfold rawSymmetricL3Activity
    dsimp [M, g]
    field_simp
  calc
    _ ≤ 2 * M.toReal := by linarith only [hV, hP]
    _ = _ := by rw [hmass]; ring

/-- The genuine combined charge decays on symmetric cylinders, with the actual
mixed-gradient source at one fixed inner scale and a universal linear mean term. -/
theorem suitableSymmetricChargeDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r / 2048)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ spaceTimeSet Ω I) :
    rawSymmetricL3Activity u p z s ≤
      2 * combinedWindowDecayConstant * 1024 ^ (3 : ℕ) * (s / r) *
        rawSymmetricL3Activity u p z r +
      combinedWindowDecayConstant * s⁻¹ ^ 2 *
        mixedOscillationSource u Du (energyShiftedTop z r) (r / 1024) := by
  let ζ := energyShiftedTop z r
  let ρ := r / 1024
  let J := Ioo (z.2 - s ^ 2) (z.2 + s ^ 2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hhalf : s ≤ ρ / 2 := by dsimp [ρ]; linarith only [hsr]
  have hsρ : s ≤ ρ := by linarith only [hhalf, hρ]
  have hρouter : ρ ≤ r / 2 := by dsimp [ρ]; linarith only [hr]
  have hsubmean : parabolicCylinder ζ.1 ζ.2 ρ ⊆ rawSymmetricL3Cylinder z r :=
    (parabolicCylinder_mono hρ.le hρouter).trans (energyShiftedOuter_subset_symmetric z hr)
  have hmeanDom := (closure_mono hsubmean).trans hdom
  have hfour : 4 * ρ ≤ r / 2 := by dsimp [ρ]; linarith only [hr]
  have hsourceDom : closure (parabolicCylinder ζ.1 ζ.2 (4 * ρ)) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity) hfour)).trans
      ((energyShiftedOuter_closure_subset_symmetric z hr).trans hdom)
  have hhalfR : (r / 512) / 2 = ρ := by dsimp [ρ]; ring
  have hJ : J ⊆ Ioc (ζ.2 - ρ ^ 2) ζ.2 := by
    have htime := symmetricTimeWindow_subset_shiftedMeanWindow
      (t := z.2) (by positivity : 0 < r / 512) hs
      (by linarith only [hsr] : s ≤ (r / 512) / 4)
    simpa only [J, ζ, energyShiftedTop, hhalfR] using htime
  have hinner : rawSymmetricL3Cylinder z s ⊆ parabolicCylinder ζ.1 ζ.2 ρ := by
    rintro a ⟨hx, hlow, hhigh⟩
    exact ⟨(vec3Ball_mono hsρ) hx, hJ ⟨hlow, hhigh⟩⟩
  have hu := (tsai_integrable_velocity_cube_on_cylinder hsol hρ hmeanDom).mono_set hinner
  have hp := (lin34_integrableOn_pressure_pow_cylinder hsol hρ hmeanDom).mono_set hinner
  have hrepr := rawSymmetricL3Activity_eq_timeIntegrals hu hp
  have hwindow := suitableCombinedTimeWindowDecay hsol hρ hs hhalf hsourceDom hJ
  have hlarge := suitableCylinderTimeMass_le_symmetricCharge hsol hr hρ hdom hsubmean
  rw [hrepr]
  apply hwindow.trans
  calc
    _ ≤ combinedWindowDecayConstant *
        ((s / ρ) * ρ⁻¹ ^ 2 * (2 * r ^ 2 * rawSymmetricL3Activity u p z r) +
          s⁻¹ ^ 2 * mixedOscillationSource u Du ζ ρ) := by
      apply mul_le_mul_of_nonneg_left _ combinedWindowDecayConstant_pos.le
      exact add_le_add (mul_le_mul_of_nonneg_left hlarge
        (mul_nonneg (div_nonneg hs.le hρ.le) (sq_nonneg _))) le_rfl
    _ = _ := by
      dsimp [ρ, ζ]
      field_simp

end FluidSingularSets
