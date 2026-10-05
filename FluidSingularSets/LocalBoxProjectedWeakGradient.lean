-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxProjectedLocalEnergy
public import FluidSingularSets.SuitableProjectedWeakGradient

/-!
# Original-interval spatial gradient of the projected velocity

The continuous harmonic correction and its canonical Hessian are the gradient
and Hessian of the same genuine pressure representative at every time. The
actual spatial weak-gradient, divergence, and finite-energy conclusions retain
the original local-box interval and the actual chosen force primitive. These
compact-interior lemmas make no outer-radius absorption claim.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance localBoxProjectedWeakForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance localBoxProjectedWeakForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual harmonic potential of the recovered force primitive, with the physical sign. -/
def localBoxProjectedHarmonicPotential
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c t : ℝ) : Vec3 → ℝ :=
  harmonicSpatialPressureRepresentative
    (-averagedTimePrimitive (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u D p) a b c t)

/-- An ambient representative of the actual compact-interior harmonic correction. -/
def localBoxProjectedHarmonicGradientAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Vec3 :=
  classicalGradient (localBoxProjectedHarmonicPotential u D p a b c z.2) z.1

/-- Its literal ambient Hessian in the original component/derivative index order. -/
def localBoxProjectedHarmonicDerivativeAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i j ↦ mixedSecond (localBoxProjectedHarmonicPotential u D p a b c z.2) j i z.1

/-- The actual projected velocity represented on ambient spatial coordinates. -/
def localBoxProjectedVelocityAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Vec3 :=
  u z + localBoxProjectedHarmonicGradientAmbient u D p a b c z

/-- The actual proposed gradient is the original gradient plus the true harmonic Hessian. -/
def localBoxProjectedVelocityDerivativeAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  D z + localBoxProjectedHarmonicDerivativeAmbient u D p a b c z

variable (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
  (p : ParabolicPoint → ℝ) (a b c : ℝ)

/-- The ambient gradient equals the frozen actual continuous time representative everywhere. -/
theorem localBoxProjectedHarmonicGradientAmbient_eq_compact
    (x : unitBallPressureCompactInterior) (t : ℝ) :
    localBoxProjectedHarmonicGradientAmbient u D p a b c (x.1, t) =
      localBoxProjectedHarmonicGradient u D p a b c (x, t) := by
  change unitBallHarmonicForceGradientExtended
      (-averagedTimePrimitive (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u D p) a b c t) x =
    (-unitBallHarmonicForceGradientExtended
      (averagedTimePrimitive (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u D p) a b c t)) x
  rw [map_neg]

/-- The ambient Hessian equals the frozen actual spatial correction derivative everywhere. -/
theorem localBoxProjectedHarmonicDerivativeAmbient_eq_compact
    (x : unitBallPressureCompactInterior) (t : ℝ) (i j : Fin 3) :
    localBoxProjectedHarmonicDerivativeAmbient u D p a b c (x.1, t) i j =
      localBoxProjectedHarmonicDerivative u D p a b c (x, t) i j := rfl

/-- The actual recovered potential has genuine C² regularity on the quarter ball at every time. -/
theorem localBoxProjectedHarmonicPotential_contDiff (t : ℝ) :
    ContDiffOn ℝ (2 : ℕ∞) (localBoxProjectedHarmonicPotential u D p a b c t)
      (vec3Ball 0 (1 / 4)) :=
  unitBallHarmonicForcePressureRepresentative_contDiff _

/-- The frozen correction's actual Hessian is its true spatial weak gradient at every time. -/
theorem localBoxProjectedHarmonicGradientAmbient_hasWeakGradient
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (t : ℝ) (i : Fin 3) :
    HasWeakGradientOn B
      (fun x ↦ localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t) i)
      (fun x ↦ localBoxProjectedHarmonicDerivativeAmbient u D p a b c (x, t) i) := by
  have hquarter : B ⊆ vec3Ball 0 (1 / 4) := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  exact (hasWeakGradientOn_gradient_of_contDiffOn_two (isOpen_vec3Ball _ _)
    (localBoxProjectedHarmonicPotential_contDiff u D p a b c t) i).mono hB hquarter

/-- Every actual harmonic correction slice belongs to spatial L² on the compact interior. -/
theorem localBoxProjectedHarmonicGradientAmbient_memLp_two (t : ℝ) :
    MemLp (fun x ↦ localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t)) 2
      (volume.restrict unitBallPressureCompactInterior) := by
  apply (memLp_harmonicInterior_ambient_iff _ _).mpr
  have heq : (fun x : unitBallPressureCompactInterior ↦
      localBoxProjectedHarmonicGradientAmbient u D p a b c (x.1, t)) =
      localBoxHarmonicTimePrimitive u D p a b c t := by
    funext x
    exact localBoxProjectedHarmonicGradientAmbient_eq_compact u D p a b c x t
  rw [heq]
  exact (localBoxHarmonicTimePrimitive u D p a b c t).memLp harmonicInteriorMeasure ℝ

/-- Every actual harmonic Hessian slice belongs to spatial L² on the compact interior. -/
theorem localBoxProjectedHarmonicDerivativeAmbient_memLp_two (t : ℝ) :
    MemLp (fun x ↦ localBoxProjectedHarmonicDerivativeAmbient u D p a b c (x, t)) 2
      (volume.restrict unitBallPressureCompactInterior) := by
  apply memLp_pi_iff.mpr
  intro i
  apply memLp_pi_iff.mpr
  intro j
  apply (memLp_harmonicInterior_ambient_iff _ _).mpr
  have hm := (harmonicCompactHessianOperator
    (-averagedTimePrimitive (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u D p) a b c t)).memLp
      (p := 2) harmonicInteriorMeasure ℝ
  exact hm.eval_piLp (j, i)

/-- The actual harmonic correction is weakly divergence-free on every inner open set. -/
theorem localBoxProjectedHarmonicGradientAmbient_divergenceFree
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (t : ℝ) (ψ : WeakTestFunction B) :
    (∫ x in B, ∑ i : Fin 3,
      localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) = 0 := by
  have hquarter : B ⊆ vec3Ball 0 (1 / 4) := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  exact classicalGradient_weakly_divergenceFree_of_weaklyHarmonic hB
    ((localBoxProjectedHarmonicPotential_contDiff u D p a b c t).mono hquarter
      |>.of_le (by norm_num))
    (localWeaklyHarmonicOn_restrict hquarter
      (unitBallHarmonicForcePressureRepresentative_weaklyHarmonic _))
    ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset

/-- Actual suitability supplies the projected velocity's genuine L² and weak-gradient slices. -/
theorem localBoxProjectedVelocityAmbient_weak_gradient_slices_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ localBoxProjectedVelocityAmbient u D p a b c (x, t)) 2
        (volume.restrict B) ∧
      MemLp (fun x ↦ localBoxProjectedVelocityDerivativeAmbient u D p a b c (x, t)) 2
        (volume.restrict B) ∧
      ∀ i : Fin 3, HasWeakGradientOn B
        (fun x ↦ localBoxProjectedVelocityAmbient u D p a b c (x, t) i)
        (fun x ↦ localBoxProjectedVelocityDerivativeAmbient u D p a b c (x, t) i) := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  have hu := ht.1.mono_measure (Measure.restrict_mono_set volume hB1)
  have hD := ht.2.mono_measure (Measure.restrict_mono_set volume hB1)
  have hH := (localBoxProjectedHarmonicGradientAmbient_memLp_two u D p a b c t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  have hDH := (localBoxProjectedHarmonicDerivativeAmbient_memLp_two u D p a b c t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  refine ⟨hu.add hH, hD.add hDH, ?_⟩
  intro i
  exact hasWeakGradientOn_add_of_memLp_two (hu.eval i) (hH.eval i)
    (hD.eval i) (hDH.eval i) ((hwt i).mono hB hB1)
    (localBoxProjectedHarmonicGradientAmbient_hasWeakGradient u D p a b c hB hBK t i)

/-- The true projected velocity remains weakly divergence-free on one common full time set. -/
theorem localBoxProjectedVelocityAmbient_divergenceFree_slices_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ ψ : WeakTestFunction B,
      (∫ x in B, ∑ i : Fin 3, localBoxProjectedVelocityAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) = 0 := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hboxB : localBox Ω I B (Ioo a b) :=
    ⟨hB, hbox.2.1.of_isClosed_subset isClosed_closure (closure_mono hB1),
      (closure_mono hB1).trans hbox.2.2.1, hbox.2.2.2⟩
  filter_upwards [suitable_divergenceFree_slices_ae_localBox hsol hboxB,
    slice_memLp_ae_of_sws hsol hboxB] with t hdiv ht ψ
  have hH := (localBoxProjectedHarmonicGradientAmbient_memLp_two u D p a b c t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  have hψd (i : Fin 3) : MemLp (spatialDeriv ψ.toFun i) 2 (volume.restrict B) :=
    ((stokesWeakTestDerivative ψ i).contDiff.continuous.memLp_of_hasCompactSupport
      (stokesWeakTestDerivative ψ i).hasCompactSupport).restrict B
  have hu (i : Fin 3) : Integrable (fun x ↦ u (x, t) i * spatialDeriv ψ.toFun i x)
      (volume.restrict B) := (ht.1.eval i).integrable_mul (hψd i)
  have hh (i : Fin 3) : Integrable (fun x ↦
      localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) (volume.restrict B) :=
    (hH.eval i).integrable_mul (hψd i)
  have hus : Integrable (fun x ↦ ∑ i : Fin 3, u (x, t) i * spatialDeriv ψ.toFun i x)
      (volume.restrict B) := integrable_finsetSum _ (fun i _ ↦ hu i)
  have hhs : Integrable (fun x ↦ ∑ i : Fin 3,
      localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) (volume.restrict B) :=
    integrable_finsetSum _ (fun i _ ↦ hh i)
  simp only [localBoxProjectedVelocityAmbient, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [integral_add hus hhs, hdiv ψ,
    localBoxProjectedHarmonicGradientAmbient_divergenceFree u D p a b c hB hBK t ψ]
  simp

/-- Suitability supplies the genuine ambient joint L² harmonic correction and Hessian. -/
theorem localBoxProjectedHarmonicAmbient_joint_memLp_two
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hct : c ∈ Ioo a b) :
    MemLp (localBoxProjectedHarmonicGradientAmbient u D p a b c) 2
      (volume.restrict (unitBallPressureCompactInterior ×ˢ Ioo a b)) ∧
    MemLp (localBoxProjectedHarmonicDerivativeAmbient u D p a b c) 2
      (volume.restrict (unitBallPressureCompactInterior ×ˢ Ioo a b)) := by
  let J := Ioo a b
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    simp only [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top)
  have hd := localBox_harmonicInterior_correction_memLp_top hsol hbox hab hct
  constructor
  · apply (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr
    have heq : (fun z : unitBallPressureCompactInterior × ℝ ↦
        localBoxProjectedHarmonicGradientAmbient u D p a b c (z.1.1, z.2)) =
        localBoxProjectedHarmonicGradient u D p a b c := by
      funext z
      exact localBoxProjectedHarmonicGradientAmbient_eq_compact u D p a b c z.1 z.2
    rw [heq]
    exact hd.1.mono_exponent le_top
  · apply memLp_pi_iff.mpr
    intro i
    apply memLp_pi_iff.mpr
    intro j
    apply (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr
    exact (hd.2 i j).mono_exponent le_top

/-- The actual projected velocity and its actual gradient have genuine joint finite energy. -/
theorem localBoxProjectedVelocityAmbient_joint_memLp_two
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hct : c ∈ Ioo a b)
    {B : Set Vec3} (hBK : B ⊆ unitBallPressureCompactInterior) :
    MemLp (localBoxProjectedVelocityAmbient u D p a b c) 2
      (volume.restrict (B ×ˢ Ioo a b)) ∧
    MemLp (localBoxProjectedVelocityDerivativeAmbient u D p a b c) 2
      (volume.restrict (B ×ˢ Ioo a b)) := by
  let J := Ioo a b
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    simp only [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top)
  have hu := localBox_harmonicInterior_memLp hsol hbox hab
  have hH := localBoxProjectedHarmonicAmbient_joint_memLp_two u D p a b c hsol hbox hab hct
  have hu2 : MemLp u 2 (volume.restrict (unitBallPressureCompactInterior ×ˢ J)) :=
    (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr
      (hu.1.mono_exponent (by norm_num))
  have hD2 : MemLp D 2 (volume.restrict (unitBallPressureCompactInterior ×ˢ J)) :=
    (memLp_harmonicInterior_product_ambient_iff _ _ _).mpr hu.2.1
  have hsub : B ×ˢ J ⊆ unitBallPressureCompactInterior ×ˢ J := prod_mono hBK le_rfl
  exact ⟨(hu2.add hH.1).mono_measure (Measure.restrict_mono_set volume hsub),
    (hD2.add hH.2).mono_measure (Measure.restrict_mono_set volume hsub)⟩

/-- The genuine projected field satisfies the weighted mixed Sobolev estimate from suitability. -/
theorem localBoxProjectedVelocityAmbient_integrated_cutoff_sobolev
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hct : c ∈ Ioo a b)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in Ioo a b,
      eLpNorm (fun x ↦ φ x ^ 3 • localBoxProjectedVelocityAmbient u D p a b c (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
          ‖φ z.1 ^ 3 • localBoxProjectedVelocityDerivativeAmbient u D p a b c z‖ₑ ^
            (2 : ℝ)) +
        ENNReal.ofReal (3 * L + 32) ^ 2 *
          ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
            ‖φ z.1 ^ 2 • localBoxProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ)) := by
  have hunit : tsupport φ ⊆ euclideanBall 0 1 := by
    rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)]
    exact fun x hx ↦ vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK (hs hx)))
  have hj := localBoxProjectedVelocityAmbient_joint_memLp_two u D p a b c hsol hbox hab hct hBK
  exact integrated_cutoff_cube_vector_sobolev hB hj.1.aestronglyMeasurable
    hj.2.aestronglyMeasurable
    (localBoxProjectedVelocityAmbient_weak_gradient_slices_ae u D p a b c hsol hbox hB hBK)
    hφ hc hs hunit hb hL hgrad

set_option maxHeartbeats 3000000 in
/-- The actual projected cubed-cutoff mixed moment is finite without extra energy premises. -/
theorem localBoxProjectedVelocityAmbient_integrated_cutoff_sobolev_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hct : c ∈ Ioo a b)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in Ioo a b,
      eLpNorm (fun x ↦ φ x ^ 3 • localBoxProjectedVelocityAmbient u D p a b c (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) < ∞ := by
  have hj := localBoxProjectedVelocityAmbient_joint_memLp_two u D p a b c hsol hbox hab hct hBK
  have hVE : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ‖localBoxProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ)) < ∞ := by
    simpa only [ENNReal.toReal_ofNat] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
        (by norm_num) (by norm_num) hj.1.eLpNorm_lt_top)
  have hDE : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ‖localBoxProjectedVelocityDerivativeAmbient u D p a b c z‖ₑ ^ (2 : ℝ)) < ∞ := by
    simpa only [ENNReal.toReal_ofNat] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
        (by norm_num) (by norm_num) hj.2.eLpNorm_lt_top)
  have hDw : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ‖φ z.1 ^ 3 • localBoxProjectedVelocityDerivativeAmbient u D p a b c z‖ₑ ^
        (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun z ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (localBoxProjectedVelocityDerivativeAmbient u D p a b c z)
        (hb z.1).1 (hb z.1).2 3) (by norm_num))).trans_lt hDE
  have hVw : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ‖φ z.1 ^ 2 • localBoxProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun z ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (localBoxProjectedVelocityAmbient u D p a b c z)
        (hb z.1).1 (hb z.1).2 2) (by norm_num))).trans_lt hVE
  apply (localBoxProjectedVelocityAmbient_integrated_cutoff_sobolev u D p a b c hsol hbox hab hct
    hB hBK hφ hc hs hb hL hgrad).trans_lt
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr cutoff_mixed_sobolev_coefficient_ne_top)
    (ENNReal.add_lt_top.mpr ⟨hDw, ENNReal.mul_lt_top (by finiteness) hVw⟩)

end FluidSingularSets
