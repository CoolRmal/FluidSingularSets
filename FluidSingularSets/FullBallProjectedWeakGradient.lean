-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedSources
public import FluidSingularSets.LocalBoxProjectedWeakGradient

/-!
# Actual full-ball projected spatial gradients

The potential is the genuine full-ball pressure representative of the projected
negative force primitive. Its actual C² regularity supplies weak gradients and
weak divergence on every inner open spatial set. The original suitable data
then give genuine projected H¹ slices on every compact radius less than one.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance fullBallProjectedWeakForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallProjectedWeakForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual full-ball harmonic potential of the original-interval force primitive. -/
def fullBallProjectedHarmonicPotential
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c t : ℝ) : Vec3 → ℝ :=
  unitBallFullHarmonicForcePressureRepresentative
    (unitBallGradientFreeForceProjection (-localBoxForcePrimitive u D p a b c t))

/-- The actual ambient harmonic correction on the full ball. -/
def fullBallProjectedHarmonicGradientAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Vec3 :=
  classicalGradient (fullBallProjectedHarmonicPotential u D p a b c z.2) z.1

/-- Its genuine Hessian in velocity-component/derivative order. -/
def fullBallProjectedHarmonicDerivativeAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i j ↦ mixedSecond (fullBallProjectedHarmonicPotential u D p a b c z.2) j i z.1

/-- The actual corrected velocity on ambient spatial coordinates. -/
def fullBallProjectedVelocityAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Vec3 :=
  u z + fullBallProjectedHarmonicGradientAmbient u D p a b c z

/-- Its literal proposed weak gradient. -/
def fullBallProjectedVelocityDerivativeAmbient
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  D z + fullBallProjectedHarmonicDerivativeAmbient u D p a b c z

variable (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
  (p : ParabolicPoint → ℝ) (a b c : ℝ)

/-- The actual full-ball potential is genuinely C² on the whole open unit ball. -/
theorem fullBallProjectedHarmonicPotential_contDiff (t : ℝ) :
    ContDiffOn ℝ (2 : ℕ∞) (fullBallProjectedHarmonicPotential u D p a b c t)
      (vec3Ball 0 1) :=
  unitBallFullHarmonicForcePressureRepresentative_contDiff _

/-- The full-ball and previous actual potential agree on the quarter ball. -/
theorem fullBallProjectedHarmonicPotential_eqOn_quarter (t : ℝ) :
    EqOn (fullBallProjectedHarmonicPotential u D p a b c t)
      (localBoxProjectedHarmonicPotential u D p a b c t) (vec3Ball 0 (1 / 4)) :=
  unitBallFullHarmonicForcePressureRepresentative_eqOn_quarter _

/-- The full-ball correction agrees with the verified compact-interior correction. -/
theorem fullBallProjectedHarmonicGradientAmbient_eqOn_quarter (t : ℝ) :
    EqOn (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t))
      (fun x ↦ localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t))
      (vec3Ball 0 (1 / 4)) :=
  classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball _ _)
    (fullBallProjectedHarmonicPotential_eqOn_quarter u D p a b c t)

/-- Actual local equality also identifies the two genuine Hessians. -/
theorem fullBallProjectedHarmonicDerivativeAmbient_eqOn_quarter
    (t : ℝ) (i j : Fin 3) :
    EqOn (fun x ↦ fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x, t) i j)
      (fun x ↦ localBoxProjectedHarmonicDerivativeAmbient u D p a b c (x, t) i j)
      (vec3Ball 0 (1 / 4)) :=
  mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball _ _)
    (fullBallProjectedHarmonicPotential_eqOn_quarter u D p a b c t) j i

/-- Actual C² regularity gives the true spatial weak gradient on every inner open set. -/
theorem fullBallProjectedHarmonicGradientAmbient_hasWeakGradient
    {B : Set Vec3} (hB : IsOpen B) (hB1 : B ⊆ vec3Ball 0 1)
    (t : ℝ) (i : Fin 3) :
    HasWeakGradientOn B
      (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t) i)
      (fun x ↦ fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x, t) i) :=
  (hasWeakGradientOn_gradient_of_contDiffOn_two (isOpen_vec3Ball _ _)
    (fullBallProjectedHarmonicPotential_contDiff u D p a b c t) i).mono hB hB1

/-- The actual harmonic correction is weakly divergence-free throughout the unit ball. -/
theorem fullBallProjectedHarmonicGradientAmbient_divergenceFree
    {B : Set Vec3} (hB : IsOpen B) (hB1 : B ⊆ vec3Ball 0 1)
    (t : ℝ) (ψ : WeakTestFunction B) :
    (∫ x in B, ∑ i : Fin 3,
      fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) = 0 :=
  classicalGradient_weakly_divergenceFree_of_weaklyHarmonic hB
    (((fullBallProjectedHarmonicPotential_contDiff u D p a b c t).mono hB1).of_le
      (by norm_num))
    (localWeaklyHarmonicOn_restrict hB1
      (unitBallFullHarmonicForcePressureRepresentative_weaklyHarmonic _))
    ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset

/-- The actual gradient is spatially continuous on the whole open unit ball. -/
theorem fullBallProjectedHarmonicGradientAmbient_continuousOn (t : ℝ) :
    ContinuousOn (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t))
      (vec3Ball 0 1) := by
  apply continuousOn_pi.mpr
  intro i
  have hH := fullBallProjectedHarmonicPotential_contDiff u D p a b c t
  have hd := hH.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball _ _) (by norm_num)
  exact hd.clm_apply (g := fun _ ↦ basisVec i) continuousOn_const

/-- The actual Hessian is spatially continuous on the whole open unit ball. -/
theorem fullBallProjectedHarmonicDerivativeAmbient_continuousOn (t : ℝ) :
    ContinuousOn (fun x ↦ fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x, t))
      (vec3Ball 0 1) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hp := contDiffOn_spatialDeriv_of_two (isOpen_vec3Ball _ _)
    (fullBallProjectedHarmonicPotential_contDiff u D p a b c t) i
  exact (hp.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball _ _) (by norm_num)).clm_apply
    (g := fun _ ↦ basisVec j) continuousOn_const

/-- Every actual correction slice has finite spatial energy on every compact inner radius. -/
theorem fullBallProjectedHarmonicGradientAmbient_memLp_two
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) (t : ℝ) :
    MemLp (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) 2
      (volume.restrict (fullBallCompactInterior ρ)) := by
  apply (memLp_fullBallInterior_ambient_iff ρ _ _).mpr
  let H : C(fullBallCompactInterior ρ, Vec3) :=
    ⟨fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x.1, t),
      continuousOn_iff_continuous_domRestrict.mp
        ((fullBallProjectedHarmonicGradientAmbient_continuousOn u D p a b c t).mono
          (fullBallCompactInterior_subset_unit hρ hρone))⟩
  exact H.memLp (fullBallInteriorMeasure ρ) ℝ

/-- Every actual Hessian slice has finite spatial energy on every compact inner radius. -/
theorem fullBallProjectedHarmonicDerivativeAmbient_memLp_two
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) (t : ℝ) :
    MemLp (fun x ↦ fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x, t)) 2
      (volume.restrict (fullBallCompactInterior ρ)) := by
  apply (memLp_fullBallInterior_ambient_iff ρ _ _).mpr
  let H : C(fullBallCompactInterior ρ, Fin 3 → Vec3) :=
    ⟨fun x ↦ fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x.1, t),
      continuousOn_iff_continuous_domRestrict.mp
        ((fullBallProjectedHarmonicDerivativeAmbient_continuousOn u D p a b c t).mono
          (fullBallCompactInterior_subset_unit hρ hρone))⟩
  exact H.memLp (fullBallInteriorMeasure ρ) ℝ

/-- Original suitable data yield the actual full-ball corrected H¹ slices. -/
theorem fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
    {Ω : Set Vec3} {I : Set ℝ} {q ρ : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 2
        (volume.restrict B) ∧
      MemLp (fun x ↦ fullBallProjectedVelocityDerivativeAmbient u D p a b c (x, t)) 2
        (volume.restrict B) ∧
      ∀ i : Fin 3, HasWeakGradientOn B
        (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t) i)
        (fun x ↦ fullBallProjectedVelocityDerivativeAmbient u D p a b c (x, t) i) := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  have hu := ht.1.mono_measure (Measure.restrict_mono_set volume hB1)
  have hD := ht.2.mono_measure (Measure.restrict_mono_set volume hB1)
  have hH := (fullBallProjectedHarmonicGradientAmbient_memLp_two u D p a b c
    hρ hρone t).mono_measure (Measure.restrict_mono_set volume hBK)
  have hDH := (fullBallProjectedHarmonicDerivativeAmbient_memLp_two u D p a b c
    hρ hρone t).mono_measure (Measure.restrict_mono_set volume hBK)
  refine ⟨hu.add hH, hD.add hDH, ?_⟩
  intro i
  exact hasWeakGradientOn_add_of_memLp_two (hu.eval i) (hH.eval i)
    (hD.eval i) (hDH.eval i) ((hwt i).mono hB hB1)
    (fullBallProjectedHarmonicGradientAmbient_hasWeakGradient u D p a b c hB hB1 t i)

/-- The actual corrected velocity remains weakly divergence-free on the original interval. -/
theorem fullBallProjectedVelocityAmbient_divergenceFree_slices_ae
    {Ω : Set Vec3} {I : Set ℝ} {q ρ : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ ψ : WeakTestFunction B,
      (∫ x in B, ∑ i : Fin 3, fullBallProjectedVelocityAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) = 0 := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hboxB : localBox Ω I B (Ioo a b) :=
    ⟨hB, hbox.2.1.of_isClosed_subset isClosed_closure (closure_mono hB1),
      (closure_mono hB1).trans hbox.2.2.1, hbox.2.2.2⟩
  filter_upwards [suitable_divergenceFree_slices_ae_localBox hsol hboxB,
    slice_memLp_ae_of_sws hsol hboxB] with t hdiv ht ψ
  have hH := (fullBallProjectedHarmonicGradientAmbient_memLp_two u D p a b c
    hρ hρone t).mono_measure (Measure.restrict_mono_set volume hBK)
  have hψd (i : Fin 3) : MemLp (spatialDeriv ψ.toFun i) 2 (volume.restrict B) :=
    ((stokesWeakTestDerivative ψ i).contDiff.continuous.memLp_of_hasCompactSupport
      (stokesWeakTestDerivative ψ i).hasCompactSupport).restrict B
  have hu (i : Fin 3) : Integrable (fun x ↦ u (x, t) i * spatialDeriv ψ.toFun i x)
      (volume.restrict B) := (ht.1.eval i).integrable_mul (hψd i)
  have hh (i : Fin 3) : Integrable (fun x ↦
      fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) (volume.restrict B) :=
    (hH.eval i).integrable_mul (hψd i)
  have hus : Integrable (fun x ↦ ∑ i : Fin 3, u (x, t) i * spatialDeriv ψ.toFun i x)
      (volume.restrict B) := integrable_finsetSum _ (fun i _ ↦ hu i)
  have hhs : Integrable (fun x ↦ ∑ i : Fin 3,
      fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t) i *
        spatialDeriv ψ.toFun i x) (volume.restrict B) :=
    integrable_finsetSum _ (fun i _ ↦ hh i)
  simp only [fullBallProjectedVelocityAmbient, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [integral_add hus hhs, hdiv ψ,
    fullBallProjectedHarmonicGradientAmbient_divergenceFree u D p a b c hB hB1 t ψ]
  simp

end FluidSingularSets
