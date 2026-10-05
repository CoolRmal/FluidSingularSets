-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Setting.ScalingInvariance
public import CKN.Setting.PressureGaugeSlices
public import CKN.Setting.Energy.PointwiseEnergy
public import CKN.Setting.Energy.Calculus
public import CKN.ClassEquivalence.TestSupport
public import CKN.Setting.Examples.ShearCounterexample.FactorIBP
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Accelerated coordinates for the actual suitable solution

The map follows a time-dependent spatial translation. Its Jacobian is one.
The relative velocity subtracts the frame velocity, and the affine pressure
accounts for the acceleration. Smooth-frame test transport is developed on
the ordinary product carrier used by the genuine CKN weak identities.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The moving coordinate map on the ordinary space-time product. -/
def acceleratedFrameMapProd (X : ℝ → Vec3) (w : Vec3 × ℝ) : Vec3 × ℝ :=
  (X w.2 + w.1, w.2)

/-- The same moving coordinate map on the actual parabolic carrier. -/
def acceleratedFrameMap (X : ℝ → Vec3) (w : ParabolicPoint) : ParabolicPoint :=
  (X w.2 + w.1, w.2)

/-- The relative velocity in moving coordinates. -/
def acceleratedVelocity (X m : ℝ → Vec3) (u : ParabolicPoint → Vec3)
    (w : ParabolicPoint) : Vec3 := u (acceleratedFrameMap X w) - m w.2

/-- Spatial translation leaves the gradient array unchanged apart from composition. -/
def acceleratedGradient (X : ℝ → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (w : ParabolicPoint) : Fin 3 → Vec3 := Du (acceleratedFrameMap X w)

/-- The force transforms by composition with the moving coordinates. -/
def acceleratedForce (X : ℝ → Vec3) (f : ParabolicPoint → Vec3)
    (w : ParabolicPoint) : Vec3 := f (acceleratedFrameMap X w)

/-- The affine acceleration potential in the pressure. -/
def acceleratedPressure (X a : ℝ → Vec3) (p : ParabolicPoint → ℝ)
    (w : ParabolicPoint) : ℝ :=
  p (acceleratedFrameMap X w) + ∑ i : Fin 3, a w.2 i * w.1 i

/-- Continuous moving coordinates are an actual homeomorphism of the ordinary
product space. No differentiability is needed for this geometric fact. -/
def acceleratedFrameHomeomorph (X : ℝ → Vec3) (hX : Continuous X) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) where
  toFun := acceleratedFrameMapProd X
  invFun := acceleratedFrameMapProd (fun t ↦ -X t)
  left_inv := by intro w; ext <;> simp [acceleratedFrameMapProd]
  right_inv := by intro w; ext <;> simp [acceleratedFrameMapProd]
  continuous_toFun := ((hX.comp continuous_snd).add continuous_fst).prodMk continuous_snd
  continuous_invFun := ((hX.neg.comp continuous_snd).add continuous_fst).prodMk continuous_snd

/-- Every measurable time-dependent translation preserves ordinary product volume. -/
theorem acceleratedFrameMapProd_measurePreserving
    (X : ℝ → Vec3) (hX : Measurable X) :
    MeasurePreserving (acceleratedFrameMapProd X) volume volume := by
  have hskew : MeasurePreserving
      (fun w : ℝ × Vec3 ↦ (w.1, X w.1 + w.2))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      ((hX.comp measurable_fst).add measurable_snd)
      (Eventually.of_forall fun t ↦
        (measurePreserving_add_left (volume : Measure Vec3) (X t)).map_eq)
  rw [Measure.volume_eq_prod]
  have hcomp := measurePreserving_swap.comp (hskew.comp measurePreserving_swap)
  convert hcomp using 1
  rfl

/-- Moving coordinates preserve the actual parabolic volume as well. -/
theorem acceleratedFrameMap_measurePreserving
    (X : ℝ → Vec3) (hX : Measurable X) :
    MeasurePreserving (acceleratedFrameMap X) volume volume := by
  have h := acceleratedFrameMapProd_measurePreserving X hX
  rw [Measure.volume_eq_prod] at h
  rw [volume_parabolicPoint_eq_prod]
  exact h

/-- Smooth paths give smooth forward and inverse moving-coordinate maps. -/
theorem acceleratedFrameMapProd_contDiff
    {X : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X) :
    ContDiff ℝ (⊤ : ℕ∞) (acceleratedFrameMapProd X) ∧
      ContDiff ℝ (⊤ : ℕ∞) (acceleratedFrameMapProd (fun t ↦ -X t)) := by
  constructor <;> unfold acceleratedFrameMapProd <;> fun_prop

/-- A test on moving coordinates is pulled back by the inverse path. -/
def acceleratedTestPullback {V : Type*} (X : ℝ → Vec3) (ψ : Vec3 × ℝ → V) :
    Vec3 × ℝ → V := ψ ∘ acceleratedFrameMapProd (fun t ↦ -X t)

/-- Smooth moving-coordinate tests remain genuine smooth compact tests on
the original domain whenever the entire source tube lies there. -/
theorem acceleratedTestPullback_mem_spaceTimeTest
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {B Ω : Set Vec3} {J I : Set ℝ} {ψ : Vec3 × ℝ → V}
    (hψ : ψ ∈ spaceTimeTestFunction (V := V) B J)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I) :
    acceleratedTestPullback X ψ ∈ spaceTimeTestFunction (V := V) Ω I := by
  refine ⟨hψ.1.comp (acceleratedFrameMapProd_contDiff hX).2, ?_, ?_⟩
  · exact hψ.2.1.comp_homeomorph (acceleratedFrameHomeomorph X hX.continuous).symm
  · change tsupport (ψ ∘ (acceleratedFrameHomeomorph X hX.continuous).symm) ⊆ Ω ×ˢ I
    rw [tsupport_comp_eq_preimage ψ (acceleratedFrameHomeomorph X hX.continuous).symm,
      ← (acceleratedFrameHomeomorph X hX.continuous).image_eq_preimage_symm]
    exact (image_mono hψ.2.2).trans htube

/-- The spatial derivatives of a pulled-back test are the translated spatial
derivatives. The path can be arbitrary because time is fixed in this derivative. -/
theorem accelerated_spatialPartial_pullback (X : ℝ → Vec3)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (acceleratedTestPullback X ψ) i (acceleratedFrameMap X z) =
      spatialPartial ψ i z := by
  have h := spatialPartial_pullback 1 (by norm_num) (X z.2, 0) hψ i z
  simpa [acceleratedTestPullback, acceleratedFrameMapProd, acceleratedFrameMap,
    scalingParabolic, scalingSpace, scalingTime, parabolicTranslate, parabolicScale,
    spatialPartial, Function.comp_def,
    sub_eq_add_neg, add_comm] using h

/-- Both spatial differentiations commute with a time-dependent translation. -/
theorem accelerated_spatialSecondPartial_pullback (X : ℝ → Vec3)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : ParabolicPoint) :
    spatialSecondPartial (acceleratedTestPullback X ψ) i j (acceleratedFrameMap X z) =
      spatialSecondPartial ψ i j z := by
  have h := spatialSecondPartial_pullback 1 (by norm_num) (X z.2, 0) hψ i j z
  simpa [acceleratedTestPullback, acceleratedFrameMapProd, acceleratedFrameMap,
    scalingParabolic, scalingSpace, scalingTime, parabolicTranslate, parabolicScale,
    spatialSecondPartial, spatialPartial,
    Function.comp_def, sub_eq_add_neg, add_comm] using h

/-- The ordinary product derivative splits into the three spatial coordinate
directions and the one time direction. -/
theorem product_linearMap_basis_decomposition
    (L : (Vec3 × ℝ) →L[ℝ] ℝ) (v : Vec3) (s : ℝ) :
    L (v, s) = (∑ i : Fin 3, v i * L (basisVec i, 0)) + s * L (0, 1) := by
  have hspace : L (v, 0) = ∑ i : Fin 3, v i * L (basisVec i, 0) := by
    change (L.comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)) v = _
    rw [← sum_smul_basisVec v, _root_.map_sum]
    simp
  have htime : L (0, s) = s * L (0, 1) := by
    simpa using L.map_smul s (0, 1)
  have hsum : (v, s) = (v, 0) + (0, s) := by simp
  rw [hsum, _root_.map_add, hspace, htime]

/-- The genuine chain rule for an accelerated test introduces precisely the
frame-velocity convection term, with the correct sign. -/
theorem accelerated_timePartial_pullback
    {X m : ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : Vec3 × ℝ)
    (hX : HasDerivAt X (m z.2) z.2) :
    timePartial (acceleratedTestPullback X ψ) (acceleratedFrameMap X z) =
      timePartial ψ z - ∑ i : Fin 3, m z.2 i * spatialPartial ψ i z := by
  have hcurve := (hX.neg.add_const (X z.2 + z.1)).prodMk (hasDerivAt_id z.2)
  have hpoint : (-X z.2 + (X z.2 + z.1), z.2) = (z.1, z.2) := by simp
  have hcomp := (hψ.differentiable (by simp)
    (-X z.2 + (X z.2 + z.1), z.2)).hasFDerivAt.comp_hasDerivAt
    (f := fun t : ℝ ↦ (-X t + (X z.2 + z.1), t)) z.2 hcurve
  change deriv (fun t ↦ ψ (-X t + (X z.2 + z.1), t)) z.2 = _
  calc
    _ = (fderiv ℝ ψ (z.1, z.2)) (-m z.2, 1) := by
      simpa only [Function.comp_def, hpoint] using hcomp.deriv
    _ = _ := by
      rw [product_linearMap_basis_decomposition]
      simp only [Pi.neg_apply, neg_mul, one_mul]
      rw [← timePartial_eq_joint_fderiv hψ (z.1, z.2)]
      simp_rw [← spatialPartial_eq_joint_fderiv hψ (z.1, z.2)]
      rw [Finset.sum_neg_distrib]
      ring

/-- A smooth moving mean pairs to zero with every compact spatial divergence.
This is the boundary cancellation needed when subtracting the frame velocity. -/
theorem accelerated_mean_divergence_pairing
    {m : ℝ → Vec3} (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    Integrable (fun z : Vec3 × ℝ ↦ ∑ i : Fin 3, m z.2 i * spatialPartial ψ i z) volume ∧
      ∫ z : Vec3 × ℝ, ∑ i : Fin 3, m z.2 i * spatialPartial ψ i z = 0 := by
  have hmi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ ↦ m z.2 i) := by
    exact ((contDiff_apply ℝ ℝ i).comp hm).comp contDiff_snd
  have hi (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ ↦ m z.2 i * spatialPartial ψ i z) volume := by
    have hcompact : HasCompactSupport (fun z : Vec3 × ℝ ↦ spatialPartial ψ i z) :=
      hcψ.isCompact.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_spatialPartial_subset i)
    exact ((hmi i).continuous.mul (spatialPartial_contDiff hψ i).continuous)
      |>.integrable_of_hasCompactSupport hcompact.mul_left
  have hzero (i : Fin 3) :
      ∫ z : Vec3 × ℝ, m z.2 i * spatialPartial ψ i z = 0 := by
    have h := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
      (hmi i) hψ hcψ i
    have hderiv (z : Vec3 × ℝ) :
        spatialPartial (fun w : Vec3 × ℝ ↦ m w.2 i) i z = 0 := by
      simp [spatialPartial]
    simpa only [hderiv, zero_mul, integral_zero, neg_zero] using h
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  exact Finset.sum_eq_zero fun i _ ↦ hzero i

/-- An actual suitable solution remains distributionally divergence free after
an arbitrary smooth moving translation and subtraction of a smooth mean.
The mean need not equal the path derivative for this spatial identity. -/
theorem suitable_accelerated_divergence
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J) :
    IntegrableOn (fun z ↦ ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z)
        (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet B J,
        ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z = 0 := by
  let Ψ := acceleratedTestPullback X ψ
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    acceleratedTestPullback_mem_spaceTimeTest hX hψ htube
  obtain ⟨hint, hzero⟩ := hsol.2.2.2.2.2.2.1 Ψ hΨ
  have hsupp : Function.support
      (fun z : ParabolicPoint ↦ ∑ i, u z i * spatialPartial Ψ i z) ⊆
        tsupport (show ParabolicPoint → ℝ from Ψ) := by
    rw [tsupport_parabolic_eq]
    intro z hz
    by_contra hcon
    apply hz
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [spatialPartial_eq_zero_off_tsupport hcon i, mul_zero]
  have hInt : Integrable
      (fun z : Vec3 × ℝ ↦ ∑ i, u z i * spatialPartial Ψ i z) volume :=
    (integrableOn_iff_integrable_of_support_subset hsupp).mp hint
  have hoff (z : Vec3 × ℝ) (hz : z ∉ spaceTimeSet Ω I) :
      (∑ i, u z i * spatialPartial Ψ i z) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [spatialPartial_eq_zero_off_tsupport (fun hmem ↦ hz (hΨ.2.2 hmem)) i,
        mul_zero]
  have hfull : ∫ z : Vec3 × ℝ, ∑ i, u z i * spatialPartial Ψ i z = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
    exact hzero
  have hMP := acceleratedFrameMapProd_measurePreserving X hX.continuous.measurable
  have hfun : (fun z : Vec3 × ℝ ↦ ∑ i, u (acceleratedFrameMap X z) i *
      spatialPartial ψ i z) =
      (fun z : Vec3 × ℝ ↦ ∑ i, u z i * spatialPartial Ψ i z) ∘
        acceleratedFrameMapProd X := by
    funext z
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun a : ℝ ↦ u (acceleratedFrameMap X z) i * a)
      (accelerated_spatialPartial_pullback X hψ.1 i z).symm
  have htranslated : Integrable (fun z : Vec3 × ℝ ↦
      ∑ i, u (acceleratedFrameMap X z) i * spatialPartial ψ i z) volume := by
    rw [hfun]
    exact hMP.integrable_comp_of_integrable hInt
  have htranslated_zero : ∫ z : Vec3 × ℝ,
      ∑ i, u (acceleratedFrameMap X z) i * spatialPartial ψ i z = 0 := by
    rw [hfun]
    exact (hMP.integral_comp
      (acceleratedFrameHomeomorph X hX.continuous).measurableEmbedding _).trans hfull
  obtain ⟨hmean, hmean_zero⟩ := accelerated_mean_divergence_pairing hm hψ.1 hψ.2.1
  have hvfun : (fun z : Vec3 × ℝ ↦
      ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) =
      fun z : Vec3 × ℝ ↦
        (∑ i, u (acceleratedFrameMap X z) i * spatialPartial ψ i z) -
          ∑ i, m z.2 i * spatialPartial ψ i z := by
    funext z
    simp only [acceleratedVelocity, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hvInt : Integrable (fun z : Vec3 × ℝ ↦
      ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) volume := by
    rw [hvfun]
    exact htranslated.sub hmean
  refine ⟨hvInt.integrableOn, ?_⟩
  have hvzero : ∫ z : Vec3 × ℝ,
      ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z = 0 := by
    rw [hvfun, integral_sub htranslated hmean, htranslated_zero, hmean_zero, sub_self]
  have hvoff (z : Vec3 × ℝ) (hz : z ∉ spaceTimeSet B J) :
      (∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [spatialPartial_eq_zero_off_tsupport (fun hmem ↦ hz (hψ.2.2 hmem)) i,
        mul_zero]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hvoff).trans hvzero

/-- The exact integrand of the genuine CKN weak momentum identity. -/
def frameMomentumDensity
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (φ : Vec3 × ℝ → Vec3) (z : ParabolicPoint) : ℝ :=
  -(∑ i, u z i * timePartial (fun w ↦ φ w i) z) -
    ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w ↦ φ w i) j z +
      ∑ i, ∑ j, Du z i j * spatialPartial (fun w ↦ φ w i) j z -
        p z * ∑ i, spatialPartial (fun w ↦ φ w i) i z - ∑ i, f z i * φ z i

/-- Weak momentum densities vanish outside the closed support of the test. -/
theorem frameMomentumDensity_eq_zero_off_tsupport
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    {φ : Vec3 × ℝ → Vec3} {z : ParabolicPoint}
    (hz : z ∉ tsupport (show ParabolicPoint → Vec3 from φ)) :
    frameMomentumDensity u Du p f φ z = 0 := by
  rw [tsupport_parabolic_eq] at hz
  have hφ0 : φ z = 0 := by
    by_contra hne
    exact hz (subset_tsupport φ (Function.mem_support.mpr hne))
  have hcomp (i : Fin 3) : z ∉ tsupport (fun w : Vec3 × ℝ ↦ φ w i) := by
    intro hmem
    exact hz (tsupport_component_subset (V := Vec3) φ i
      (fun w hw ↦ by rw [hw]; rfl) hmem)
  have hs (i j : Fin 3) : spatialPartial (fun w ↦ φ w i) j z = 0 :=
    spatialPartial_eq_zero_off_tsupport (hcomp i) j
  have ht (i : Fin 3) : timePartial (fun w ↦ φ w i) z = 0 :=
    timePartial_eq_zero_off_tsupport (hcomp i)
  simp [frameMomentumDensity, hφ0, hs, ht]

/-- The actual suitable weak momentum equation can be integrated over all
ordinary space-time because the integrand is supported on its compact test. -/
theorem suitable_global_momentum
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    Integrable (fun z : Vec3 × ℝ ↦ frameMomentumDensity u Du p f φ z) volume ∧
      ∫ z : Vec3 × ℝ, frameMomentumDensity u Du p f φ z = 0 := by
  obtain ⟨hint, hzero⟩ := hsol.2.2.2.2.2.2.2.1 φ hφ
  have hsupp : Function.support (frameMomentumDensity u Du p f φ) ⊆
      tsupport (show ParabolicPoint → Vec3 from φ) := by
    intro z hz
    by_contra hcon
    exact hz (frameMomentumDensity_eq_zero_off_tsupport u Du p f hcon)
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsupp).mp hint, ?_⟩
  have hoff (z : Vec3 × ℝ) (hz : z ∉ spaceTimeSet Ω I) :
      frameMomentumDensity u Du p f φ z = 0 :=
    frameMomentumDensity_eq_zero_off_tsupport u Du p f (by
      rw [tsupport_parabolic_eq]
      exact fun hmem ↦ hz (hφ.2.2 hmem))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
  exact hzero

/-- Pointwise weak momentum transport leaves only the mean time derivative,
the mean convection, and the affine acceleration-pressure correction.
The three terms will cancel after integration. -/
theorem accelerated_momentum_density_identity
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    {X m a : ℝ → Vec3} {φ : Vec3 × ℝ → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : ParabolicPoint)
    (hX : HasDerivAt X (m z.2) z.2) :
    frameMomentumDensity (acceleratedVelocity X m u) (acceleratedGradient X Du)
        (acceleratedPressure X a p) (acceleratedForce X f) φ z =
      frameMomentumDensity u Du p f (acceleratedTestPullback X φ)
          (acceleratedFrameMap X z) +
        (∑ i : Fin 3, m z.2 i * timePartial (fun w ↦ φ w i) z) +
          (∑ i : Fin 3, ∑ j : Fin 3, m z.2 i * acceleratedVelocity X m u z j *
            spatialPartial (fun w ↦ φ w i) j z) -
              (∑ i : Fin 3, a z.2 i * z.1 i) *
                ∑ i : Fin 3, spatialPartial (fun w ↦ φ w i) i z := by
  have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ ↦ φ w i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hs (i j : Fin 3) :
      spatialPartial (fun w ↦ acceleratedTestPullback X φ w i) j
          (acceleratedFrameMap X z) = spatialPartial (fun w ↦ φ w i) j z :=
    accelerated_spatialPartial_pullback X (hcomp i) j z
  have ht (i : Fin 3) :
      timePartial (fun w ↦ acceleratedTestPullback X φ w i) (acceleratedFrameMap X z) =
        timePartial (fun w ↦ φ w i) z -
          ∑ j : Fin 3, m z.2 j * spatialPartial (fun w ↦ φ w i) j z :=
    accelerated_timePartial_pullback (hcomp i) (z.1, z.2) hX
  have hvalue (i : Fin 3) :
      acceleratedTestPullback X φ (acceleratedFrameMap X z) i = φ z i := by
    simp [acceleratedTestPullback, acceleratedFrameMapProd, acceleratedFrameMap]
  unfold frameMomentumDensity
  simp only [ht, hs, hvalue, acceleratedVelocity, acceleratedGradient,
    acceleratedPressure, acceleratedForce, Pi.sub_apply]
  simp only [Fin.sum_univ_three]
  ring

/-- A smooth time-dependent vector mean differentiated in a test pairing
produces exactly the negative acceleration pairing. -/
theorem accelerated_mean_time_pairing
    {m a : ℝ → Vec3} (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hma : ∀ t, HasDerivAt m (a t) t)
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) :
    Integrable (fun z : Vec3 × ℝ ↦ ∑ i, m z.2 i * timePartial (fun w ↦ φ w i) z)
        volume ∧
      Integrable (fun z : Vec3 × ℝ ↦ ∑ i, a z.2 i * φ z i) volume ∧
        (∫ z : Vec3 × ℝ, ∑ i, m z.2 i * timePartial (fun w ↦ φ w i) z) =
          -(∫ z : Vec3 × ℝ, ∑ i, a z.2 i * φ z i) := by
  have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ ↦ φ w i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hccomp (i : Fin 3) : HasCompactSupport (fun w : Vec3 × ℝ ↦ φ w i) :=
    hcφ.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_component_subset (V := Vec3) φ i (fun w hw ↦ by rw [hw]; rfl))
  have hmi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ ↦ m z.2 i) :=
    ((contDiff_apply ℝ ℝ i).comp hm).comp contDiff_snd
  have hai (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ ↦ a z.2 i) :=
    ((contDiff_apply ℝ ℝ i).comp ha).comp contDiff_snd
  have hi (i : Fin 3) : Integrable (fun z : Vec3 × ℝ ↦
      m z.2 i * timePartial (fun w ↦ φ w i) z) volume :=
    ((hmi i).continuous.mul (contDiff_timePartial (hcomp i)).continuous)
      |>.integrable_of_hasCompactSupport (hasCompactSupport_timePartial (hccomp i)).mul_left
  have hj (i : Fin 3) : Integrable (fun z : Vec3 × ℝ ↦ a z.2 i * φ z i) volume :=
    ((hai i).continuous.mul (hcomp i).continuous)
      |>.integrable_of_hasCompactSupport (hccomp i).mul_left
  have heq (i : Fin 3) :
      (∫ z : Vec3 × ℝ, m z.2 i * timePartial (fun w ↦ φ w i) z) =
        -(∫ z : Vec3 × ℝ, a z.2 i * φ z i) := by
    have h := integral_mul_timePartial_eq_neg_timePartial_mul
      (hmi i) (hcomp i) (hccomp i)
    have hderiv (z : ParabolicPoint) : timePartial (fun w : Vec3 × ℝ ↦ m w.2 i) z =
        a z.2 i := by
      change deriv (fun t : ℝ ↦ m t i) z.2 = _
      exact (hasDerivAt_pi.mp (hma z.2) i).deriv
    calc
      _ = -(∫ z : Vec3 × ℝ, timePartial (fun w : Vec3 × ℝ ↦ m w.2 i) z * φ z i) := h
      _ = _ := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        exact Eventually.of_forall fun z ↦ congrArg (fun b : ℝ ↦ b * φ z i) (hderiv z)
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hi i),
    integrable_finsetSum _ (fun i _ ↦ hj i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hi i),
    integral_finsetSum _ (fun i _ ↦ hj i), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ heq i

/-- The actual moving-coordinate divergence identity in its global integral
form, convenient for compactly supported momentum correction tests. -/
theorem suitable_accelerated_global_divergence
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) B J) :
    Integrable (fun z : Vec3 × ℝ ↦
      ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) volume ∧
      ∫ z : Vec3 × ℝ,
        ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z = 0 := by
  obtain ⟨hint, hzero⟩ := suitable_accelerated_divergence hsol hX hm htube hψ
  have hsupp : Function.support
      (fun z : ParabolicPoint ↦
        ∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) ⊆
        tsupport (show ParabolicPoint → ℝ from ψ) := by
    rw [tsupport_parabolic_eq]
    intro z hz
    by_contra hcon
    exact hz (Finset.sum_eq_zero fun i _ ↦ by
      rw [spatialPartial_eq_zero_off_tsupport hcon i, mul_zero])
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsupp).mp hint, ?_⟩
  have hoff (z : Vec3 × ℝ) (hz : z ∉ spaceTimeSet B J) :
      (∑ i, acceleratedVelocity X m u z i * spatialPartial ψ i z) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [spatialPartial_eq_zero_off_tsupport (fun hmem ↦ hz (hψ.2.2 hmem)) i,
        mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
  exact hzero

/-- The actual transformed divergence equation cancels the entire mean
convection term in weak momentum, with support integrability proved as well. -/
theorem suitable_accelerated_mean_convection_pairing
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) B J) :
    Integrable (fun z : Vec3 × ℝ ↦
        ∑ i, ∑ j, m z.2 i * acceleratedVelocity X m u z j *
          spatialPartial (fun w ↦ φ w i) j z) volume ∧
      ∫ z : Vec3 × ℝ, ∑ i, ∑ j, m z.2 i * acceleratedVelocity X m u z j *
        spatialPartial (fun w ↦ φ w i) j z = 0 := by
  have hcomp (i : Fin 3) :
      (fun w : Vec3 × ℝ ↦ φ w i) ∈ spaceTimeTestFunction (V := ℝ) B J := by
    have hsupp := tsupport_component_subset (V := Vec3) φ i
      (fun w hw ↦ by rw [hw]; rfl)
    exact ⟨(contDiff_apply ℝ ℝ i).comp hφ.1,
      hφ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport _) hsupp,
      hsupp.trans hφ.2.2⟩
  have htest (i : Fin 3) :
      (fun w : Vec3 × ℝ ↦ φ w i * m w.2 i) ∈ spaceTimeTestFunction (V := ℝ) B J :=
    spaceTimeTestFunction_mul_smooth (hcomp i)
      (((contDiff_apply ℝ ℝ i).comp hm).comp contDiff_snd)
  have hderiv (i j : Fin 3) (z : ParabolicPoint) :
      spatialPartial (fun w : Vec3 × ℝ ↦ φ w i * m w.2 i) j z =
        spatialPartial (fun w ↦ φ w i) j z * m z.2 i :=
    spatialPartial_mul_time (χ := fun t ↦ m t i) (hcomp i).1 j (z.1, z.2)
  have hfun (i : Fin 3) : (fun z : Vec3 × ℝ ↦
      ∑ j, m z.2 i * acceleratedVelocity X m u z j * spatialPartial (fun w ↦ φ w i) j z) =
      fun z : Vec3 × ℝ ↦ ∑ j, acceleratedVelocity X m u z j *
        spatialPartial (fun w : Vec3 × ℝ ↦ φ w i * m w.2 i) j z := by
    funext z
    apply Finset.sum_congr rfl
    intro j _
    rw [hderiv]
    ring
  have hi (i : Fin 3) : Integrable (fun z : Vec3 × ℝ ↦
      ∑ j, m z.2 i * acceleratedVelocity X m u z j * spatialPartial (fun w ↦ φ w i) j z)
      volume := by
    rw [hfun]
    exact (suitable_accelerated_global_divergence hsol hX hm htube (htest i)).1
  have heq (i : Fin 3) : (∫ z : Vec3 × ℝ,
      ∑ j, m z.2 i * acceleratedVelocity X m u z j * spatialPartial (fun w ↦ φ w i) j z)
      = 0 := by
    rw [hfun]
    exact (suitable_accelerated_global_divergence hsol hX hm htube (htest i)).2
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  exact Finset.sum_eq_zero fun i _ ↦ heq i

/-- The acceleration potential has spatial gradient equal to the frame
acceleration, independently of the time regularity of the latter. -/
theorem accelerated_affine_pressure_spatialPartial (a : ℝ → Vec3)
    (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w : Vec3 × ℝ ↦ ∑ i : Fin 3, a w.2 i * w.1 i) j z =
      a z.2 j := by
  have hDi (i : Fin 3) : HasFDerivAt (fun x : Vec3 ↦ a z.2 i * x i)
      (a z.2 i • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) i z.1).const_mul (a z.2 i)
  have hD := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hDi i)
  change fderiv ℝ (fun x : Vec3 ↦ ∑ i : Fin 3, a z.2 i * x i) z.1 (basisVec j) = _
  rw [hD.fderiv]
  simp [basisVec_apply]

/-- The affine acceleration pressure contributes exactly the negative
acceleration pairing in weak momentum. This cancels the moving-mean term. -/
theorem accelerated_affine_pressure_pairing
    {a : ℝ → Vec3} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) :
    Integrable (fun z : Vec3 × ℝ ↦
        (∑ i : Fin 3, a z.2 i * z.1 i) *
          ∑ i : Fin 3, spatialPartial (fun w ↦ φ w i) i z) volume ∧
      (∫ z : Vec3 × ℝ, (∑ i : Fin 3, a z.2 i * z.1 i) *
        ∑ i : Fin 3, spatialPartial (fun w ↦ φ w i) i z) =
          -(∫ z : Vec3 × ℝ, ∑ i : Fin 3, a z.2 i * φ z i) := by
  let A : Vec3 × ℝ → ℝ := fun z ↦ ∑ i : Fin 3, a z.2 i * z.1 i
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by dsimp [A]; fun_prop
  have hcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ ↦ φ w i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hccomp (i : Fin 3) : HasCompactSupport (fun w : Vec3 × ℝ ↦ φ w i) :=
    hcφ.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_component_subset (V := Vec3) φ i (fun w hw ↦ by rw [hw]; rfl))
  have hi (i : Fin 3) : Integrable (fun z : Vec3 × ℝ ↦
      A z * spatialPartial (fun w ↦ φ w i) i z) volume :=
    (hA.continuous.mul (spatialPartial_contDiff (hcomp i) i).continuous)
      |>.integrable_of_hasCompactSupport (hasCompactSupport_spatialPartial (hccomp i) i).mul_left
  have hj (i : Fin 3) : Integrable (fun z : Vec3 × ℝ ↦ a z.2 i * φ z i) volume := by
    have hai : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ ↦ a z.2 i) :=
      ((contDiff_apply ℝ ℝ i).comp ha).comp contDiff_snd
    exact (hai.continuous.mul (hcomp i).continuous)
      |>.integrable_of_hasCompactSupport (hccomp i).mul_left
  have heq (i : Fin 3) :
      (∫ z : Vec3 × ℝ, A z * spatialPartial (fun w ↦ φ w i) i z) =
        -(∫ z : Vec3 × ℝ, a z.2 i * φ z i) := by
    have h := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
      hA (hcomp i) (hccomp i) i
    calc
      _ = -(∫ z : Vec3 × ℝ, spatialPartial A i z * φ z i) := h
      _ = _ := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        exact Eventually.of_forall fun z ↦ congrArg (fun b : ℝ ↦ b * φ z i)
          (accelerated_affine_pressure_spatialPartial a i z)
  have hfun : (fun z : Vec3 × ℝ ↦ A z *
      ∑ i : Fin 3, spatialPartial (fun w ↦ φ w i) i z) =
      fun z ↦ ∑ i : Fin 3, A z * spatialPartial (fun w ↦ φ w i) i z := by
    funext z
    exact Finset.mul_sum _ _ _
  change Integrable (fun z : Vec3 × ℝ ↦ A z * ∑ i, _) volume ∧ _
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hi i),
    integral_finsetSum _ (fun i _ ↦ hj i), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ heq i

/-- The weak momentum equation of the actual suitable solution transports
through a smooth accelerating frame. Both the convection and acceleration
corrections are canceled by identities already derived from that solution. -/
theorem suitable_accelerated_momentum
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hXm : ∀ t, HasDerivAt X (m t) t) (hma : ∀ t, HasDerivAt m (a t) t)
    (htube : acceleratedFrameMapProd X '' (B ×ˢ J) ⊆ Ω ×ˢ I)
    {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) B J) :
    IntegrableOn (frameMomentumDensity (acceleratedVelocity X m u)
        (acceleratedGradient X Du) (acceleratedPressure X a p) (acceleratedForce X f) φ)
        (tsupport φ) volume ∧
      ∫ z in spaceTimeSet B J,
        frameMomentumDensity (acceleratedVelocity X m u) (acceleratedGradient X Du)
          (acceleratedPressure X a p) (acceleratedForce X f) φ z = 0 := by
  let Φ := acceleratedTestPullback X φ
  have hΦ : Φ ∈ spaceTimeTestFunction (V := Vec3) Ω I :=
    acceleratedTestPullback_mem_spaceTimeTest hX hφ htube
  obtain ⟨hsource, hsource_zero⟩ := suitable_global_momentum hsol hΦ
  let S : Vec3 × ℝ → ℝ :=
    fun z ↦ frameMomentumDensity u Du p f Φ (acceleratedFrameMap X z)
  let T : Vec3 × ℝ → ℝ :=
    fun z ↦ ∑ i, m z.2 i * timePartial (fun w ↦ φ w i) z
  let C : Vec3 × ℝ → ℝ :=
    fun z ↦ ∑ i, ∑ j, m z.2 i * acceleratedVelocity X m u z j *
      spatialPartial (fun w ↦ φ w i) j z
  let P : Vec3 × ℝ → ℝ :=
    fun z ↦ (∑ i : Fin 3, a z.2 i * z.1 i) *
      ∑ i : Fin 3, spatialPartial (fun w ↦ φ w i) i z
  have hMP := acceleratedFrameMapProd_measurePreserving X hX.continuous.measurable
  have hS : Integrable S volume := hMP.integrable_comp_of_integrable hsource
  have hSzero : ∫ z, S z = 0 :=
    (hMP.integral_comp
      (acceleratedFrameHomeomorph X hX.continuous).measurableEmbedding _).trans hsource_zero
  obtain ⟨hT, hA, hTeq⟩ := accelerated_mean_time_pairing hm ha hma hφ.1 hφ.2.1
  obtain ⟨hC, hCzero⟩ :=
    suitable_accelerated_mean_convection_pairing hsol hX hm htube hφ
  obtain ⟨hP, hPeq⟩ := accelerated_affine_pressure_pairing ha hφ.1 hφ.2.1
  change Integrable T volume at hT
  change Integrable C volume at hC
  change Integrable P volume at hP
  change (∫ z, C z) = 0 at hCzero
  change (∫ z, T z) = -(∫ z : Vec3 × ℝ, ∑ i, a z.2 i * φ z i) at hTeq
  change (∫ z, P z) = -(∫ z : Vec3 × ℝ, ∑ i, a z.2 i * φ z i) at hPeq
  have hfun : (fun z : Vec3 × ℝ ↦
      frameMomentumDensity (acceleratedVelocity X m u) (acceleratedGradient X Du)
        (acceleratedPressure X a p) (acceleratedForce X f) φ z) =
      fun z ↦ S z + T z + C z - P z := by
    funext z
    exact accelerated_momentum_density_identity u Du p f hφ.1 z (hXm z.2)
  have hInt : Integrable (fun z : Vec3 × ℝ ↦
      frameMomentumDensity (acceleratedVelocity X m u) (acceleratedGradient X Du)
        (acceleratedPressure X a p) (acceleratedForce X f) φ z) volume := by
    rw [hfun]
    exact ((hS.add hT).add hC).sub hP
  have hzero : ∫ z : Vec3 × ℝ,
      frameMomentumDensity (acceleratedVelocity X m u) (acceleratedGradient X Du)
        (acceleratedPressure X a p) (acceleratedForce X f) φ z = 0 := by
    rw [hfun, integral_sub (f := fun z ↦ S z + T z + C z) (g := P)
      ((hS.add hT).add hC) hP,
      integral_add (f := fun z ↦ S z + T z) (g := C) (hS.add hT) hC,
      integral_add (f := S) (g := T) hS hT]
    change (∫ z, S z) + (∫ z, T z) + (∫ z, C z) - (∫ z, P z) = 0
    rw [hSzero, hCzero]
    rw [hTeq, hPeq]
    ring
  refine ⟨hInt.integrableOn, ?_⟩
  have hoff (z : Vec3 × ℝ) (hz : z ∉ spaceTimeSet B J) :
      frameMomentumDensity (acceleratedVelocity X m u) (acceleratedGradient X Du)
        (acceleratedPressure X a p) (acceleratedForce X f) φ z = 0 :=
    frameMomentumDensity_eq_zero_off_tsupport _ _ _ _ (by
      rw [tsupport_parabolic_eq]
      exact fun hmem ↦ hz (hφ.2.2 hmem))
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).trans hzero

end FluidSingularSets
