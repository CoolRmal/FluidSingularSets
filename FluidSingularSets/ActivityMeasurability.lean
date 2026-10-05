module

public import FluidSingularSets.RealCharge
public import FluidSingularSets.MixedGradient
public import CKN.Foundation.Parabolic.Integration.Average
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurability of moving-cylinder activity

Tonelli gives joint measurability in the center and radius of cylinder masses and of the mixed
spatial gradient cost. Almost everywhere measurable densities suffice: one measurable
representative gives the same mass on every cylinder, and the same mixed cost after time
integration. Localization therefore applies directly to the energy class of actual solutions.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

noncomputable section

namespace FluidSingularSets

/-- Mass of a nonnegative density on a symmetric cylinder. -/
def symmetricCylinderMass (f : SpaceTime → ℝ≥0∞) (z : SpaceTime) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in symmetricL3Cylinder z r, f a

/-- Symmetric cylinders are measurable at every real radius. -/
theorem measurableSet_symmetricL3Cylinder (z : SpaceTime) (r : ℝ) :
    MeasurableSet (symmetricL3Cylinder z r) :=
  Metric.isOpen_ball.measurableSet.prod measurableSet_Ioo

/-- A measurable density has jointly measurable moving-cylinder mass. -/
theorem measurable_symmetricCylinderMass {f : SpaceTime → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun s : SpaceTime × ℝ ↦ symmetricCylinderMass f s.1 s.2) := by
  let A : Set ((SpaceTime × ℝ) × SpaceTime) :=
    {w | w.2 ∈ symmetricL3Cylinder w.1.1 w.1.2}
  have hA : MeasurableSet A := by
    change MeasurableSet {w : (SpaceTime × ℝ) × SpaceTime |
      dist w.2.1 w.1.1.1 < w.1.2 ∧
        w.1.1.2 - w.1.2 ^ 2 < w.2.2 ∧ w.2.2 < w.1.1.2 + w.1.2 ^ 2}
    have hspace : IsOpen {w : (SpaceTime × ℝ) × SpaceTime |
        dist w.2.1 w.1.1.1 < w.1.2} := isOpen_lt (by fun_prop) (by fun_prop)
    have hlow : IsOpen {w : (SpaceTime × ℝ) × SpaceTime |
        w.1.1.2 - w.1.2 ^ 2 < w.2.2} := isOpen_lt (by fun_prop) (by fun_prop)
    have hhigh : IsOpen {w : (SpaceTime × ℝ) × SpaceTime |
        w.2.2 < w.1.1.2 + w.1.2 ^ 2} := isOpen_lt (by fun_prop) (by fun_prop)
    exact (hspace.inter (hlow.inter hhigh)).measurableSet
  have hjoint := ((hf.comp measurable_snd).indicator hA).lintegral_prod_right'
    (ν := (volume : Measure SpaceTime))
  have heq : (fun s : SpaceTime × ℝ ↦ ∫⁻ a, A.indicator (fun w ↦ f w.2) (s, a)) =
      fun s ↦ symmetricCylinderMass f s.1 s.2 := by
    funext s
    change (∫⁻ a, (symmetricL3Cylinder s.1 s.2).indicator f a) =
      ∫⁻ a in symmetricL3Cylinder s.1 s.2, f a
    exact lintegral_indicator (measurableSet_symmetricL3Cylinder _ _) _
  rw [← heq]
  exact hjoint

/-- Almost everywhere measurable densities still give an everywhere measurable cylinder
mass function, because changes on a null set preserve every restricted integral. -/
theorem measurable_symmetricCylinderMass_of_aemeasurable {f : SpaceTime → ℝ≥0∞}
    (hf : AEMeasurable f volume) :
    Measurable (fun s : SpaceTime × ℝ ↦ symmetricCylinderMass f s.1 s.2) := by
  have heq : (fun s : SpaceTime × ℝ ↦ symmetricCylinderMass f s.1 s.2) =
      fun s ↦ symmetricCylinderMass (hf.mk f) s.1 s.2 := by
    funext s
    exact lintegral_congr_ae (ae_restrict_of_ae hf.ae_eq_mk)
  rw [heq]
  exact measurable_symmetricCylinderMass hf.measurable_mk

/-- A spatial ball integral with time retained as a parameter. -/
def spatialBallMass (f : SpaceTime → ℝ≥0∞) (z : SpaceTime) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball z.1 r, f (x, z.2)

/-- A measurable density has a jointly measurable spatial ball mass. -/
theorem measurable_spatialBallMass {f : SpaceTime → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun s : SpaceTime × ℝ ↦ spatialBallMass f s.1 s.2) := by
  let A : Set ((SpaceTime × ℝ) × Space) :=
    {w | dist w.2 w.1.1.1 < w.1.2}
  have hA : MeasurableSet A :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hg : Measurable (fun w : (SpaceTime × ℝ) × Space ↦ f (w.2, w.1.1.2)) :=
    hf.comp (by fun_prop)
  have hjoint := (hg.indicator hA).lintegral_prod_right' (ν := (volume : Measure Space))
  have heq : (fun s : SpaceTime × ℝ ↦
      ∫⁻ x, A.indicator (fun w ↦ f (w.2, w.1.1.2)) (s, x)) =
      fun s ↦ spatialBallMass f s.1 s.2 := by
    funext s
    change (∫⁻ x, (Metric.ball s.1.1 s.2).indicator (fun x ↦ f (x, s.1.2)) x) =
      ∫⁻ x in Metric.ball s.1.1 s.2, f (x, s.1.2)
    exact lintegral_indicator Metric.isOpen_ball.measurableSet _
  rwa [heq] at hjoint

/-- Time integral of the seven-sixths power of the spatial density mass. -/
def symmetricMixedMass (f : SpaceTime → ℝ≥0∞) (z : SpaceTime) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (z.2 - r ^ 2) (z.2 + r ^ 2), spatialBallMass f (z.1, t) r ^ (7 / 6 : ℝ)

/-- For a measurable density, the mixed mass is jointly measurable in center and radius. -/
theorem measurable_symmetricMixedMass {f : SpaceTime → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun s : SpaceTime × ℝ ↦ symmetricMixedMass f s.1 s.2) := by
  let A : Set ((SpaceTime × ℝ) × ℝ) :=
    {w | w.1.1.2 - w.1.2 ^ 2 < w.2 ∧ w.2 < w.1.1.2 + w.1.2 ^ 2}
  have hA : MeasurableSet A := by
    have hlow : IsOpen {w : (SpaceTime × ℝ) × ℝ |
        w.1.1.2 - w.1.2 ^ 2 < w.2} := isOpen_lt (by fun_prop) (by fun_prop)
    have hhigh : IsOpen {w : (SpaceTime × ℝ) × ℝ |
        w.2 < w.1.1.2 + w.1.2 ^ 2} := isOpen_lt (by fun_prop) (by fun_prop)
    exact (hlow.inter hhigh).measurableSet
  have hg : Measurable (fun w : (SpaceTime × ℝ) × ℝ ↦
      spatialBallMass f (w.1.1.1, w.2) w.1.2 ^ (7 / 6 : ℝ)) :=
    ((measurable_spatialBallMass hf).comp
      (show Measurable (fun w : (SpaceTime × ℝ) × ℝ ↦ ((w.1.1.1, w.2), w.1.2)) from
        by fun_prop)).pow_const _
  have hjoint := (hg.indicator hA).lintegral_prod_right' (ν := (volume : Measure ℝ))
  have heq : (fun s : SpaceTime × ℝ ↦
      ∫⁻ t, A.indicator
        (fun w ↦ spatialBallMass f (w.1.1.1, w.2) w.1.2 ^ (7 / 6 : ℝ)) (s, t)) =
      fun s ↦ symmetricMixedMass f s.1 s.2 := by
    funext s
    change (∫⁻ t, (Ioo (s.1.2 - s.2 ^ 2) (s.1.2 + s.2 ^ 2)).indicator
      (fun t ↦ spatialBallMass f (s.1.1, t) s.2 ^ (7 / 6 : ℝ)) t) = _
    exact lintegral_indicator measurableSet_Ioo _
  rwa [heq] at hjoint

/-- Null-set changes in the joint density preserve every time-integrated mixed mass. -/
theorem symmetricMixedMass_congr_ae {f g : SpaceTime → ℝ≥0∞} (hfg : f =ᵐ[volume] g)
    (z : SpaceTime) (r : ℝ) : symmetricMixedMass f z r = symmetricMixedMass g z r := by
  rw [Measure.volume_eq_prod] at hfg
  have hmp := Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
  have hswap := hmp.quasiMeasurePreserving.ae_eq_comp hfg
  have hslices := Measure.ae_ae_of_ae_prod hswap
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hslices] with t ht
  congr 1
  exact lintegral_congr_ae (ae_restrict_of_ae ht)

/-- Joint almost everywhere measurability suffices for everywhere measurable mixed mass. -/
theorem measurable_symmetricMixedMass_of_aemeasurable {f : SpaceTime → ℝ≥0∞}
    (hf : AEMeasurable f volume) :
    Measurable (fun s : SpaceTime × ℝ ↦ symmetricMixedMass f s.1 s.2) := by
  have heq : (fun s : SpaceTime × ℝ ↦ symmetricMixedMass f s.1 s.2) =
      fun s ↦ symmetricMixedMass (hf.mk f) s.1 s.2 := by
    funext s
    exact symmetricMixedMass_congr_ae hf.ae_eq_mk _ _
  rw [heq]
  exact measurable_symmetricMixedMass hf.measurable_mk

/-- The real velocity-pressure activity is jointly measurable, even for merely almost
everywhere measurable velocity and pressure. -/
theorem measurable_symmetricL3Activity {u : SpaceTime → Space} {p : SpaceTime → ℝ}
    (hu : AEStronglyMeasurable u volume) (hp : AEStronglyMeasurable p volume) :
    Measurable (fun s : SpaceTime × ℝ ↦ symmetricL3Activity u p s.1 s.2) := by
  have hmass := measurable_symmetricCylinderMass_of_aemeasurable
    ((hu.enorm.pow_const (3 : ℝ)).add (hp.enorm.pow_const (3 / 2 : ℝ)))
  have hscale : Measurable (fun s : SpaceTime × ℝ ↦ ENNReal.ofReal (s.2⁻¹ ^ 2)) := by
    fun_prop
  exact (hscale.mul hmass).ennreal_toReal

/-- The real mixed gradient activity, normalized by `r^(-3/2)`. -/
def symmetricMixedGradientActivity {F : Type*} [NormedAddCommGroup F]
    (D : SpaceTime → F) (z : SpaceTime) (r : ℝ) : ℝ :=
  (ENNReal.ofReal r ^ (-3 / 2 : ℝ) *
    symmetricMixedMass (fun a ↦ ‖D a‖ₑ ^ (12 / 7 : ℝ)) z r).toReal

/-- The mixed gradient activity is jointly measurable in center and radius. -/
theorem measurable_symmetricMixedGradientActivity {F : Type*} [NormedAddCommGroup F]
    {D : SpaceTime → F} (hD : AEStronglyMeasurable D volume) :
    Measurable (fun s : SpaceTime × ℝ ↦ symmetricMixedGradientActivity D s.1 s.2) := by
  have hmass := measurable_symmetricMixedMass_of_aemeasurable
    (hD.enorm.pow_const (12 / 7 : ℝ))
  have hscale : Measurable (fun s : SpaceTime × ℝ ↦
      ENNReal.ofReal s.2 ^ (-3 / 2 : ℝ)) := by fun_prop
  exact (hscale.mul hmass).ennreal_toReal

/-- A velocity-pressure cutoff changes no activity on cylinders contained in its carrier. -/
theorem symmetricL3Activity_indicator_of_subset {S : Set SpaceTime}
    (u : SpaceTime → Space) (p : SpaceTime → ℝ) (z : SpaceTime) (r : ℝ)
    (hsub : symmetricL3Cylinder z r ⊆ S) :
    symmetricL3Activity (S.indicator u) (S.indicator p) z r =
      symmetricL3Activity u p z r := by
  unfold symmetricL3Activity
  congr 2
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_symmetricL3Cylinder z r)] with a ha
  rw [indicator_of_mem (hsub ha), indicator_of_mem (hsub ha)]

set_option maxHeartbeats 800000 in
/-- A gradient cutoff changes no mixed activity on cylinders contained in its carrier. -/
theorem symmetricMixedGradientActivity_indicator_of_subset {F : Type*}
    [NormedAddCommGroup F] {S : Set SpaceTime} (D : SpaceTime → F)
    (z : SpaceTime) (r : ℝ) (hsub : symmetricL3Cylinder z r ⊆ S) :
    symmetricMixedGradientActivity (S.indicator D) z r =
      symmetricMixedGradientActivity D z r := by
  have hmass : symmetricMixedMass (fun a ↦ ‖S.indicator D a‖ₑ ^ (12 / 7 : ℝ)) z r =
      symmetricMixedMass (fun a ↦ ‖D a‖ₑ ^ (12 / 7 : ℝ)) z r := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hinner : spatialBallMass (fun a ↦ ‖S.indicator D a‖ₑ ^ (12 / 7 : ℝ)) (z.1, t) r =
        spatialBallMass (fun a ↦ ‖D a‖ₑ ^ (12 / 7 : ℝ)) (z.1, t) r := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hxs : (x, t) ∈ S := hsub (show (x, t) ∈ symmetricL3Cylinder z r from ⟨hx, ht⟩)
      have hvalue : S.indicator D (x, t) = D (x, t) :=
        indicator_of_mem hxs D
      exact congrArg (fun a : F ↦ ‖a‖ₑ ^ (12 / 7 : ℝ)) hvalue
    exact congrArg (fun a : ℝ≥0∞ ↦ a ^ (7 / 6 : ℝ)) hinner
  exact congrArg (fun a : ℝ≥0∞ ↦ (ENNReal.ofReal r ^ (-3 / 2 : ℝ) * a).toReal) hmass

/-- Local almost everywhere measurability of the fields suffices for measurability of real
activity against any measure carried by centers with cylinders in that local box. -/
theorem aemeasurable_symmetricL3Activity_of_local {S E : Set SpaceTime}
    (hS : MeasurableSet S) (hE : MeasurableSet E) (μ : Measure SpaceTime)
    {u : SpaceTime → Space} {p : SpaceTime → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict S))
    (hp : AEStronglyMeasurable p (volume.restrict S)) (r : ℝ)
    (hsub : ∀ z ∈ E, symmetricL3Cylinder z r ⊆ S) :
    AEMeasurable (fun z ↦ symmetricL3Activity u p z r) (μ.restrict E) := by
  have hu' := (aestronglyMeasurable_indicator_iff hS).2 hu
  have hp' := (aestronglyMeasurable_indicator_iff hS).2 hp
  have hm := ((measurable_symmetricL3Activity hu' hp').comp
    (show Measurable (fun z : SpaceTime ↦ (z, r)) from by fun_prop)).aemeasurable
    (μ := μ.restrict E)
  apply hm.congr
  filter_upwards [ae_restrict_mem hE] with z hz
  exact symmetricL3Activity_indicator_of_subset _ _ _ _ (hsub z hz)

/-- Local almost everywhere measurability likewise suffices for the mixed gradient activity
against any measure carried by centers with cylinders in the local box. -/
theorem aemeasurable_symmetricMixedGradientActivity_of_local {F : Type*}
    [NormedAddCommGroup F] {S E : Set SpaceTime} (hS : MeasurableSet S)
    (hE : MeasurableSet E) (μ : Measure SpaceTime) {D : SpaceTime → F}
    (hD : AEStronglyMeasurable D (volume.restrict S)) (r : ℝ)
    (hsub : ∀ z ∈ E, symmetricL3Cylinder z r ⊆ S) :
    AEMeasurable (fun z ↦ symmetricMixedGradientActivity D z r) (μ.restrict E) := by
  have hD' := (aestronglyMeasurable_indicator_iff hS).2 hD
  have hm := ((measurable_symmetricMixedGradientActivity hD').comp
    (show Measurable (fun z : SpaceTime ↦ (z, r)) from by fun_prop)).aemeasurable
    (μ := μ.restrict E)
  apply hm.congr
  filter_upwards [ae_restrict_mem hE] with z hz
  exact symmetricMixedGradientActivity_indicator_of_subset _ _ _ (hsub z hz)

/-- Actual suitable weak solutions give measurable velocity-pressure and mixed gradient
activity on every family of centers whose cylinders stay in a compact product box. -/
theorem suitableWeakSolution_activity_aemeasurable {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I q) (U : Set Space) (J : Set ℝ)
    (hUJ : IsOpen U ∧ CKNChallenge.IsCompactlyContained U Ω ∧
      OrdConnected J ∧ CKNChallenge.IsCompactlyContained J I)
    (hJ : MeasurableSet J) {E : Set SpaceTime} (hE : MeasurableSet E)
    (μ : Measure SpaceTime) (r : ℝ) (hsub : ∀ z ∈ E, symmetricL3Cylinder z r ⊆ U ×ˢ J) :
    AEMeasurable (fun z ↦ symmetricL3Activity sol.u sol.p z r) (μ.restrict E) ∧
      AEMeasurable (fun z ↦ symmetricMixedGradientActivity sol.Dxu z r) (μ.restrict E) := by
  have henergy := sol.energyRegularity U J hUJ
  have hS := hUJ.1.measurableSet.prod hJ
  exact ⟨aemeasurable_symmetricL3Activity_of_local hS hE μ
    henergy.velocityMemLp.aestronglyMeasurable henergy.pressureMemLp.aestronglyMeasurable
      r hsub,
    aemeasurable_symmetricMixedGradientActivity_of_local hS hE μ
      henergy.gradientMemLp.aestronglyMeasurable r hsub⟩

/-- The CKN array-gradient version of the unnormalized mixed integral. -/
def arrayMixedGradientIntegral (D : ParabolicPoint → Fin 3 → Vec3)
    (U : Set Vec3) (J : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in J, (∫⁻ x in U, ‖D (x, t)‖ₑ ^ (12 / 7 : ℝ)) ^ (7 / 6 : ℝ)

/-- The array mixed integral equals the time integral of the squared spatial critical
`eLpNorm`, whenever the array is jointly almost everywhere strongly measurable. -/
theorem arrayMixedGradientIntegral_eq_eLpNorm (D : ParabolicPoint → Fin 3 → Vec3)
    (U : Set Vec3) (J : Set ℝ)
    (hD : AEStronglyMeasurable D (volume.restrict (U ×ˢ J))) :
    arrayMixedGradientIntegral D U J =
      ∫⁻ t in J, eLpNorm (fun x ↦ D (x, t)) (12 / 7) (volume.restrict U) ^ (2 : ℝ) := by
  have hprod : AEStronglyMeasurable D
      ((volume.restrict U).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hD
  apply lintegral_congr_ae
  filter_upwards [aestronglyMeasurable_spatial_slice_ae hprod] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (12 / 7 : ℝ≥0∞) ≠ 0) (by finiteness : (12 / 7 : ℝ≥0∞) ≠ ∞) ht]
  norm_num
  have hrpow (a : ℝ≥0∞) : a ^ (7 / 6 : ℝ) = (a ^ (7 / 12 : ℝ)) ^ 2 := by
    have h := ENNReal.rpow_mul a (7 / 12 : ℝ) (2 : ℝ)
    norm_num at h
    exact h
  exact hrpow _

/-- Spatial Hölder and Tonelli control the CKN array mixed integral by its ordinary
quadratic energy, with the sixth-root volume factor. -/
theorem arrayMixedGradientIntegral_le_dissipation (D : ParabolicPoint → Fin 3 → Vec3)
    (U : Set Vec3) (J : Set ℝ)
    (hD : AEStronglyMeasurable D (volume.restrict (U ×ˢ J))) :
    arrayMixedGradientIntegral D U J ≤ volume U ^ (1 / 6 : ℝ) *
      ∫⁻ a in U ×ˢ J, ‖D a‖ₑ ^ (2 : ℝ) := by
  have hprod : AEStronglyMeasurable D
      ((volume.restrict U).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hD
  unfold arrayMixedGradientIntegral
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa only [Measure.restrict_apply_univ] using mixedGradientIntegral_le_dissipation hprod

/-- The mixed array cost is finite on every local box of an actual CKN suitable weak
solution, derived directly from the energy clauses of the solution class. -/
theorem rawSuitableWeakSolution_arrayMixedGradientIntegral_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (U : Set Vec3) (J : Set ℝ) (hbox : CKN.localBox Ω I U J) :
    arrayMixedGradientIntegral D U J < ⊤ := by
  obtain ⟨-, hD, -, -, -, henergy, -, -, -⟩ := hsol.2.2.2.2.2.1 U J hbox
  apply (arrayMixedGradientIntegral_le_dissipation D U J hD).trans_lt
  apply ENNReal.mul_lt_top
  · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact (lt_of_le_of_lt (measure_mono subset_closure) hbox.2.1.measure_lt_top).ne
  · exact (lintegral_mono fun _ ↦ le_add_left le_rfl).trans_lt henergy

end FluidSingularSets
