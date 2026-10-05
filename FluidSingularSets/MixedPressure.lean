-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.CriticalPoincare
public import CKN.Setting.VectorNormAggregation
public import CKN.Pressure.SliceIntegrability
public import CKN.Setting.Finiteness
public import CKN.Core.Endgame.Lin34Faithful
public import CKN.Setting.SliceNormBounds

/-!
# Mixed-gradient control of the mean-subtracted pressure source

The cubic source of the actual pressure decay estimate is controlled by critical
Sobolev–Poincaré and spatial Hölder with exponents two and four. The spatial
estimates keep the radius-independent constants explicit.

The mean and interpolation arguments adapt proofs by Scott Armstrong and Vlad
Vicol in the CKN library, distributed under the Apache 2.0 license.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Averaging contracts the norm of the corresponding constant function in any
finite Hölder exponent. -/
theorem averageConst_eLpNorm_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    eLpNorm (fun _ : α ↦ average μ f) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal p) μ := by
  have hp : 0 < p := hpq.pos
  have htop : μ univ ≠ ∞ := measure_ne_top μ univ
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    hf.enorm (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    one_mul] at hholder
  have hnorm := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hf
  rw [ENNReal.toReal_ofReal hp.le] at hnorm
  have havg : ‖average μ f‖ₑ = (μ univ)⁻¹ * ‖∫ x, f x ∂μ‖ₑ := by
    rw [average_eq, smul_eq_mul, enorm_mul, Real.enorm_eq_ofReal,
      ENNReal.ofReal_inv_of_pos, measureReal_def, ENNReal.ofReal_toReal htop]
    · exact ENNReal.toReal_pos hμ htop
    · positivity
  rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, havg]
  calc
    _ ≤ ((μ univ)⁻¹ * ∫⁻ x, ‖f x‖ₑ ∂μ) * (μ univ) ^ (1 / p) := by
      gcongr
      exact enorm_integral_le_lintegral_enorm f
    _ ≤ ((μ univ)⁻¹ *
        ((∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) * (μ univ) ^ (1 / q))) *
          (μ univ) ^ (1 / p) := by
      gcongr
    _ = eLpNorm f (ENNReal.ofReal p) μ := by
      rw [← hnorm]
      rw [show (μ univ)⁻¹ *
          (eLpNorm f (ENNReal.ofReal p) μ * μ univ ^ (1 / q)) * μ univ ^ (1 / p) =
          eLpNorm f (ENNReal.ofReal p) μ *
            ((μ univ)⁻¹ * μ univ ^ (1 / q) * μ univ ^ (1 / p)) by ring,
        ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hμ htop,
        ← ENNReal.rpow_add _ _ hμ htop]
      have hexp : (-1 : ℝ) + 1 / q + 1 / p = 0 := by
        have h := hpq.inv_add_inv_eq_one
        simp only [one_div] at h ⊢
        linarith only [h]
      rw [hexp, ENNReal.rpow_zero, mul_one]

/-- Subtracting the spatial average increases a finite Hölder norm by at most two. -/
theorem centered_eLpNorm_le_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    eLpNorm (fun x ↦ f x - average μ f) (ENNReal.ofReal p) μ ≤
      2 * eLpNorm f (ENNReal.ofReal p) μ := by
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal p) μ +
        eLpNorm (fun _ : α ↦ average μ f) (ENNReal.ofReal p) μ :=
      eLpNorm_sub_le (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hpq.lt.le)
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add le_rfl (averageConst_eLpNorm_le hμ hf hpq)

/-- Spatial Hölder bounds the cubic mass by one quadratic norm and the square
of the quartic norm. -/
theorem cubic_mass_le_L2_L4
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ^ (3 : ℝ) ∂μ) ≤
      eLpNorm f 2 μ * eLpNorm f 4 μ ^ (2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    hf.enorm (hf.enorm.pow_const 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num) hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num) hf]
  simp only [← ENNReal.rpow_mul] at h ⊢
  norm_num at h ⊢
  convert h using 1
  · apply lintegral_congr
    intro x
    simp only [pow_succ, pow_zero, mul_comm]
  · simp only [← pow_mul]

/-- Absolute coefficient for the cubic mean-subtracted pressure source. -/
def criticalCubicOscillationConstant : ℝ≥0∞ :=
  8 * criticalSobolevPoincareConstant ^ (2 : ℝ)

/-- A local weak representative's cubic mean oscillation is controlled by its
quadratic velocity norm and mixed-gradient norm, with an absolute coefficient. -/
theorem weakCriticalCubicOscillationBall
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (4 * r))))
    (hDu : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (4 * r))))
    (hweak : HasWeakGradientOn (euclideanBall x₀ (4 * r)) u Du)
    (hu2 : MemLp u 2 (volume.restrict (euclideanBall x₀ r))) :
    (∫⁻ x in euclideanBall x₀ r,
        ‖u x - integralAverage (euclideanBall x₀ r) u‖ₑ ^ (3 : ℝ)) ≤
      criticalCubicOscillationConstant *
        eLpNorm u 2 (volume.restrict (euclideanBall x₀ r)) *
        eLpNorm Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))) ^
          (2 : ℝ) := by
  let μ := volume.restrict (euclideanBall x₀ r)
  let b := integralAverage (euclideanBall x₀ (2 * r)) u
  let v := fun x ↦ u x - b
  let : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_euclideanBall_lt_top x₀ hr
  have hμ : μ univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact (volume_euclideanBall_pos x₀ hr).ne'
  let : NeZero μ := ⟨by
    intro hzero
    apply hμ
    rw [hzero]
    simp⟩
  have hv : AEStronglyMeasurable v μ := hu2.aestronglyMeasurable.sub
    aestronglyMeasurable_const
  have havg : average μ v = average μ u - b := by
    change average μ (u - fun _ ↦ b) = average μ u - b
    rw [average_sub (hu2.integrable (by norm_num)) (integrable_const b),
      average_const]
  have hL4 : eLpNorm (fun x ↦ u x - average μ u) 4 μ ≤
      2 * criticalSobolevPoincareConstant *
        eLpNorm Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))) := by
    have hc := centered_eLpNorm_le_two hμ hv
      (show (4 : ℝ).HolderConjugate (4 / 3) by constructor <;> norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hc
    have hsob := weakCriticalSobolevPoincareBall hr hu hDu hweak
    have heq : (fun x ↦ v x - average μ v) = (fun x ↦ u x - average μ u) := by
      funext x
      rw [havg]
      dsimp [v]
      ring
    rw [heq] at hc
    apply hc.trans
    show 2 * eLpNorm v 4 μ ≤ _
    exact (by
      unfold lpNormOn weakGradientLpNormOn at hsob
      simpa [mul_assoc, v, b, μ] using mul_le_mul' (le_refl (2 : ℝ≥0∞)) hsob)
  have hL2 := centered_eLpNorm_le_two hμ hu2.aestronglyMeasurable
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
  norm_num only [ENNReal.ofReal_ofNat] at hL2
  have hc := cubic_mass_le_L2_L4 (μ := μ) (f := fun x ↦ u x - average μ u)
    (hu2.aestronglyMeasurable.sub aestronglyMeasurable_const)
  calc
    _ ≤ eLpNorm (fun x ↦ u x - average μ u) 2 μ *
        eLpNorm (fun x ↦ u x - average μ u) 4 μ ^ (2 : ℝ) := hc
    _ ≤ (2 * eLpNorm u 2 μ) *
        (2 * criticalSobolevPoincareConstant *
          eLpNorm Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r)))) ^
            (2 : ℝ) := by
      gcongr
    _ = _ := by
      unfold criticalCubicOscillationConstant
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      ring

/-- Absolute Euclidean coefficient after summing the three scalar oscillations. -/
def criticalVectorCubicOscillationConstant : ℝ≥0∞ :=
  3 * ENNReal.ofReal (Real.sqrt 3) * criticalCubicOscillationConstant

/-- The cubic oscillation coefficient is finite. -/
theorem criticalVectorCubicOscillationConstant_ne_top :
    criticalVectorCubicOscillationConstant ≠ ∞ := by
  unfold criticalVectorCubicOscillationConstant criticalCubicOscillationConstant
  finiteness [criticalSobolevPoincareConstant_ne_top]

/-- The cubic Euclidean velocity oscillation is controlled by the quadratic
velocity norm and the mixed-gradient matrix norm. -/
theorem weakCriticalVectorCubicOscillationBall
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (4 * r))))
    (hDu : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (4 * r))))
    (hweak : ∀ i : Fin 3, HasWeakGradientOn (euclideanBall x₀ (4 * r))
      (fun x ↦ u x i) (fun x ↦ Du x i))
    (hu2 : MemLp u 2 (volume.restrict (euclideanBall x₀ r))) :
    (∫⁻ x in euclideanBall x₀ r,
        ENNReal.ofReal (vec3EuclideanNorm
          (fun i ↦ u x i - integralAverage (euclideanBall x₀ r) (fun y ↦ u y i))) ^
          (3 : ℝ)) ≤
      criticalVectorCubicOscillationConstant *
        eLpNorm u 2 (volume.restrict (euclideanBall x₀ r)) *
        eLpNorm Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))) ^
          (2 : ℝ) := by
  let B := euclideanBall x₀ r
  let B₂ := euclideanBall x₀ (2 * r)
  let V := fun x i ↦ u x i - integralAverage B (fun y ↦ u y i)
  have hB₂sub : B₂ ⊆ euclideanBall x₀ (4 * r) := by
    intro x hx
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)]
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : 0 < 2 * r)).1 hx
    linarith only [hx', hr]
  have hDu₂ := hDu.mono_measure (Measure.restrict_mono_set volume hB₂sub)
  have hmeas (i : Fin 3) : AEMeasurable (fun x ↦ V x i) (volume.restrict B) :=
    ((MemLp.eval hu2 i).aestronglyMeasurable.sub aestronglyMeasurable_const).aemeasurable
  have hscalar (i : Fin 3) : (∫⁻ x in B, ‖V x i‖ₑ ^ (3 : ℝ)) ≤
      criticalCubicOscillationConstant * eLpNorm u 2 (volume.restrict B) *
        eLpNorm Du (12 / 7) (volume.restrict B₂) ^ (2 : ℝ) := by
    have h := weakCriticalCubicOscillationBall hr (MemLp.eval hu i)
      (MemLp.eval hDu i) (hweak i) (MemLp.eval hu2 i)
    apply h.trans
    gcongr
    · exact eLpNorm_mono_ae (MemLp.eval hu2 i).aestronglyMeasurable
        (Eventually.of_forall (fun x ↦ norm_le_pi_norm (u x) i))
    · exact eLpNorm_mono_ae (MemLp.eval hDu₂ i).aestronglyMeasurable
        (Eventually.of_forall (fun x ↦ norm_le_pi_norm (Du x) i))
  have hv := lintegral_vec3EuclideanNorm_rpow_le_sum (s := B) (u := V)
    (p := (3 : ℝ)) (by norm_num) hmeas
  have hpow : (3 : ℝ) ^ max 0 ((3 : ℝ) / 2 - 1) = Real.sqrt 3 := by
    rw [show max 0 ((3 : ℝ) / 2 - 1) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  rw [hpow] at hv
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt 3) *
        ∑ i : Fin 3, ∫⁻ x in B, ‖V x i‖ₑ ^ (3 : ℝ) := hv
    _ ≤ ENNReal.ofReal (Real.sqrt 3) * ∑ _i : Fin 3,
        criticalCubicOscillationConstant * eLpNorm u 2 (volume.restrict B) *
          eLpNorm Du (12 / 7) (volume.restrict B₂) ^ (2 : ℝ) := by
      gcongr with i
      exact hscalar i
    _ = _ := by
      unfold criticalVectorCubicOscillationConstant
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The actual suitable weak solution has critical cubic oscillation control on
almost every time slice, without a separate Sobolev or pressure-estimate assumption. -/
theorem suitableCubicOscillationSlices
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * r)) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - r ^ 2) z.2),
      MemLp (fun x ↦ u (x, s)) 2 (volume.restrict (vec3Ball z.1 r)) ∧
      (∫⁻ x in vec3Ball z.1 r,
          ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u z.1 r s x)) ^ (3 : ℝ)) ≤
        criticalVectorCubicOscillationConstant *
          eLpNorm (fun x ↦ u (x, s)) 2 (volume.restrict (vec3Ball z.1 r)) *
          eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
            (volume.restrict (vec3Ball z.1 (2 * r))) ^ (2 : ℝ) := by
  have hr4 : 0 < 4 * r := by positivity
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hr4 hsub
  have hball4 : vec3Ball z.1 (4 * r) ⊆ Ω' := by
    intro x hx
    have hxcy : (x, z.2) ∈ parabolicCylinder z.1 z.2 (4 * r) := by
      rw [mem_parabolicCylinder]
      exact ⟨hx, by nlinarith only [sq_pos_of_pos hr4], le_rfl⟩
    exact (hcyl hxcy).1
  have htime : Ioc (z.2 - r ^ 2) z.2 ⊆ J := by
    intro s hs
    have hcenter : z.1 ∈ vec3Ball z.1 (4 * r) := by
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hr4
    have hsCy : (z.1, s) ∈ parabolicCylinder z.1 z.2 (4 * r) := by
      rw [mem_parabolicCylinder]
      exact ⟨hcenter, by nlinarith only [hs.1, sq_pos_of_pos hr], hs.2⟩
    exact (hcyl hsCy).2
  have hslices := ae_restrict_of_ae_restrict_of_subset htime
    (slice_memLp_ae_of_sws hsol hbox)
  obtain ⟨_hu, _hDu, _hp, _hf, _hess, _henergy, _hp', _hf', hgrad⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hweak := ae_restrict_of_ae_restrict_of_subset htime (ae_all_iff.mpr hgrad)
  have hballEq4 := euclideanBall_eq_vec3Ball (x₀ := z.1) hr4
  have hballEq2 := euclideanBall_eq_vec3Ball (x₀ := z.1)
    (by positivity : 0 < 2 * r)
  have hballEq := euclideanBall_eq_vec3Ball (x₀ := z.1) hr
  have hBsub : vec3Ball z.1 r ⊆ vec3Ball z.1 (4 * r) :=
    vec3Ball_mono (by linarith only [hr])
  let : IsFiniteMeasure (volume.restrict (vec3Ball z.1 (4 * r))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_vec3Ball_lt_top
  filter_upwards [hslices, hweak] with s hs hw
  have hu4 := hs.1.mono_measure (Measure.restrict_mono_set volume hball4)
  have hDu4 := hs.2.mono_measure (Measure.restrict_mono_set volume hball4)
  have hcrit : (12 / 7 : ℝ≥0∞) ≤ 2 := by
    rw [ENNReal.div_le_iff (by norm_num : (7 : ℝ≥0∞) ≠ 0) (by norm_num)]
    norm_num
  have huCrit := hu4.mono_exponent hcrit
  have hDuCrit := hDu4.mono_exponent hcrit
  have hu2 := hu4.mono_measure (Measure.restrict_mono_set volume hBsub)
  have hw4 (i : Fin 3) : HasWeakGradientOn (euclideanBall z.1 (4 * r))
      (fun x ↦ u (x, s) i) (fun x ↦ Du (x, s) i) := by
    apply (hw i).mono (isOpen_euclideanBall z.1 (4 * r))
    rw [hballEq4]
    exact hball4
  have h := weakCriticalVectorCubicOscillationBall hr
    (by simpa only [hballEq4] using huCrit) (by simpa only [hballEq4] using hDuCrit)
    hw4 (by simpa only [hballEq] using hu2)
  refine ⟨hu2, ?_⟩
  unfold meanFreeVec meanFreeComponent
  simpa only [hballEq2, hballEq, integralAverage] using h

/-- Integrating the actual cubic oscillation slices uses only the genuine
quadratic time-energy supremum and the mixed-gradient energy. -/
theorem suitableCubicOscillationMass
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * r)) ⊆ spaceTimeSet Ω I) :
    (∫⁻ s in Ioc (z.2 - r ^ 2) z.2, ∫⁻ x in vec3Ball z.1 r,
        ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u z.1 r s x)) ^ (3 : ℝ)) ≤
      criticalVectorCubicOscillationConstant *
        timeSliceEnergyEssSup z.1 z.2 (2 * r) (fun w ↦ vec3EuclideanNorm (u w)) ^
          (1 / 2 : ℝ) *
        ∫⁻ s in Ioc (z.2 - (2 * r) ^ 2) z.2,
          eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
            (volume.restrict (vec3Ball z.1 (2 * r))) ^ (2 : ℝ) := by
  let T := Ioc (z.2 - r ^ 2) z.2
  let T₂ := Ioc (z.2 - (2 * r) ^ 2) z.2
  let E := timeSliceEnergyEssSup z.1 z.2 (2 * r)
    (fun w ↦ vec3EuclideanNorm (u w))
  have hT : T ⊆ T₂ := by
    intro s hs
    exact ⟨by nlinarith only [hs.1, sq_pos_of_pos hr], hs.2⟩
  have hsub₂ : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity) (by linarith only [hr]))).trans
      hsub
  have hE : E ≠ ∞ := (sws_timeSliceEnergyEssSup_lt_top hsol (by positivity) hsub₂).ne
  have henergy := ae_restrict_of_ae_restrict_of_subset hT
    (ENNReal.ae_le_essSup (μ := volume.restrict T₂)
      (fun s ↦ timeSliceBallEnergy z.1 (2 * r) s (fun w ↦ vec3EuclideanNorm (u w))))
  have hslices := suitableCubicOscillationSlices hsol hr hsub
  have hnorm (v : Vec3) : ‖v‖ ≤ vec3EuclideanNorm v := by
    simpa only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      pi_norm_le_vecEuclideanNorm v
  have hpoint : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ x in vec3Ball z.1 r,
          ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u z.1 r s x)) ^ (3 : ℝ)) ≤
        criticalVectorCubicOscillationConstant * E ^ (1 / 2 : ℝ) *
          eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
            (volume.restrict (vec3Ball z.1 (2 * r))) ^ (2 : ℝ) := by
    filter_upwards [hslices, henergy] with s hs he
    have hL2 : eLpNorm (fun x ↦ u (x, s)) 2 (volume.restrict (vec3Ball z.1 r)) ≤
        E ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num) hs.1.aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply le_trans _ he
      calc
        _ ≤ ∫⁻ x in vec3Ball z.1 r, ‖vec3EuclideanNorm (u (x, s))‖ₑ ^ (2 : ℝ) := by
          apply lintegral_mono
          intro x
          apply ENNReal.rpow_le_rpow _ (by norm_num)
          rw [enorm_le_iff_norm_le, Real.norm_eq_abs,
            abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
          exact hnorm (u (x, s))
        _ ≤ _ := lintegral_mono_set (vec3Ball_mono (by linarith only [hr]))
    exact hs.2.trans (by gcongr)
  calc
    _ ≤ ∫⁻ s in T, criticalVectorCubicOscillationConstant * E ^ (1 / 2 : ℝ) *
        eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
          (volume.restrict (vec3Ball z.1 (2 * r))) ^ (2 : ℝ) := lintegral_mono_ae hpoint
    _ = criticalVectorCubicOscillationConstant * E ^ (1 / 2 : ℝ) *
        ∫⁻ s in T, eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
          (volume.restrict (vec3Ball z.1 (2 * r))) ^ (2 : ℝ) := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
        criticalVectorCubicOscillationConstant_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE))]
    _ ≤ _ := by
      gcongr

/-- The actual pressure source quantity is controlled by the mixed-gradient
energy and the genuine quadratic energy supremum. -/
theorem suitablePressureChatMixedBound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * ρ)) ⊆ spaceTimeSet Ω I) :
    ENNReal.ofReal (pressureChat u z ρ) ≤
      ENNReal.ofReal (ρ⁻¹ ^ 2) * criticalVectorCubicOscillationConstant *
        timeSliceEnergyEssSup z.1 z.2 (2 * ρ) (fun w ↦ vec3EuclideanNorm (u w)) ^
          (1 / 2 : ℝ) *
        ∫⁻ s in Ioc (z.2 - (2 * ρ) ^ 2) z.2,
          eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
            (volume.restrict (vec3Ball z.1 (2 * ρ))) ^ (2 : ℝ) := by
  have hsubρ : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono hρ.le (by linarith only [hρ]))).trans hsub
  have hc := lin34_integrableOn_meanFree_cube hρ
    (tsai_integrable_velocity_on_cylinder hsol hρ hsubρ)
    (tsai_integrable_velocity_cube_on_cylinder hsol hρ hsubρ)
  let V := fun w : ParabolicPoint ↦ vec3EuclideanNorm (meanFreeVec u z.1 ρ w.2 w.1)
  have hnonneg : ∀ w, 0 ≤ V w := fun w ↦ vec3EuclideanNorm_nonneg _
  have hpow (w : ParabolicPoint) : ENNReal.ofReal (V w) ^ (3 : ℝ) =
      ENNReal.ofReal (V w ^ (3 : ℕ)) := by
    norm_num only [ENNReal.rpow_ofNat]
    exact (ENNReal.ofReal_pow (hnonneg w) 3).symm
  have hmeas : AEMeasurable (fun w ↦ ENNReal.ofReal (V w) ^ (3 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    simp_rw [hpow]
    exact hc.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmass : ENNReal.ofReal
      (∫ w in parabolicCylinder z.1 z.2 ρ, V w ^ (3 : ℕ)) =
        ∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ∫⁻ x in vec3Ball z.1 ρ,
          ENNReal.ofReal (V (x, s)) ^ (3 : ℝ) := by
    calc
      _ = ∫⁻ w in parabolicCylinder z.1 z.2 ρ,
          ENNReal.ofReal (V w ^ (3 : ℕ)) :=
        ofReal_integral_eq_lintegral_ofReal hc
          (Eventually.of_forall (fun w ↦ pow_nonneg (hnonneg w) 3))
      _ = ∫⁻ w in parabolicCylinder z.1 z.2 ρ, ENNReal.ofReal (V w) ^ (3 : ℝ) := by
        simp_rw [hpow]
      _ = _ := lintegral_parabolicCylinder hmeas
  unfold pressureChat
  rw [ENNReal.ofReal_mul (sq_nonneg _), hmass]
  have hbound := suitableCubicOscillationMass hsol hρ hsub
  simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal (ρ⁻¹ ^ 2))) hbound

/-- The actual unforced pressure obeys a mixed-gradient decay estimate. The
coefficient is the absolute real constant from the proved CKN pressure decomposition;
the new oscillation term has no additional analytic-estimate hypothesis. -/
theorem suitablePressureMixedDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * ρ)) ⊆ spaceTimeSet Ω I) :
    ENNReal.ofReal (pressureD p z r) ≤
      ENNReal.ofReal lin34AbsoluteConstant *
        (ENNReal.ofReal ((ρ / r) ^ 2) *
          (ENNReal.ofReal (ρ⁻¹ ^ 2) * criticalVectorCubicOscillationConstant *
            timeSliceEnergyEssSup z.1 z.2 (2 * ρ)
              (fun w ↦ vec3EuclideanNorm (u w)) ^ (1 / 2 : ℝ) *
            ∫⁻ s in Ioc (z.2 - (2 * ρ) ^ 2) z.2,
              eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
                (volume.restrict (vec3Ball z.1 (2 * ρ))) ^ (2 : ℝ)) +
          ENNReal.ofReal (r / ρ) * ENNReal.ofReal (pressureD p z ρ)) := by
  have hsubρ : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono hρ.le (by linarith only [hρ]))).trans hsub
  have hforce : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w ↦ ∑ i : Fin 3, (0 : Vec3) i * spatialPartial ψ i w)
          (tsupport ψ) volume ∧
        (∫ w in spaceTimeSet Ω I, ∑ i : Fin 3, (0 : Vec3) i * spatialPartial ψ i w) = 0 :=
    by intro ψ hψ; simp
  have hpressure := ((CKN.pressure_lin34_of_sws q hsol hρ hr hhalf hsubρ).1 hforce).2
  have hC : 0 ≤ lin34AbsoluteConstant := by
    exact (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg).trans (le_max_left _ _)
  have hChat : 0 ≤ pressureChat u z ρ := by
    unfold pressureChat
    exact mul_nonneg (sq_nonneg _)
      (integral_nonneg (fun _ ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3))
  have hD : 0 ≤ pressureD p z ρ := by
    unfold pressureD
    exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ ↦ by positivity))
  have hbound := ENNReal.ofReal_le_ofReal hpressure
  rw [ENNReal.ofReal_mul hC,
    ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) hChat)
      (mul_nonneg (div_nonneg hr.le hρ.le) hD),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (div_nonneg hr.le hρ.le)] at hbound
  apply hbound.trans
  gcongr
  exact suitablePressureChatMixedBound hsol hρ hsub

end FluidSingularSets
