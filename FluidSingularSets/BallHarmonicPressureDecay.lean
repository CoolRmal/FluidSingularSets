-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallStokesPressureSources
public import FluidSingularSets.HarmonicPressureOscillation
public import FluidSingularSets.MixedPressure

/-!
# Genuine pressure decay on arbitrary spatial balls

Actual affine changes of variables preserve the weak Laplacian equation and
the literal centered spatial L² seminorm. This transports the proved harmonic
oscillation estimate to balls of arbitrary positive radius. The difference
between the genuine large-ball and local convective pressures is harmonic
because their actual compact-test Poisson pairings agree.
-/

@[expose] public section

open CKN MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The genuine first spatial derivative of a smooth scalar affine pullback. -/
theorem spatialDeriv_ballAffine {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec3) (a : ℝ) (i : Fin 3) (y : Vec3) :
    spatialDeriv (φ ∘ CKN.spatialAffine a x) i y =
      a * spatialDeriv φ i (CKN.spatialAffine a x y) := by
  have ha := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul a).const_add x
  have hd := (hφ.differentiable (by simp)).differentiableAt
    (x := CKN.spatialAffine a x y) |>.hasFDerivAt
  unfold spatialDeriv
  rw [(hd.comp y ha).fderiv]
  simp [CKN.spatialAffine]

/-- The actual smooth Hessian has the square affine scale factor. -/
theorem mixedSecond_ballAffine {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec3) (a : ℝ)
    (i j : Fin 3) (y : Vec3) :
    mixedSecond (φ ∘ CKN.spatialAffine a x) i j y =
      a ^ 2 * mixedSecond φ i j (CKN.spatialAffine a x y) := by
  have he : spatialDeriv (φ ∘ CKN.spatialAffine a x) j =
      fun z ↦ a * spatialDeriv φ j (CKN.spatialAffine a x z) := by
    funext z
    exact spatialDeriv_ballAffine hφ x a j z
  have hd : DifferentiableAt ℝ
      ((spatialDeriv φ j) ∘ CKN.spatialAffine a x) y :=
    ((contDiff_spatialDeriv_smooth hφ j).comp
      (by unfold CKN.spatialAffine; fun_prop)).differentiable (by simp) y
  unfold mixedSecond
  rw [he]
  change (fderiv ℝ (fun z ↦ a *
    ((spatialDeriv φ j) ∘ CKN.spatialAffine a x) z) y) (basisVec i) = _
  rw [fderiv_const_mul hd a]
  change a * spatialDeriv ((spatialDeriv φ j) ∘ CKN.spatialAffine a x) i y = _
  rw [spatialDeriv_ballAffine (contDiff_spatialDeriv_smooth hφ j)]
  ring

/-- The literal Laplacian of a smooth affine pullback has the square scale factor. -/
theorem spatialLaplacian_ballAffine {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec3) (a : ℝ) (y : Vec3) :
    spatialLaplacian (φ ∘ CKN.spatialAffine a x) y =
      a ^ 2 * spatialLaplacian φ (CKN.spatialAffine a x y) := by
  change (∑ i : Fin 3, mixedSecond (φ ∘ CKN.spatialAffine a x) i i y) = _
  simp_rw [mixedSecond_ballAffine hφ x a]
  exact (Finset.mul_sum ..).symm

/-- Inverse-coordinate compact tests have their actual reciprocal Laplacian factor. -/
theorem ballTestPushforward_laplacian (x : Vec3) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (vec3Ball 0 1)) (y : Vec3) :
    spatialLaplacian (ballTestPushforward x hr φ).toFun y =
      r⁻¹ ^ 2 * spatialLaplacian φ.toFun (ballCoordinates x r y) := by
  have he : ballCoordinates x r = CKN.spatialAffine r⁻¹ (-(r⁻¹ • x)) := by
    funext z
    simp [ballCoordinates, CKN.spatialAffine, smul_sub]
    abel
  change spatialLaplacian (φ.toFun ∘ ballCoordinates x r) y = _
  rw [he]
  exact spatialLaplacian_ballAffine φ.contDiff _ _ y

/-- Literal integrals, with no chosen representative, have the actual affine Jacobian. -/
theorem ballAffine_integral (x : Vec3) {r : ℝ} (hr : 0 < r) (f : Vec3 → ℝ) :
    (∫ y in vec3Ball 0 1, f (CKN.spatialAffine r x y)) =
      r⁻¹ ^ 3 * ∫ y in vec3Ball x r, f y := by
  rw [← (ballAffine_measurableEmbedding x hr).integral_map,
    map_ballAffine_restrict x hr, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ r⁻¹ ^ 3 by positivity), smul_eq_mul]

/-- Genuine weak harmonicity is preserved by a positive-radius affine pullback. -/
theorem weaklyHarmonicOn_ballAffine {h : Vec3 → ℝ}
    (x : Vec3) {r : ℝ} (hr : 0 < r)
    (hh : WeaklyHarmonicOn (vec3Ball x r) h) :
    WeaklyHarmonicOn (vec3Ball 0 1) (h ∘ CKN.spatialAffine r x) := by
  intro ψ hψ hcompact hsub
  let φ : WeakTestFunction (vec3Ball 0 1) := ⟨ψ, hψ, hcompact, hsub⟩
  let η := ballTestPushforward x hr φ
  have hz := hh η.toFun η.contDiff η.hasCompactSupport η.tsupport_subset
  have he : (∫ y in vec3Ball 0 1,
      (h ∘ CKN.spatialAffine r x) y * spatialLaplacian ψ y) =
      r ^ 2 * ∫ y in vec3Ball 0 1,
        (fun z ↦ h z * spatialLaplacian η.toFun z) (CKN.spatialAffine r x y) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      dsimp only [Function.comp_apply, η]
      rw [ballTestPushforward_laplacian, ballCoordinates_affine x y hr]
      change h (CKN.spatialAffine r x y) * spatialLaplacian ψ y =
        r ^ 2 * (h (CKN.spatialAffine r x y) * (r⁻¹ ^ 2 * spatialLaplacian ψ y))
      field_simp
  rw [he]
  calc
    _ = r ^ 2 * (r⁻¹ ^ 3 * ∫ z in vec3Ball x r,
        h z * spatialLaplacian η.toFun z) :=
      congrArg (fun a : ℝ ↦ r ^ 2 * a)
        (ballAffine_integral x hr (fun z ↦ h z * spatialLaplacian η.toFun z))
    _ = 0 := by rw [hz, mul_zero, mul_zero]

/-- The genuine affine pullback of finite L² data is finite L² data. -/
theorem memLp_two_ballAffine {h : Vec3 → ℝ} (x : Vec3) {r : ℝ} (hr : 0 < r)
    (hh : MemLp h 2 (volume.restrict (vec3Ball x r))) :
    MemLp (h ∘ CKN.spatialAffine r x) 2 (volume.restrict (vec3Ball 0 1)) := by
  apply (ballAffine_measurableEmbedding x hr).memLp_map_measure_iff.mp
  rw [map_ballAffine_restrict x hr]
  exact hh.smul_measure ENNReal.ofReal_ne_top

/-- The genuine affine spatial L² seminorm has its exact reciprocal Jacobian. -/
theorem eLpNorm_two_ballAffine (x : Vec3) {r : ℝ} (hr : 0 < r) (h : Vec3 → ℝ) :
    eLpNorm (h ∘ CKN.spatialAffine r x) 2 (volume.restrict (vec3Ball 0 1)) =
      ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) *
        eLpNorm h 2 (volume.restrict (vec3Ball x r)) := by
  rw [← (ballAffine_measurableEmbedding x hr).eLpNorm_map_measure,
    map_ballAffine_restrict x hr,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  norm_num

/-- Affine transport maps every smaller concentric ball exactly to its physical ball. -/
theorem ballAffine_preimage_scaled (x : Vec3) {R : ℝ} (hR : 0 < R) (s : ℝ) :
    CKN.spatialAffine R x ⁻¹' vec3Ball x (R * s) = vec3Ball 0 s := by
  ext y
  simp only [mem_preimage, mem_vec3Ball, CKN.spatialAffine, add_sub_cancel_left,
    sub_zero, vec3EuclideanNorm_smul, abs_of_pos hR]
  exact mul_lt_mul_iff_right₀ hR

/-- The genuine affine Jacobian applies to all concentric restricted spatial balls. -/
theorem map_ballAffine_restrict_scaled (x : Vec3) {R : ℝ} (hR : 0 < R) (s : ℝ) :
    Measure.map (CKN.spatialAffine R x) (volume.restrict (vec3Ball 0 s)) =
      ENNReal.ofReal (R⁻¹ ^ 3) • volume.restrict (vec3Ball x (R * s)) := by
  have he := Measure.restrict_map (μ := (volume : Measure Vec3))
    (ballAffine_measurableEmbedding x hR).measurable (vec3Ball_measurable x (R * s))
  rw [map_ballAffine_volume x hR, Measure.restrict_smul,
    ballAffine_preimage_scaled x hR s] at he
  exact he.symm

/-- Positive finite rescaling of a measure preserves its literal average. -/
theorem average_ofReal_smul_measure {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    average (ENNReal.ofReal c • μ) f = average μ f := by
  rw [average_eq, average_eq, integral_smul_measure]
  simp only [measureReal_def, Measure.smul_apply, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  rw [mul_inv_rev]
  calc
    _ = (μ univ).toReal⁻¹ * (c⁻¹ * c) * ∫ a, f a ∂μ := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc.ne', mul_one]

/-- The actual average of an affine pullback is the actual physical-ball average. -/
theorem average_ballAffine_scaled (x : Vec3) {R : ℝ} (hR : 0 < R)
    (s : ℝ) (h : Vec3 → ℝ) :
    average (volume.restrict (vec3Ball 0 s)) (h ∘ CKN.spatialAffine R x) =
      average (volume.restrict (vec3Ball x (R * s))) h := by
  have he := (ballAffine_measurableEmbedding x hR).integral_map
    (μ := volume.restrict (vec3Ball 0 s)) h
  have hm : (Measure.map (CKN.spatialAffine R x)
      (volume.restrict (vec3Ball 0 s))).real univ =
      (volume.restrict (vec3Ball 0 s)).real univ := by
    rw [measureReal_def, Measure.map_apply
      (ballAffine_measurableEmbedding x hR).measurable MeasurableSet.univ]
    simp only [preimage_univ, measureReal_def]
  have ha : average (volume.restrict (vec3Ball 0 s))
      (h ∘ CKN.spatialAffine R x) =
      average (Measure.map (CKN.spatialAffine R x)
        (volume.restrict (vec3Ball 0 s))) h := by
    rw [average_eq, average_eq, hm, he]
    rfl
  rw [ha, map_ballAffine_restrict_scaled x hR s]
  exact average_ofReal_smul_measure _ h (by positivity)

/-- The centered L² seminorm transforms with its genuine square-root spatial Jacobian. -/
theorem centered_eLpNorm_two_ballAffine_scaled (x : Vec3) {R : ℝ} (hR : 0 < R)
    (s : ℝ) (h : Vec3 → ℝ) :
    eLpNorm (fun y ↦ (h ∘ CKN.spatialAffine R x) y -
        average (volume.restrict (vec3Ball 0 s)) (h ∘ CKN.spatialAffine R x)) 2
      (volume.restrict (vec3Ball 0 s)) =
      ENNReal.ofReal (R⁻¹ ^ 3) ^ (1 / 2 : ℝ) *
        eLpNorm (fun y ↦ h y - average (volume.restrict (vec3Ball x (R * s))) h) 2
          (volume.restrict (vec3Ball x (R * s))) := by
  rw [average_ballAffine_scaled x hR s h]
  change eLpNorm ((fun y ↦ h y -
    average (volume.restrict (vec3Ball x (R * s))) h) ∘ CKN.spatialAffine R x) 2 _ = _
  rw [← (ballAffine_measurableEmbedding x hR).eLpNorm_map_measure,
    map_ballAffine_restrict_scaled x hR s,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  norm_num

/-- Actual harmonic pressure on any ball has the true relative-radius centered L² decay. -/
theorem ballHarmonic_centered_eLpNorm_two_decay {h : Vec3 → ℝ}
    (x : Vec3) {R : ℝ} (hR : 0 < R)
    (hmem : MemLp h 2 (volume.restrict (vec3Ball x R)))
    (hweak : WeaklyHarmonicOn (vec3Ball x R) h)
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    eLpNorm (fun y ↦ h y - average (volume.restrict (vec3Ball x (R * s))) h) 2
        (volume.restrict (vec3Ball x (R * s))) ≤
      fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ) *
        eLpNorm h 2 (volume.restrict (vec3Ball x R)) := by
  have hb := fullBallHarmonic_centered_eLpNorm_two_decay
    (memLp_two_ballAffine x hR hmem) (weaklyHarmonicOn_ballAffine x hR hweak) hs hsρ hρ
  rw [centered_eLpNorm_two_ballAffine_scaled x hR s,
    eLpNorm_two_ballAffine x hR] at hb
  have hc : 0 < ENNReal.ofReal (R⁻¹ ^ 3) ^ (1 / 2 : ℝ) := by positivity
  have hct : ENNReal.ofReal (R⁻¹ ^ 3) ^ (1 / 2 : ℝ) ≠ ∞ := by finiteness
  exact (ENNReal.mul_le_mul_iff_left hc.ne' hct).mp
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb)

/-- The Laplacian of a genuine compact test vanishes outside its actual domain. -/
theorem integral_laplacian_test_eq_integral {U : Set Vec3}
    (ψ : WeakTestFunction U) (p : Vec3 → ℝ) :
    (∫ y in U, p y * spatialLaplacian ψ.toFun y) =
      ∫ y, p y * spatialLaplacian ψ.toFun y := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hz := stokesWeakTest_eq_zero_outside (stokesWeakTestLaplacian ψ) hy
  change spatialLaplacian ψ.toFun y = 0 at hz
  rw [hz, mul_zero]

/-- Every genuine Hessian-test pairing vanishes outside the compact test domain. -/
theorem integral_hessian_test_eq_integral {U : Set Vec3}
    (ψ : WeakTestFunction U) (T : Vec3 → Fin 3 × Fin 3 → ℝ) :
    (∫ y in U, ∑ ij : Fin 3 × Fin 3,
      T y ij * mixedSecond ψ.toFun ij.1 ij.2 y) =
      ∫ y, ∑ ij : Fin 3 × Fin 3, T y ij * mixedSecond ψ.toFun ij.1 ij.2 y := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  apply Finset.sum_eq_zero
  intro ij _
  have hz := stokesWeakTest_eq_zero_outside
    (stokesWeakTestDerivative (stokesWeakTestDerivative ψ ij.2) ij.1) hy
  change mixedSecond ψ.toFun ij.1 ij.2 y = 0 at hz
  rw [hz, mul_zero]

/-- Actual large-ball and local convective pressures differ by a harmonic function. -/
theorem ballNonlinearPressure_local_difference_weaklyHarmonic
    (x : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x R))) :
    WeaklyHarmonicOn (vec3Ball x r)
      (fun y ↦ ballNonlinearPressure x hR u hu y -
        ballNonlinearPressure x hr u
          (hu.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)) y) := by
  let hur := hu.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)
  apply weaklyHarmonicOn_sub_of_laplacian_pairings_eq
    ((Lp.memLp (ballNonlinearPressure x hR u hu)).mono_measure
      (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl))
    (Lp.memLp (ballNonlinearPressure x hr u hur))
  intro ψ
  let η : WeakTestFunction (vec3Ball x R) :=
    ⟨ψ.toFun, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans (vec3Ball_mono hrR)⟩
  have hp := (ballNonlinearPressure_poisson x hR u hu η).2
  have hq := (ballNonlinearPressure_poisson x hr u hur ψ).2
  rw [integral_laplacian_test_eq_integral η,
    integral_hessian_test_eq_integral η] at hp
  rw [integral_laplacian_test_eq_integral ψ,
    integral_hessian_test_eq_integral ψ] at hq
  simp_rw [integral_laplacian_test_eq_integral ψ]
  exact hp.trans hq.symm

/-- The actual centered convective pressure decays after local pressure subtraction. -/
theorem ballNonlinearPressure_centered_local_decay
    (x : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x R)))
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    let q := ballNonlinearPressure x hR u hu
    let p := ballNonlinearPressure x hr u
      (hu.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl))
    eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball x (r * s))) q) 2
        (volume.restrict (vec3Ball x (r * s))) ≤
      2 * eLpNorm p 2 (volume.restrict (vec3Ball x r)) +
        fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ) *
          (eLpNorm q 2 (volume.restrict (vec3Ball x r)) +
            eLpNorm p 2 (volume.restrict (vec3Ball x r))) := by
  dsimp only
  let q : Vec3 → ℝ := ballNonlinearPressure x hR u hu
  let p : Vec3 → ℝ := ballNonlinearPressure x hr u
    (hu.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl))
  let B := vec3Ball x (r * s)
  let μ := volume.restrict B
  have hrs : 0 < r * s := mul_pos hr hs
  have hsmall : B ⊆ vec3Ball x r := vec3Ball_mono (by nlinarith)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hμ : μ univ ≠ 0 := by
    simpa only [μ, B, Measure.restrict_apply_univ] using (volume_vec3Ball_pos hrs).ne'
  have hp : MemLp p 2 (volume.restrict (vec3Ball x r)) :=
    Lp.memLp (ballNonlinearPressure x hr u
      (hu.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)))
  have hq : MemLp q 2 (volume.restrict (vec3Ball x r)) :=
    (Lp.memLp (ballNonlinearPressure x hR u hu)).mono_measure
      (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)
  have hp' := hp.mono_measure (Measure.restrict_mono hsmall le_rfl)
  have hq' := hq.mono_measure (Measure.restrict_mono hsmall le_rfl)
  have hav : average μ (q - p) = average μ q - average μ p :=
    average_sub (hq'.integrable (by norm_num)) (hp'.integrable (by norm_num))
  have hsplit : (fun y ↦ q y - average μ q) =
      (fun y ↦ p y - average μ p) + (fun y ↦ (q - p) y - average μ (q - p)) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, hav]
    ring
  have hcenter : eLpNorm (fun y ↦ p y - average μ p) 2 μ ≤
      2 * eLpNorm p 2 (volume.restrict (vec3Ball x r)) := by
    have hb := centered_eLpNorm_le_two hμ hp'.aestronglyMeasurable
      (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hb
    exact hb.trans (mul_le_mul' le_rfl (eLpNorm_mono_measure p
      (Measure.restrict_mono hsmall le_rfl)))
  have hdecay := ballHarmonic_centered_eLpNorm_two_decay x hr (hq.sub hp)
    (ballNonlinearPressure_local_difference_weaklyHarmonic x hR hr hrR u hu) hs hsρ hρ
  have hdiff : eLpNorm (q - p) 2 (volume.restrict (vec3Ball x r)) ≤
      eLpNorm q 2 (volume.restrict (vec3Ball x r)) +
        eLpNorm p 2 (volume.restrict (vec3Ball x r)) :=
    eLpNorm_sub_le (p := 2) (by norm_num)
  change eLpNorm (fun y ↦ q y - average μ q) 2 μ ≤ _
  rw [hsplit]
  exact (eLpNorm_add_le (p := 2) (by norm_num)).trans (add_le_add hcenter
    (hdecay.trans (mul_le_mul' le_rfl hdiff)))

/-- The actual local convective pressure has its extended L² to L⁴ velocity bound. -/
theorem ballNonlinearPressure_eLpNorm_two_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x r))) :
    eLpNorm (ballNonlinearPressure x hr u hu) 2 (volume.restrict (vec3Ball x r)) ≤
      12 * eLpNorm u 4 (volume.restrict (vec3Ball x r)) ^ 2 := by
  have hb := ENNReal.ofReal_le_ofReal (ballNonlinearPressure_norm_le x hr u hu)
  rw [ofReal_norm, Lp.enorm_def, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hu.eLpNorm_ne_top] at hb
  norm_num only [ENNReal.ofReal_ofNat] at hb
  exact hb

/-- Finite-volume Hölder gives the exact spatial L⁶ to L⁴ factor in the quadratic source. -/
theorem ball_velocity_four_squared_eLpNorm_le_six (x : Vec3) (r : ℝ)
    (u : Vec3 → Vec3) (hu : MemLp u 6 (volume.restrict (vec3Ball x r))) :
    eLpNorm u 4 (volume.restrict (vec3Ball x r)) ^ 2 ≤
      volume (vec3Ball x r) ^ (1 / 6 : ℝ) *
        eLpNorm u 6 (volume.restrict (vec3Ball x r)) ^ 2 := by
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := 4) (q := 6) (by norm_num) hu.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at hb
  have hpow := pow_le_pow_left' hb 2
  rw [mul_pow, ← ENNReal.rpow_natCast (volume (vec3Ball x r) ^ (1 / 12 : ℝ)) 2,
    ← ENNReal.rpow_mul] at hpow
  norm_num only at hpow
  exact hpow.trans_eq (by ring)

/-- The genuine local pressure quadratic source is bounded directly by spatial L⁶ velocity. -/
theorem ballNonlinearPressure_eLpNorm_two_le_six (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x r)))
    (hu6 : MemLp u 6 (volume.restrict (vec3Ball x r))) :
    eLpNorm (ballNonlinearPressure x hr u hu) 2 (volume.restrict (vec3Ball x r)) ≤
      12 * volume (vec3Ball x r) ^ (1 / 6 : ℝ) *
        eLpNorm u 6 (volume.restrict (vec3Ball x r)) ^ 2 := by
  exact (ballNonlinearPressure_eLpNorm_two_le x hr u hu).trans
    ((mul_le_mul' le_rfl (ball_velocity_four_squared_eLpNorm_le_six x r u hu6)).trans_eq
      (by ring))

/-- Actual localized pressure decay expressed solely through the genuine local velocity source. -/
theorem ballNonlinearPressure_centered_local_decay_velocity_source
    (x : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x R)))
    (hu6 : MemLp u 6 (volume.restrict (vec3Ball x r)))
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    let q := ballNonlinearPressure x hR u hu
    let A := 12 * volume (vec3Ball x r) ^ (1 / 6 : ℝ) *
      eLpNorm u 6 (volume.restrict (vec3Ball x r)) ^ 2
    eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball x (r * s))) q) 2
        (volume.restrict (vec3Ball x (r * s))) ≤
      2 * A + fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ) *
        (eLpNorm q 2 (volume.restrict (vec3Ball x r)) + A) := by
  have hb := ballNonlinearPressure_centered_local_decay x hR hr hrR u hu hs hsρ hρ
  have hsource := ballNonlinearPressure_eLpNorm_two_le_six x hr u
    (hu.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)) hu6
  exact hb.trans (add_le_add (mul_le_mul' le_rfl hsource)
    (mul_le_mul' le_rfl (add_le_add le_rfl hsource)))

end FluidSingularSets
