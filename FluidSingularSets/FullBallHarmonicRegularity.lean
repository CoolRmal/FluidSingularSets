-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HarmonicC2
public import FluidSingularSets.UnitBallPressureBounds
public import FluidSingularSets.LocalHessianCalculus
public import FluidSingularSets.UnitBallHarmonicForceGradient
public import CKN.Foundation.Harmonic.InteriorDisplaysOuter

/-!
# Genuine harmonic regularity on the whole open ball

Translated local Weyl representatives agree on open overlaps by their actual
almost-everywhere identification. Gluing their values gives a C² representative
on the entire open unit ball. The full-ball identification follows from the
second-countable locally-null theorem, rather than an assumed representative.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- Actual local a.e. C² representatives glue on any open set. -/
theorem exists_contDiffOn_two_ae_of_local_representatives
    {U : Set Vec3} {h : Vec3 → ℝ} (hU : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ V : Set Vec3, IsOpen V ∧ x ∈ V ∧
      ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H V ∧ h =ᵐ[volume.restrict V] H) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H U ∧ h =ᵐ[volume.restrict U] H := by
  classical
  choose V hV hxV L hL ha using hlocal
  let H : Vec3 → ℝ := fun y ↦ if hy : y ∈ U then L y hy y else 0
  have heq (x : Vec3) (hx : x ∈ U) (y : Vec3) (hy : y ∈ U) (hyV : y ∈ V x hx) :
      H y = L x hx y := by
    let W := V x hx ∩ V y hy
    have hxa : h =ᵐ[volume.restrict W] L x hx :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (ha x hx)
    have hya : h =ᵐ[volume.restrict W] L y hy :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (ha y hy)
    have hp := MeasureTheory.Measure.eqOn_open_of_ae_eq (hxa.symm.trans hya)
      ((hV x hx).inter (hV y hy))
      ((hL x hx).continuousOn.mono inter_subset_left)
      ((hL y hy).continuousOn.mono inter_subset_right) ⟨hyV, hxV y hy⟩
    simpa only [H, dite_eq_left hy] using hp.symm
  have hH : ContDiffOn ℝ (2 : ℕ∞) H U := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    refine ⟨V x hx, hV x hx, hxV x hx, ?_⟩
    exact ((hL x hx).mono inter_subset_right).congr fun y hy ↦ heq x hx y hy.1 hy.2
  let bad : Set Vec3 := {x | x ∈ U ∧ H x ≠ h x}
  have hbad : volume bad = 0 := by
    apply MeasureTheory.measure_null_of_locally_null bad
    intro x hx
    have hxU := hx.1
    have hag : ∀ᵐ y ∂volume, y ∈ V x hxU → h y = L x hxU y :=
      ae_imp_of_ae_restrict (ha x hxU)
    have hn : volume {y | ¬ (y ∈ V x hxU → h y = L x hxU y)} = 0 := ae_iff.mp hag
    have hb : volume (bad ∩ V x hxU) = 0 := by
      apply measure_mono_null ?_ hn
      rintro y ⟨⟨hyU, hneq⟩, hyV⟩ hgood
      exact hneq ((heq x hxU y hyU hyV).trans (hgood hyV).symm)
    refine ⟨bad ∩ V x hxU, ?_, hb⟩
    exact mem_nhdsWithin.mpr ⟨V x hxU, hV x hxU, hxV x hxU,
      fun y hy ↦ ⟨hy.2, hy.1⟩⟩
  have hag : ∀ᵐ x ∂volume, x ∈ U → h x = H x := by
    filter_upwards [compl_mem_ae_iff.mpr hbad] with x hx hxU
    change ¬ (x ∈ U ∧ H x ≠ h x) at hx
    exact (not_not.mp (fun hneq ↦ hx ⟨hxU, hneq⟩)).symm
  refine ⟨H, hH, ?_⟩
  filter_upwards [hag.filter_mono ae_restrict_le, ae_restrict_mem hU.measurableSet]
    with x hx hxU
  exact hx hxU

private theorem fullBall_local_ball_subset {x : Vec3} {r R : ℝ}
    (hx : x ∈ vec3Ball 0 r) (hmargin : r + R ≤ 1) :
    vec3Ball x R ⊆ vec3Ball 0 1 := by
  intro y hy
  rw [mem_vec3Ball] at hx hy ⊢
  have ht := vec3EuclideanNorm_add_le (y - x) x
  rw [sub_add_cancel] at ht
  norm_num only [sub_zero] at hx ⊢
  linarith

/-- Genuine local Weyl analysis yields a C² representative on the entire open unit ball. -/
theorem exists_fullBall_weaklyHarmonic_C2_representative {h : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1) ∧
      h =ᵐ[volume.restrict (vec3Ball 0 1)] H ∧ WeaklyHarmonicOn (vec3Ball 0 1) H := by
  obtain ⟨H, hH, hae⟩ := exists_contDiffOn_two_ae_of_local_representatives
    (isOpen_vec3Ball 0 1) (by
      intro x hx
      let R : ℝ := (1 - vec3EuclideanNorm x) / 2
      have hxnorm : vec3EuclideanNorm x < 1 := by simpa only [mem_vec3Ball, sub_zero] using hx
      have hR : 0 < R := by dsimp [R]; linarith
      have hsub : vec3Ball x R ⊆ vec3Ball 0 1 := by
        intro y hy
        rw [mem_vec3Ball] at hy ⊢
        have ht := vec3EuclideanNorm_add_le (y - x) x
        rw [sub_add_cancel] at ht
        norm_num only [sub_zero]
        dsimp [R] at hy
        linarith
      have hm := hmem.mono_measure (Measure.restrict_mono_set volume hsub)
      have hw := localWeaklyHarmonicOn_restrict hsub hweak
      rw [← euclideanBall_eq_vec3Ball hR] at hm hw
      obtain ⟨G, hG, hGa⟩ := exists_weaklyHarmonic_C2_representative hR hm hw
      rw [euclideanBall_eq_vec3Ball (by positivity : 0 < R / 4)] at hG hGa
      refine ⟨vec3Ball x (R / 4), isOpen_vec3Ball x (R / 4), ?_, G, hG, hGa⟩
      rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
      positivity)
  exact ⟨H, hH, hae, localWeaklyHarmonicOn_congr_ae hae hweak⟩

/-- The genuine first-derivative constant at any inner radius below one. -/
def fullBallHarmonicGradientConstant (ρ : ℝ) : ℝ :=
  1728 * harmonicInteriorGradientSupConstant * ((1 - ρ) ^ 3)⁻¹

/-- The genuine second-derivative constant, expressed directly in the boundary margin. -/
def fullBallHarmonicHessianConstant (ρ : ℝ) : ℝ :=
  1728 * harmonicInteriorGradientSupConstant * (((1 - ρ) / 2) ^ 3)⁻¹ *
    fullBallHarmonicGradientConstant ρ *
      (volume (vec3Ball (0 : Vec3) ((1 - ρ) / 2))).toReal ^ (2 / 3 : ℝ)

theorem fullBallHarmonicGradientConstant_nonneg {ρ : ℝ} (hρ : ρ < 1) :
    0 ≤ fullBallHarmonicGradientConstant ρ := by
  exact mul_nonneg (mul_nonneg (by norm_num) harmonicInteriorGradientSupConstant_nonneg)
    (by have h : 0 < 1 - ρ := sub_pos.mpr hρ; positivity)

theorem fullBallHarmonicHessianConstant_nonneg {ρ : ℝ} (hρ : ρ < 1) :
    0 ≤ fullBallHarmonicHessianConstant ρ := by
  have h : 0 < 1 - ρ := sub_pos.mpr hρ
  exact mul_nonneg
    (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) harmonicInteriorGradientSupConstant_nonneg)
      (by positivity)) (fullBallHarmonicGradientConstant_nonneg hρ))
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

private theorem fullBall_local_gradient_bound {h H : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1))
    (hae : h =ᵐ[volume.restrict (vec3Ball 0 1)] H)
    {x : Vec3} {R : ℝ} (hR : 0 < R) (hsub : vec3Ball x R ⊆ vec3Ball 0 1) :
    ∀ y ∈ vec3Ball x (R / 2), vec3EuclideanNorm (classicalGradient H y) ≤
      1728 * harmonicInteriorGradientSupConstant * (R ^ 3)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by
  have hal : h =ᵐ[volume.restrict (vec3Ball x R)] H :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have hm := MemLp.ae_eq hal (hmem.mono_measure (Measure.restrict_mono_set volume hsub))
  have hw := localWeaklyHarmonicOn_congr_ae hal (localWeaklyHarmonicOn_restrict hsub hweak)
  have hn : lpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x R)) ≤
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by
    change (eLpNorm H _ _).toReal ≤ (eLpNorm h _ _).toReal
    rw [← eLpNorm_congr_ae hal]
    exact ENNReal.toReal_mono hmem.eLpNorm_ne_top
      (eLpNorm_mono_measure h (Measure.restrict_mono_set volume hsub))
  intro y hy
  exact (harmonic_contDiffOn_gradient_bound hR ((hH.of_le (by norm_num)).mono hsub)
    hm hw y hy).trans (mul_le_mul_of_nonneg_left hn
      (mul_nonneg (mul_nonneg (by norm_num) harmonicInteriorGradientSupConstant_nonneg)
        (by positivity)))

/-- Actual first derivatives on every inner ball have a quantitative boundary-margin bound. -/
theorem fullBallHarmonic_representative_gradient_bound {h H : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1))
    (hae : h =ᵐ[volume.restrict (vec3Ball 0 1)] H)
    {ρ : ℝ} (hρ : ρ < 1) {x : Vec3} (hx : x ∈ vec3Ball 0 ρ) :
    vec3EuclideanNorm (classicalGradient H x) ≤ fullBallHarmonicGradientConstant ρ *
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by
  have hR : 0 < 1 - ρ := sub_pos.mpr hρ
  apply fullBall_local_gradient_bound hmem hweak hH hae hR
    (fullBall_local_ball_subset hx (by linarith))
  rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
  positivity

/-- Actual Hessians on every inner ball have the corresponding true margin-dependent bound. -/
theorem fullBallHarmonic_representative_hessian_bound {h H : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1))
    (hae : h =ᵐ[volume.restrict (vec3Ball 0 1)] H)
    {ρ : ℝ} (hρ : ρ < 1) {x : Vec3} (hx : x ∈ vec3Ball 0 ρ) (i j : Fin 3) :
    |mixedSecond H i j x| ≤ fullBallHarmonicHessianConstant ρ *
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by
  let R := 1 - ρ
  have hR : 0 < R := sub_pos.mpr hρ
  have hsub : vec3Ball x R ⊆ vec3Ball 0 1 :=
    fullBall_local_ball_subset hx (by dsimp [R]; linarith)
  have hs : vec3Ball x (R / 2) ⊆ vec3Ball 0 1 :=
    (vec3Ball_mono (by linarith : R / 2 ≤ R)).trans hsub
  have ho := isOpen_vec3Ball x (R / 2)
  have hpartial := contDiffOn_spatialDeriv_of_two (isOpen_vec3Ball 0 1) hH j
  let B := fullBallHarmonicGradientConstant ρ *
    lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1))
  have hB : 0 ≤ B := mul_nonneg (fullBallHarmonicGradientConstant_nonneg hρ) lpNorm_nonneg
  have hpn : ∀ y ∈ vec3Ball x (R / 2), ‖spatialDeriv H j y‖ ≤ B := by
    intro y hy
    rw [Real.norm_eq_abs]
    exact (abs_apply_le_vec3EuclideanNorm (classicalGradient H y) j).trans
      (fullBall_local_gradient_bound hmem hweak hH hae hR hsub y hy)
  let : IsFiniteMeasure (volume.restrict (vec3Ball x (R / 2))) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hpm : MemLp (spatialDeriv H j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x (R / 2))) := by
    apply MemLp.of_bound ((hpartial.continuousOn.mono hs).aestronglyMeasurable
      ho.measurableSet) B
    filter_upwards [ae_restrict_mem ho.measurableSet] with y hy
    exact hpn y hy
  have hpLp : lpNorm (spatialDeriv H j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x (R / 2))) ≤
      B * (volume (vec3Ball 0 (R / 2))).toReal ^ (2 / 3 : ℝ) := by
    have ht := lpNorm_bound_on ho.measurableSet
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num) (by norm_num) B hB hpn
    norm_num at ht
    simpa only [volume_vec3Ball x (R / 2)] using ht
  have hw := weaklyHarmonicOn_spatialDeriv_of_contDiffOn (isOpen_vec3Ball 0 1)
    (hH.of_le (by norm_num)) (localWeaklyHarmonicOn_congr_ae hae hweak) j
  have hxinner : x ∈ vec3Ball x ((R / 2) / 2) := by
    rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    positivity
  have hg := harmonic_contDiffOn_gradient_bound (by positivity : 0 < R / 2)
    (hpartial.mono hs) hpm (localWeaklyHarmonicOn_restrict hs hw) x hxinner
  have hb := mul_le_mul_of_nonneg_left hpLp
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1728)
      harmonicInteriorGradientSupConstant_nonneg) (by positivity : 0 ≤ ((R / 2) ^ 3)⁻¹))
  have hf := (abs_apply_le_vec3EuclideanNorm (classicalGradient (spatialDeriv H j) x) i)
    |>.trans (hg.trans hb)
  change |mixedSecond H i j x| ≤ _ at hf
  convert hf using 1
  dsimp [fullBallHarmonicHessianConstant, R, B]
  ring

/-- Full-ball representatives carry the genuine derivative bounds at every inner radius. -/
theorem exists_fullBall_weaklyHarmonic_C2_with_derivative_bounds {h : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1) ∧
      h =ᵐ[volume.restrict (vec3Ball 0 1)] H ∧ WeaklyHarmonicOn (vec3Ball 0 1) H ∧
      (∀ ρ < 1, ∀ x ∈ vec3Ball 0 ρ,
        vec3EuclideanNorm (classicalGradient H x) ≤ fullBallHarmonicGradientConstant ρ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1))) ∧
      (∀ ρ < 1, ∀ x ∈ vec3Ball 0 ρ, ∀ i j : Fin 3,
        |mixedSecond H i j x| ≤ fullBallHarmonicHessianConstant ρ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1))) := by
  obtain ⟨H, hH, ha, hw⟩ := exists_fullBall_weaklyHarmonic_C2_representative hmem hweak
  exact ⟨H, hH, ha, hw,
    fun _ρ hρ _x hx ↦ fullBallHarmonic_representative_gradient_bound hmem hweak hH ha hρ hx,
    fun _ρ hρ _x hx i j ↦ fullBallHarmonic_representative_hessian_bound
      hmem hweak hH ha hρ hx i j⟩

/-- The actual harmonic force pressure admits a representative on the whole open unit ball. -/
theorem unitBallFullHarmonicForcePressure_exists (F : unitBallGradientFreeForce) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1) ∧
      unitBallPressureFunction F.1 =ᵐ[volume.restrict (vec3Ball 0 1)] H ∧
      WeaklyHarmonicOn (vec3Ball 0 1) H :=
  exists_fullBall_weaklyHarmonic_C2_representative
    (unitBallPressureFunction_memLp_threeHalves F.1)
    (unitBallStokesPressure_weaklyHarmonic F.1 F.property)

/-- A genuine full-ball extension of the existing canonical quarter-ball potential. -/
def unitBallFullHarmonicForcePressureRepresentative (F : unitBallGradientFreeForce) : Vec3 → ℝ :=
  Classical.choose (unitBallFullHarmonicForcePressure_exists F)

theorem unitBallFullHarmonicForcePressureRepresentative_contDiff (F : unitBallGradientFreeForce) :
    ContDiffOn ℝ (2 : ℕ∞) (unitBallFullHarmonicForcePressureRepresentative F) (vec3Ball 0 1) :=
  (Classical.choose_spec (unitBallFullHarmonicForcePressure_exists F)).1

theorem unitBallFullHarmonicForcePressureRepresentative_ae (F : unitBallGradientFreeForce) :
    unitBallPressureFunction F.1 =ᵐ[volume.restrict (vec3Ball 0 1)]
      unitBallFullHarmonicForcePressureRepresentative F :=
  (Classical.choose_spec (unitBallFullHarmonicForcePressure_exists F)).2.1

theorem unitBallFullHarmonicForcePressureRepresentative_weaklyHarmonic
    (F : unitBallGradientFreeForce) :
    WeaklyHarmonicOn (vec3Ball 0 1) (unitBallFullHarmonicForcePressureRepresentative F) :=
  (Classical.choose_spec (unitBallFullHarmonicForcePressure_exists F)).2.2

/-- True a.e. agreement identifies the old and full-ball representatives pointwise. -/
theorem unitBallFullHarmonicForcePressureRepresentative_eqOn_quarter
    (F : unitBallGradientFreeForce) :
    EqOn (unitBallFullHarmonicForcePressureRepresentative F)
      (unitBallHarmonicForcePressureRepresentative F) (vec3Ball 0 (1 / 4)) := by
  have hs : vec3Ball (0 : Vec3) (1 / 4) ⊆ vec3Ball 0 1 := vec3Ball_mono (by norm_num)
  have ha : unitBallPressureFunction F.1 =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      unitBallFullHarmonicForcePressureRepresentative F :=
    ae_restrict_of_ae_restrict_of_subset hs
      (unitBallFullHarmonicForcePressureRepresentative_ae F)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq
    (ha.symm.trans (unitBallHarmonicForcePressureRepresentative_pressure_ae F))
    (isOpen_vec3Ball 0 (1 / 4))
    ((unitBallFullHarmonicForcePressureRepresentative_contDiff F).continuousOn.mono hs)
    (unitBallHarmonicForcePressureRepresentative_contDiff F).continuousOn

end FluidSingularSets
