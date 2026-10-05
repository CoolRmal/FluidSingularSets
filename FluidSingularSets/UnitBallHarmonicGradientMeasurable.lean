-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicGradientPairing
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Genuine space-time measurability of the local harmonic pressure gradient

Actual restricted L² slices supply the local operator when finite, with zero
at other times. At a fixed interior point the genuine Riesz field expresses
every gradient coordinate as a measurable spatial integral. Continuity in
space then proves joint measurability, without a whole-space pressure operator.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual local harmonic-gradient slice, zero when the source slice is not in L². -/
def unitBallHarmonicGradientSliceOfField (F : Vec3 × ℝ → L2Vec3) (t : ℝ) :
    C(unitBallPressureCompactInterior, Vec3) := by
  classical
  exact if h : MemLp (fun z : Vec3 ↦ F (z, t)) 2 (volume.restrict (vec3Ball 0 1)) then
    unitBallHarmonicGradientExtended (h.toLp (fun z ↦ F (z, t)))
  else 0

/-- The true restricted spatial L² seminorm is measurable in time. -/
theorem measurable_unitBallVector_eLpNorm_slice {F : Vec3 × ℝ → L2Vec3}
    (hF : StronglyMeasurable F) :
    Measurable fun t : ℝ ↦ eLpNorm (fun z : Vec3 ↦ F (z, t)) 2
      (volume.restrict (vec3Ball 0 1)) := by
  have hs (t : ℝ) : AEStronglyMeasurable (fun z : Vec3 ↦ F (z, t))
      (volume.restrict (vec3Ball 0 1)) :=
    (hF.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have he : (fun t : ℝ ↦ eLpNorm (fun z : Vec3 ↦ F (z, t)) 2
      (volume.restrict (vec3Ball 0 1))) =
      fun t ↦ (∫⁻ z in vec3Ball 0 1, ‖F (z, t)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    funext t
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hs t)]
    simp
  rw [he]
  refine Measurable.pow_const ?_ _
  exact Measurable.lintegral_prod_left'
    (f := fun q : Vec3 × ℝ ↦ ‖F q‖ₑ ^ (2 : ℝ)) (hF.measurable.enorm.pow_const _)

/-- The actual finite L² slice times form a measurable set. -/
theorem measurableSet_unitBallVector_memLp_slice {F : Vec3 × ℝ → L2Vec3}
    (hF : StronglyMeasurable F) :
    MeasurableSet {t : ℝ | MemLp (fun z : Vec3 ↦ F (z, t)) 2
      (volume.restrict (vec3Ball 0 1))} := by
  have hm : MeasurableSet {t : ℝ | eLpNorm (fun z : Vec3 ↦ F (z, t)) 2
      (volume.restrict (vec3Ball 0 1)) < ∞} :=
    measurableSet_lt (measurable_unitBallVector_eLpNorm_slice hF) measurable_const
  convert hm using 1
  ext t
  simp only [MemLp]

/-- Every fixed interior point and coordinate is genuinely measurable in time. -/
theorem measurable_unitBallHarmonicGradientSliceOfField_coordinate
    {F : Vec3 × ℝ → L2Vec3} (hF : StronglyMeasurable F)
    (x : unitBallPressureCompactInterior) (i : Fin 3) :
    Measurable fun t : ℝ ↦ unitBallHarmonicGradientSliceOfField F t x i := by
  let H := unitBallHarmonicGradientPairingField x i
  have hH : Measurable H := (Lp.stronglyMeasurable H).measurable
  let good : Set ℝ := {t | MemLp (fun z : Vec3 ↦ F (z, t)) 2
    (volume.restrict (vec3Ball 0 1))}
  have he : (fun t : ℝ ↦ unitBallHarmonicGradientSliceOfField F t x i) =
      good.indicator (fun t ↦ ∫ z in vec3Ball 0 1, ∑ j : Fin 3, H z j * F (z, t) j) := by
    funext t
    by_cases ht : MemLp (fun z : Vec3 ↦ F (z, t)) 2 (volume.restrict (vec3Ball 0 1))
    · rw [Set.indicator_of_mem (show t ∈ good from ht), unitBallHarmonicGradientSliceOfField,
        dite_eq_left ht, unitBallHarmonicGradientExtended_integral_pairing]
      apply integral_congr_ae
      filter_upwards [ht.coeFn_toLp] with z hz
      rw [hz]
    · rw [Set.indicator_of_notMem (show t ∉ good from ht), unitBallHarmonicGradientSliceOfField,
        dite_eq_right ht]
      rfl
  rw [he]
  refine Measurable.indicator ?_ (measurableSet_unitBallVector_memLp_slice hF)
  refine (StronglyMeasurable.integral_prod_left
    (f := fun (z : Vec3) (t : ℝ) ↦ ∑ j : Fin 3, H z j * F (z, t) j) ?_).measurable
  apply Measurable.stronglyMeasurable
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  have hj := (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) j : L2Vec3 →L[ℝ] ℝ).continuous.measurable
  have hmul := (hj.comp (hH.comp measurable_fst)).mul (hj.comp hF.measurable)
  convert hmul using 1
  funext q
  rfl

/-- The true local harmonic gradient is jointly measurable on the compact interior and time. -/
theorem measurable_unitBallHarmonicGradientSliceOfField_spaceTime
    {F : Vec3 × ℝ → L2Vec3} (hF : StronglyMeasurable F) :
    Measurable fun z : unitBallPressureCompactInterior × ℝ ↦
      unitBallHarmonicGradientSliceOfField F z.2 z.1 :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : unitBallPressureCompactInterior) (t : ℝ) ↦
      unitBallHarmonicGradientSliceOfField F t x)
    (fun t ↦ (unitBallHarmonicGradientSliceOfField F t).continuous)
    (fun x ↦ Measurable.of_eval fun i ↦
      measurable_unitBallHarmonicGradientSliceOfField_coordinate hF x i)

/-- The true compact-gradient norm is controlled by the actual spatial slice L² norm. -/
theorem unitBallHarmonicGradientSliceOfField_norm_le (F : Vec3 × ℝ → L2Vec3) (t : ℝ) :
    ‖unitBallHarmonicGradientSliceOfField F t‖ ≤ stokesVectorPressureGradientConstant *
      lpNorm (fun z : Vec3 ↦ F (z, t)) 2 (volume.restrict (vec3Ball 0 1)) := by
  by_cases ht : MemLp (fun z : Vec3 ↦ F (z, t)) 2 (volume.restrict (vec3Ball 0 1))
  · rw [unitBallHarmonicGradientSliceOfField, dite_eq_left ht]
    simpa only [Lp.norm_toLp, toReal_eLpNorm] using
      unitBallHarmonicGradientExtended_norm_le (ht.toLp (fun z ↦ F (z, t)))
  · rw [unitBallHarmonicGradientSliceOfField, dite_eq_right ht, norm_zero,
      lpNorm_of_not_memLp ht, mul_zero]

end FluidSingularSets
