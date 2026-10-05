-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.CombinedWindowDecay
public import FluidSingularSets.ActualEnergyControl
public import FluidSingularSets.SymmetricChargeDecay

/-!
# Fixed-scale contraction from the actual local energy estimates

A positive lower bound for the cubic charge absorbs the quadratic cutoff term.
The scale is chosen from one dyadic subsequence, independent of the solution.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual scale-invariant mixed cost of the CKN gradient array on a symmetric cylinder. -/
def rawSymmetricMixedGradientActivity (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (R : ℝ) : ℝ :=
  R ^ (-(3 / 2 : ℝ)) * (arrayMixedGradientIntegral Du (vec3Ball z.1 R)
    (Ioo (z.2 - R ^ 2) (z.2 + R ^ 2))).toReal

/-- Positive radii give nonnegative symmetric mixed cost. -/
theorem rawSymmetricMixedGradientActivity_nonneg
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ rawSymmetricMixedGradientActivity Du z R := by
  unfold rawSymmetricMixedGradientActivity
  exact mul_nonneg (Real.rpow_nonneg hR _) ENNReal.toReal_nonneg

/-- The unnormalized symmetric mass has the expected three-halves scale factor. -/
theorem rawSymmetricMixedGradientActivity_mass_eq
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) {R : ℝ} (hR : 0 < R) :
    (arrayMixedGradientIntegral Du (vec3Ball z.1 R)
      (Ioo (z.2 - R ^ 2) (z.2 + R ^ 2))).toReal =
      R ^ (3 / 2 : ℝ) * rawSymmetricMixedGradientActivity Du z R := by
  unfold rawSymmetricMixedGradientActivity
  rw [← mul_assoc, ← Real.rpow_add hR]
  norm_num

/-- A backward cylinder with fixed upper time face covers the full symmetric
inner cylinder and remains inside the symmetric outer cylinder. -/
theorem mixedGradientCover_geometry (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    rawSymmetricL3Cylinder z (r / 512) ⊆
      parabolicCylinder z.1 (z.2 + r ^ 2 / 16) (r / 2) ∧
    parabolicCylinder z.1 (z.2 + r ^ 2 / 16) (r / 2) ⊆
      rawSymmetricL3Cylinder z r := by
  constructor
  · rintro a ⟨hx, hlow, hhigh⟩
    refine ⟨(vec3Ball_mono (by linarith : r / 512 ≤ r / 2)) hx, ?_, ?_⟩ <;>
      nlinarith only [hlow, hhigh, sq_pos_of_pos hr]
  · rintro a ⟨hx, hlow, hhigh⟩
    refine ⟨(vec3Ball_mono (by linarith : r / 2 ≤ r)) hx, ?_, ?_⟩ <;>
      nlinarith only [hlow, hhigh, sq_pos_of_pos hr]

/-- The genuine suitable solution makes the symmetric inner mixed cost finite
and supplies the joint measurability needed for its norm representation. -/
theorem suitableSymmetricMixedGradientData
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ spaceTimeSet Ω I) :
    AEStronglyMeasurable Du (volume.restrict (rawSymmetricL3Cylinder z (r / 512))) ∧
      arrayMixedGradientIntegral Du (vec3Ball z.1 (r / 512))
        (Ioo (z.2 - (r / 512) ^ 2) (z.2 + (r / 512) ^ 2)) < ⊤ := by
  let B := vec3Ball z.1 (r / 512)
  let T := Ioo (z.2 - (r / 512) ^ 2) (z.2 + (r / 512) ^ 2)
  let S : Set ParabolicPoint := B ×ˢ T
  have hgeo := mixedGradientCover_geometry z hr
  have hcover : closure (parabolicCylinder z.1 (z.2 + r ^ 2 / 16) (r / 2)) ⊆
      spaceTimeSet Ω I := (closure_mono hgeo.2).trans hdom
  obtain ⟨U, J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 (by positivity : 0 < r / 2) hcover
  obtain ⟨-, hD, -, -, -, henergy, -, -, -⟩ := hsol.2.2.2.2.2.1 U J hbox
  have hsub : S ⊆ U ×ˢ J := hgeo.1.trans hcyl
  have hDsmall : AEStronglyMeasurable Du (volume.restrict S) :=
    hD.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨hDsmall, ?_⟩
  apply (arrayMixedGradientIntegral_le_dissipation Du B T hDsmall).trans_lt
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne
  · calc
      _ ≤ ∫⁻ a in U ×ˢ J, ‖Du a‖ₑ ^ (2 : ℝ) := lintegral_mono_set hsub
      _ < ⊤ := (lintegral_mono fun _ ↦ le_add_left le_rfl).trans_lt henergy

/-- Positive persistent charge absorbs the two-thirds power from the cutoff. -/
theorem persistentCharge_twoThirds_le
    {ε G : ℝ} (hε : 0 < ε) (hG : ε ≤ G) :
    G ^ (2 / 3 : ℝ) ≤ ε ^ (-(1 / 3 : ℝ)) * G := by
  have hGpos := hε.trans_le hG
  have hneg := Real.rpow_le_rpow_of_nonpos hε hG (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have hrep : G ^ (2 / 3 : ℝ) = G ^ (-(1 / 3 : ℝ)) * G := by
    simpa only [Real.rpow_one, show -(1 / 3 : ℝ) + 1 = 2 / 3 by norm_num] using
      Real.rpow_add hGpos (-(1 / 3 : ℝ)) 1
  rw [hrep]
  exact mul_le_mul_of_nonneg_right hneg hGpos.le

/-- The square root of the local energy cutoff term has the required square-root
charge factor, with a coefficient depending only on the persistent threshold. -/
theorem persistentCharge_energyRoot_le
    {ε G : ℝ} (hε : 0 < ε) (hG : ε ≤ G) :
    (G ^ (2 / 3 : ℝ) + G) ^ (1 / 2 : ℝ) ≤
      (1 + ε ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ) := by
  have hGpos := hε.trans_le hG
  have hsum : G ^ (2 / 3 : ℝ) + G ≤ (1 + ε ^ (-(1 / 3 : ℝ))) * G := by
    nlinarith only [persistentCharge_twoThirds_le hε hG]
  have hroot := Real.rpow_le_rpow
    (add_nonneg (Real.rpow_nonneg hGpos.le _) hGpos.le) hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow (by positivity) hGpos.le] at hroot
  exact hroot

/-- One fixed dyadic subsequence makes the mean and harmonic contributions
contract by a quarter and fits every symmetric target window in the mean window. -/
theorem exists_dyadic_contractionScale :
    ∃ M : ℕ, 0 < (1 / 2 : ℝ) ^ M ∧ (1 / 2 : ℝ) ^ M < 1 / 2048 ∧
      2 * combinedWindowDecayConstant * 1024 ^ (3 : ℕ) * (1 / 2 : ℝ) ^ M ≤ 1 / 4 := by
  obtain ⟨M, hM⟩ := exists_nat_gt
    (max (2048 : ℝ) (8 * combinedWindowDecayConstant * 1024 ^ (3 : ℕ)))
  have hpow : (M : ℝ) < (2 : ℝ) ^ M := by
    exact_mod_cast (show M < 2 ^ M from Nat.lt_two_pow_self)
  have hpowpos : 0 < (2 : ℝ) ^ M := pow_pos (by norm_num) _
  have hwindow : (2048 : ℝ) < (2 : ℝ) ^ M :=
    ((le_max_left _ _).trans_lt hM).trans hpow
  have hcost : 8 * combinedWindowDecayConstant * 1024 ^ (3 : ℕ) < (2 : ℝ) ^ M :=
    ((le_max_right _ _).trans_lt hM).trans hpow
  refine ⟨M, pow_pos (by norm_num) _, ?_, ?_⟩
  · simpa only [div_pow, one_pow] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2048) hwindow
  · have hbound : (2 * combinedWindowDecayConstant * 1024 ^ (3 : ℕ)) /
        (2 : ℝ) ^ M ≤ 1 / 4 :=
      (div_le_iff₀ hpowpos).mpr (by nlinarith only [hcost])
    simpa only [div_eq_mul_inv, one_mul, inv_pow] using hbound

/-- The actual backward source mass is dominated by the full symmetric mixed
mass at the same inner radius. The source time window sits strictly inside it. -/
theorem shiftedMixedGradientMass_le_symmetricActivity
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ spaceTimeSet Ω I) :
    (∫⁻ t in Ioc ((energyShiftedTop z r).2 - (r / 512) ^ 2)
        (energyShiftedTop z r).2,
      eLpNorm (fun x ↦ Du (x, t)) (12 / 7)
        (volume.restrict (vec3Ball z.1 (r / 512))) ^ (2 : ℝ)).toReal ≤
      (r / 512) ^ (3 / 2 : ℝ) * rawSymmetricMixedGradientActivity Du z (r / 512) := by
  let B := vec3Ball z.1 (r / 512)
  let T := Ioo (z.2 - (r / 512) ^ 2) (z.2 + (r / 512) ^ 2)
  let J := Ioc ((energyShiftedTop z r).2 - (r / 512) ^ 2) (energyShiftedTop z r).2
  let S : Set ParabolicPoint := B ×ˢ J
  have hdata := suitableSymmetricMixedGradientData hsol hr hdom
  have htime : J ⊆ T := shiftedGradientWindow_subset_symmetricTimeWindow
    (by positivity : 0 < r / 512)
  have hsub : S ⊆ rawSymmetricL3Cylinder z (r / 512) := by
    rintro a ⟨hx, ht⟩
    exact ⟨hx, htime ht⟩
  have hD : AEStronglyMeasurable Du (volume.restrict S) :=
    hdata.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hmass : arrayMixedGradientIntegral Du B J ≤ arrayMixedGradientIntegral Du B T :=
    lintegral_mono_set htime
  have hreal := ENNReal.toReal_mono hdata.2.ne hmass
  rw [arrayMixedGradientIntegral_eq_eLpNorm Du B J hD] at hreal
  exact hreal.trans_eq (rawSymmetricMixedGradientActivity_mass_eq Du z
    (R := r / 512) (by positivity))

/-- Caccioppoli and the actual mixed mass control the mean-free cubic source on
the fixed inner cylinder. Every analytic input is derived from suitability. -/
theorem suitableShiftedMixedSourceBound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ spaceTimeSet Ω I) :
    mixedOscillationSource u Du (energyShiftedTop z r) (r / 1024) ≤
      criticalVectorCubicOscillationConstant.toReal * energyChargeConstant ^ (1 / 2 : ℝ) *
        r ^ (1 / 2 : ℝ) *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) +
          rawSymmetricL3Activity u p z r) ^ (1 / 2 : ℝ) *
        (r / 512) ^ (3 / 2 : ℝ) * rawSymmetricMixedGradientActivity Du z (r / 512) := by
  let G := rawSymmetricL3Activity u p z r
  have hG : 0 ≤ G := rawSymmetricL3Activity_nonneg u p z r
  have hsum : 0 ≤ G ^ (2 / 3 : ℝ) + G := add_nonneg (Real.rpow_nonneg hG _) hG
  have henergy := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (unforced_shifted_energy_bound hsol hr hdom)
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg energyChargeConstant_pos.le hr.le) hsum)] at henergy
  have hroot := Real.rpow_le_rpow ENNReal.toReal_nonneg henergy
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow (mul_nonneg energyChargeConstant_pos.le hr.le) hsum,
    Real.mul_rpow energyChargeConstant_pos.le hr.le] at hroot
  have hmass := shiftedMixedGradientMass_le_symmetricActivity hsol hr hdom
  have hR : 2 * (r / 1024) = r / 512 := by ring
  unfold mixedOscillationSource
  simp only [hR, energyShiftedTop]
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hroot ENNReal.toReal_nonneg) hmass
    ENNReal.toReal_nonneg
    (mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg energyChargeConstant_pos.le _)
        (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hsum _)))).trans_eq
  ring

/-- The half-power energy factor and three-halves gradient factor exactly
cancel the two powers of the target radius in the scale-invariant charge. -/
theorem mixedCharge_scaleIdentity {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (θ * r)⁻¹ ^ 2 * r ^ (1 / 2 : ℝ) * (r / 512) ^ (3 / 2 : ℝ) =
      θ⁻¹ ^ 2 * (512 : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp : r ^ (1 / 2 : ℝ) * r ^ (3 / 2 : ℝ) = r ^ (2 : ℕ) := by
    rw [← Real.rpow_add hr]
    norm_num
  rw [Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 512),
    mul_inv_rev, mul_pow]
  calc
    _ = θ⁻¹ ^ 2 * (r⁻¹ ^ 2 * (r ^ (1 / 2 : ℝ) * r ^ (3 / 2 : ℝ))) /
        (512 : ℝ) ^ (3 / 2 : ℝ) := by ring
    _ = _ := by rw [hp]; field_simp

/-- The universal coefficient for the normalized mixed cost at a fixed scale,
with one added to give a strictly positive constant. -/
def fixedScaleMixedCostConstant (ε θ : ℝ) : ℝ :=
  1 + combinedWindowDecayConstant * criticalVectorCubicOscillationConstant.toReal *
    energyChargeConstant ^ (1 / 2 : ℝ) *
    (1 + ε ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) *
    θ⁻¹ ^ 2 * (512 : ℝ) ^ (-(3 / 2 : ℝ))

/-- The normalized cost coefficient is positive for every positive threshold. -/
theorem fixedScaleMixedCostConstant_pos {ε : ℝ} (hε : 0 < ε) (θ : ℝ) :
    0 < fixedScaleMixedCostConstant ε θ := by
  unfold fixedScaleMixedCostConstant
  have hcoef : 0 ≤ combinedWindowDecayConstant *
      criticalVectorCubicOscillationConstant.toReal * energyChargeConstant ^ (1 / 2 : ℝ) *
      (1 + ε ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) *
      θ⁻¹ ^ 2 * (512 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg combinedWindowDecayConstant_pos.le ENNReal.toReal_nonneg)
      (Real.rpow_nonneg energyChargeConstant_pos.le _))
      (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  linarith

/-- At a point of persistent positive charge, the actual normalized nonlinear
source is bounded by the square root of the charge times the symmetric mixed cost. -/
theorem suitableNormalizedMixedSourceBound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ spaceTimeSet Ω I)
    (hcharge : ε ≤ rawSymmetricL3Activity u p z r) (θ : ℝ) :
    combinedWindowDecayConstant * (θ * r)⁻¹ ^ 2 *
        mixedOscillationSource u Du (energyShiftedTop z r) (r / 1024) ≤
      fixedScaleMixedCostConstant ε θ * Real.sqrt (rawSymmetricL3Activity u p z r) *
        rawSymmetricMixedGradientActivity Du z (r / 512) := by
  let G := rawSymmetricL3Activity u p z r
  let e := rawSymmetricMixedGradientActivity Du z (r / 512)
  let A := criticalVectorCubicOscillationConstant.toReal *
    energyChargeConstant ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ)
  let B := (1 + ε ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ)
  have hG : 0 ≤ G := rawSymmetricL3Activity_nonneg u p z r
  have he : 0 ≤ e := rawSymmetricMixedGradientActivity_nonneg Du z (by positivity)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg energyChargeConstant_pos.le _))
    (Real.rpow_nonneg hr.le _)
  have hroot := persistentCharge_energyRoot_le hε hcharge
  have hsource : mixedOscillationSource u Du (energyShiftedTop z r) (r / 1024) ≤
      A * (B * G ^ (1 / 2 : ℝ)) * (r / 512) ^ (3 / 2 : ℝ) * e := by
    exact (suitableShiftedMixedSourceBound hsol hr hdom).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hA)
          (Real.rpow_nonneg (by positivity) _)) he)
  have hnorm := mul_le_mul_of_nonneg_left hsource
    (mul_nonneg combinedWindowDecayConstant_pos.le (sq_nonneg ((θ * r)⁻¹)))
  let C := combinedWindowDecayConstant * criticalVectorCubicOscillationConstant.toReal *
    energyChargeConstant ^ (1 / 2 : ℝ) * B * θ⁻¹ ^ 2 * (512 : ℝ) ^ (-(3 / 2 : ℝ))
  have hrep : combinedWindowDecayConstant * (θ * r)⁻¹ ^ 2 *
      (A * (B * G ^ (1 / 2 : ℝ)) * (r / 512) ^ (3 / 2 : ℝ) * e) =
      C * G ^ (1 / 2 : ℝ) * e := by
    calc
      _ = (combinedWindowDecayConstant * criticalVectorCubicOscillationConstant.toReal *
          energyChargeConstant ^ (1 / 2 : ℝ) * B) *
          ((θ * r)⁻¹ ^ 2 * r ^ (1 / 2 : ℝ) * (r / 512) ^ (3 / 2 : ℝ)) *
          G ^ (1 / 2 : ℝ) * e := by dsimp [A]; ring
      _ = _ := by rw [mixedCharge_scaleIdentity hr θ]; dsimp [C]; ring
  have hcost : C ≤ fixedScaleMixedCostConstant ε θ := by
    dsimp [C, B, fixedScaleMixedCostConstant]
    linarith
  have hfinal := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hG (1 / 2 : ℝ))) he
  simpa only [Real.sqrt_eq_rpow] using (hnorm.trans_eq hrep).trans hfinal

/-- Every positive persistence threshold admits one dyadic scale and one
constant, independent of the suitable solution and of the cylinder, at which
the actual symmetric cubic charge contracts with the genuine mixed-gradient cost. -/
theorem exists_suitableFixedScaleRecurrence {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (C : ℝ), 0 < C ∧ (1 / 2 : ℝ) ^ M < 1 / 2048 ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (q : ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0) →
        ∀ (z : ParabolicPoint) (r : ℝ), 0 < r →
          closure (rawSymmetricL3Cylinder z r) ⊆ spaceTimeSet Ω I →
          ε ≤ rawSymmetricL3Activity u p z r →
          rawSymmetricL3Activity u p z ((1 / 2 : ℝ) ^ M * r) ≤
            rawSymmetricL3Activity u p z r / 4 +
              C * Real.sqrt (rawSymmetricL3Activity u p z r) *
                rawSymmetricMixedGradientActivity Du z (r / 512) := by
  obtain ⟨M, hθ, hwindow, hquarter⟩ := exists_dyadic_contractionScale
  refine ⟨M, fixedScaleMixedCostConstant ε ((1 / 2 : ℝ) ^ M),
    fixedScaleMixedCostConstant_pos hε _, hwindow, ?_⟩
  intro Ω I q u Du p hsol z r hr hdom hcharge
  let θ := (1 / 2 : ℝ) ^ M
  have hs : 0 < θ * r := mul_pos hθ hr
  have hsr : θ * r ≤ r / 2048 := by
    have hscaled := mul_le_mul_of_nonneg_right hwindow.le hr.le
    dsimp [θ]
    linarith only [hscaled]
  have hdecay := suitableSymmetricChargeDecay hsol hr hs hsr hdom
  have hratio : (θ * r) / r = θ := by field_simp
  rw [hratio] at hdecay
  have hG := rawSymmetricL3Activity_nonneg u p z r
  have hlinear : 2 * combinedWindowDecayConstant * 1024 ^ (3 : ℕ) * θ *
      rawSymmetricL3Activity u p z r ≤ rawSymmetricL3Activity u p z r / 4 := by
    have hbound := mul_le_mul_of_nonneg_right hquarter hG
    linarith only [hbound]
  have hsource := suitableNormalizedMixedSourceBound hsol hr hε hdom hcharge θ
  exact hdecay.trans (add_le_add hlinear hsource)

end FluidSingularSets
