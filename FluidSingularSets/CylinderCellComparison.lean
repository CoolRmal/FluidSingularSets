module

public import FluidSingularSets.GradientEnergyControl
public import FluidSingularSets.ShiftedCellRepresentation
public import FluidSingularSets.FixedScaleRecurrence

/-!
# Dissipation comparison between cylinders and adjacent-grid cells

A cell containing a singular center with side between `r/32` and `r/16` lies
inside an admissible backward energy cylinder. Actual Caccioppoli therefore
controls its normalized gradient mass by the activity of the outer symmetric
cylinder. The gradient density uses the same array norm as the trace embedding.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- The backward terminal time used to include the whole small cell. -/
def traceEnergyTop (z : ParabolicPoint) (r : ℝ) : ℝ := z.2 + r ^ 2 / 64

/-- The outer energy cylinder remains inside the symmetric activity cylinder. -/
theorem traceEnergyOuter_subset_symmetric (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    parabolicCylinder z.1 (traceEnergyTop z r) (r / 2) ⊆ rawSymmetricL3Cylinder z r := by
  rintro a ⟨hx, hlow, hhigh⟩
  refine ⟨vec3Ball_mono (by linarith : r / 2 ≤ r) hx, ?_, ?_⟩ <;>
    dsimp [traceEnergyTop] at * <;> nlinarith [sq_pos_of_pos hr]

/-- Every sufficiently small containing cell lies in the inner backward energy cylinder. -/
theorem shiftedCell_subset_traceEnergyInner (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ shiftedParabolicDyadicCell g Q) (hside : dyadicScale Q.scale < r / 16) :
    shiftedParabolicDyadicCell g Q ⊆ parabolicCylinder z.1 (traceEnergyTop z r) (r / 4) := by
  intro a ha
  have hd := (Metric.edist_le_ediam_of_mem ha hz).trans
    (ediam_shiftedParabolicDyadicCell_le g Q)
  have hdreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  simp only [← dist_edist, ENNReal.toReal_ofReal
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (dyadicScale_pos Q.scale).le)] at hdreal
  rw [dist_eq_parabolicDist, parabolicDist, max_le_iff] at hdreal
  have htime : |a.2 - z.2| ≤ (2 * dyadicScale Q.scale) ^ 2 :=
    (Real.sqrt_le_iff.1 hdreal.2).2
  have htimesmall : |a.2 - z.2| < r ^ 2 / 64 := by
    apply htime.trans_lt
    have hp := pow_lt_pow_left₀ (by linarith : 2 * dyadicScale Q.scale < r / 8)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (dyadicScale_pos Q.scale).le)
      (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith only [hp]
  have ht := abs_lt.1 htimesmall
  refine ⟨hdreal.1.trans_lt (by linarith), ?_, ?_⟩ <;>
    dsimp [traceEnergyTop] <;> nlinarith [sq_pos_of_pos hr]

/-- Actual suitable solutions control the normalized dissipation of every such cell. -/
theorem normalized_shiftedCell_dissipation_le_activity
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) (hz : z ∈ shiftedParabolicDyadicCell g Q)
    (hsideLo : r / 32 ≤ dyadicScale Q.scale) (hsideHi : dyadicScale Q.scale < r / 16)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I) :
    (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖Du a‖ₑ ^ (2 : ℝ)).toReal /
        dyadicScale Q.scale ≤
      1536 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r) := by
  let S := rawSymmetricL3Activity u p z r ^ (2 / 3 : ℝ) + rawSymmetricL3Activity u p z r
  have hG := rawSymmetricL3Activity_nonneg u p z r
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg hG _) hG
  have hsub := shiftedCell_subset_traceEnergyInner g Q hr hz hsideHi
  have hmass : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖Du a‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal (48 * CKN.Core.Endgame.startGammaConstant ^ 2 * r * S) := by
    calc
      _ ≤ ∫⁻ a in shiftedParabolicDyadicCell g Q,
          ENNReal.ofReal (CKN.spatialGradientSq u Du a) :=
        lintegral_mono (fun a ↦ array_enorm_sq_le_spatialGradientSq u Du a)
      _ ≤ ∫⁻ a in parabolicCylinder z.1 (traceEnergyTop z r) (r / 4),
          ENNReal.ofReal (CKN.spatialGradientSq u Du a) := lintegral_mono_set hsub
      _ ≤ _ := unforced_backward_half_gradient_mass_le_charge hsol (traceEnergyTop z r)
        hr hdom (traceEnergyOuter_subset_symmetric z hr)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hr.le) hS)] at hreal
  have hratio : r / dyadicScale Q.scale ≤ 32 :=
    (div_le_iff₀ (dyadicScale_pos _)).2 (by linarith only [hsideLo])
  calc
    _ ≤ (48 * CKN.Core.Endgame.startGammaConstant ^ 2 * r * S) /
        dyadicScale Q.scale := div_le_div_of_nonneg_right hreal (dyadicScale_pos _).le
    _ = (48 * CKN.Core.Endgame.startGammaConstant ^ 2 * S) *
        (r / dyadicScale Q.scale) := by ring
    _ ≤ (48 * CKN.Core.Endgame.startGammaConstant ^ 2 * S) * 32 :=
      mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hS)
    _ = _ := by dsimp [S]; ring

/-- Positive persistent charge absorbs the cutoff power in the actual cell dissipation. -/
theorem persistent_shiftedCell_dissipation_le_activity
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) {z : ParabolicPoint} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hG : ε ≤ rawSymmetricL3Activity u p z r)
    (hz : z ∈ shiftedParabolicDyadicCell g Q)
    (hsideLo : r / 32 ≤ dyadicScale Q.scale) (hsideHi : dyadicScale Q.scale < r / 16)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I) :
    (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖Du a‖ₑ ^ (2 : ℝ)).toReal /
        dyadicScale Q.scale ≤
      (1 + 1536 * CKN.Core.Endgame.startGammaConstant ^ 2 *
        (1 + ε ^ (-(1 / 3 : ℝ)))) * rawSymmetricL3Activity u p z r := by
  have hbase := normalized_shiftedCell_dissipation_le_activity
    hsol g Q hr hz hsideLo hsideHi hdom
  have hpower := persistentCharge_twoThirds_le hε hG
  have hGpos := hε.trans_le hG
  have hcoeff : 0 ≤ 1536 * CKN.Core.Endgame.startGammaConstant ^ 2 := by positivity
  have habsorb := mul_le_mul_of_nonneg_left
    (add_le_add_right hpower (rawSymmetricL3Activity u p z r)) hcoeff
  nlinarith only [hbase, habsorb, hGpos]

/-- A normalized dissipation bound transfers the reciprocal gauge activity cost
into the concrete trace cost, with the correct zero-mass convention. -/
theorem weighted_activity_le_trace_cost {e a d G F A B : ℝ}
    (he : 0 ≤ e) (hd : 0 ≤ d) (hG : 0 < G)
    (hF : 0 < F) (hB : 0 < B)
    (hea : e ≤ A * a) (hcharge : d ≤ B * G) (hzero : d = 0 → a = 0) :
    (1 / Real.sqrt F) * e / Real.sqrt G ≤
      A * Real.sqrt B * (a / Real.sqrt (d * F)) := by
  rcases eq_or_lt_of_le hd with hzerod | hposd
  · have ha0 := hzero hzerod.symm
    have he0 : e = 0 := le_antisymm (by simpa only [ha0, mul_zero] using hea) he
    simp only [he0, ha0, mul_zero, zero_div, le_refl]
  have hdenpos : 0 < Real.sqrt (d * F) := Real.sqrt_pos.2 (mul_pos hposd hF)
  have hGroot : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  have hFroot : 0 < Real.sqrt F := Real.sqrt_pos.2 hF
  have hden : Real.sqrt (d * F) ≤ Real.sqrt B * (Real.sqrt G * Real.sqrt F) := by
    rw [Real.sqrt_mul hd]
    have h := Real.sqrt_le_sqrt hcharge
    rw [Real.sqrt_mul hB.le] at h
    nlinarith only [h, hFroot]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hdenpos).2
  have hnonneg : 0 ≤ (1 / Real.sqrt F) * e / Real.sqrt G :=
    div_nonneg (mul_nonneg (div_nonneg (by norm_num) hFroot.le) he) hGroot.le
  have hscaled := mul_le_mul_of_nonneg_left hden hnonneg
  have hrepr : ((1 / Real.sqrt F) * e / Real.sqrt G) *
      (Real.sqrt B * (Real.sqrt G * Real.sqrt F)) = Real.sqrt B * e := by
    field_simp
  have hbound := mul_le_mul_of_nonneg_left hea (Real.sqrt_nonneg B)
  calc
    _ ≤ Real.sqrt B * e := hscaled.trans_eq hrepr
    _ ≤ Real.sqrt B * (A * a) := hbound
    _ = _ := by ring

end FluidSingularSets
