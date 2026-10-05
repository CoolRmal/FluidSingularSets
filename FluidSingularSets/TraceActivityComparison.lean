module

public import FluidSingularSets.CylinderCellComparison
public import FluidSingularSets.PointwiseGradientTrace
public import FluidSingularSets.CellMixedDissipation
public import FluidSingularSets.SymmetricCellMixedComparison
public import FluidSingularSets.DyadicLogWeights

/-!
# Actual activity costs are controlled by the concrete trace

Caccioppoli controls normalized cell dissipation by persistent symmetric activity.
The symmetric-to-cell mixed comparison then bounds the reciprocal logarithmic
activity cost by the actual trace cost. Zero dissipation forces zero mixed cost.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- The uniform coefficient in the singular-point cell comparison. -/
def traceActivityConstant (ε : ℝ) : ℝ :=
  512 * Real.sqrt (1 + 1536 * CKN.Core.Endgame.startGammaConstant ^ 2 *
    (1 + ε ^ (-(1 / 3 : ℝ))))

/-- For actual suitable solutions the cylinder cost is bounded by the fine-cell
trace cost of any finite-energy field agreeing with the gradient on that cell. -/
theorem suitable_weighted_activity_le_cell_trace
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (k : ℕ) (D : ParabolicPoint → Fin 3 → Vec3)
    (hD : AEStronglyMeasurable D volume) (hfinite : (∫⁻ a, ‖D a‖ₑ ^ (2 : ℕ)) < ⊤)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) {z : ParabolicPoint} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hG : ε ≤ rawSymmetricL3Activity u p z r)
    (hz : z ∈ shiftedParabolicDyadicCell g Q)
    (hsideLo : r / 32 ≤ dyadicScale Q.scale) (hsideHi : dyadicScale Q.scale < r / 16)
    (hdom : closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I)
    (hDDu : Set.EqOn D Du (shiftedParabolicDyadicCell g Q))
    (hcmp : ENNReal.ofReal (rawSymmetricMixedGradientActivity Du z (r / 512)) ≤
      512 * dyadicMixedGradientActivity g Du Q) :
    dyadicReciprocalLogWeight k Q.scale * rawSymmetricMixedGradientActivity Du z (r / 512) /
        Real.sqrt (rawSymmetricL3Activity u p z r) ≤
      traceActivityConstant ε * dyadicGradientTraceCost k g D Q := by
  let B := 1 + 1536 * CKN.Core.Endgame.startGammaConstant ^ 2 *
    (1 + ε ^ (-(1 / 3 : ℝ)))
  have hB : 0 < B := by dsimp [B]; positivity
  have he := rawSymmetricMixedGradientActivity_nonneg Du z (by positivity : 0 ≤ r / 512)
  have hmixeq := dyadicMixedGradientActivity_congr_on_cell g Q hDDu
  have hmixfinite := dyadicMixedGradientActivity_lt_top D hD hfinite g Q
  have hecell : rawSymmetricMixedGradientActivity Du z (r / 512) ≤
      512 * (dyadicMixedGradientActivity g D Q).toReal := by
    rw [← hmixeq] at hcmp
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) hmixfinite.ne) hcmp
    simpa only [ENNReal.toReal_ofReal he, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hb
  have hmass : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)) =
      ∫⁻ a in shiftedParabolicDyadicCell g Q, ‖Du a‖ₑ ^ (2 : ℝ) := by
    apply setLIntegral_congr_fun (shiftedParabolicDyadicCell_measurable g Q)
    intro a ha
    dsimp only
    rw [hDDu ha, ENNReal.rpow_two]
  have hcharge : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)).toReal /
      dyadicScale Q.scale ≤ B * rawSymmetricL3Activity u p z r := by
    rw [hmass]
    exact persistent_shiftedCell_dissipation_le_activity hsol g Q hr hε hG hz
      hsideLo hsideHi hdom
  have hzero : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)).toReal /
      dyadicScale Q.scale = 0 → (dyadicMixedGradientActivity g D Q).toReal = 0 := by
    intro hzero
    have hzreal : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)).toReal = 0 :=
      (div_eq_zero_iff.1 hzero).resolve_right (dyadicScale_pos _).ne'
    have hmassfinite : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite.ne (setLIntegral_le_lintegral _ _)
    have hzext : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)) = 0 := by
      rw [← ENNReal.ofReal_toReal hmassfinite, hzreal, ENNReal.ofReal_zero]
    rw [dyadicMixedGradientActivity_eq_zero_of_dissipation_eq_zero D hD g Q hzext,
      ENNReal.toReal_zero]
  exact weighted_activity_le_trace_cost he
    (div_nonneg ENNReal.toReal_nonneg (dyadicScale_pos _).le) (hε.trans_le hG)
    (zero_lt_one.trans_le (one_le_dyadicLogFactor k Q.scale)) hB hecell hcharge hzero

end FluidSingularSets
