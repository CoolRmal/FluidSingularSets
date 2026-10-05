module

public import FluidSingularSets.TraceActivityComparison
public import FluidSingularSets.DyadicActivitySequence
public import FluidSingularSets.WeightedActivity

/-!
# Genuine Frostman traces exclude suitable persistent singular activity

The suitable recurrence is sampled at one dyadic arithmetic progression. The
adjacent-cell choice is injective, so the almost everywhere summable full trace
controls this sampled cost. The divergent reciprocal logarithmic weights force
a contradiction at every point of persistent positive activity.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- A genuine Frostman measure gives zero mass to any set of persistent activity
of an actual suitable solution. Local gradient agreement supplies the finite
energy localization; neither the recurrence nor the trace is assumed. -/
theorem suitable_persistent_set_frostman_null
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {r₀ ρ ε : ℝ}
    (hr₀ : 0 < r₀) (hρ : 0 < ρ) (hε : 0 < ε)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge (k + 1) (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge (k + 1) (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge (k + 1) (ENNReal.ofReal r))
    (D : ParabolicPoint → Fin 3 → Vec3) (hD : AEStronglyMeasurable D volume)
    (hfinite : (∫⁻ a, ‖D a‖ₑ ^ (2 : ℕ)) < ⊤) (E : Set ParabolicPoint)
    (hpersistent : ∀ z ∈ E, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      ε ≤ rawSymmetricL3Activity u p z r ∧
        closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I ∧
        ∀ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex),
          dyadicScale Q.scale < r / 16 → z ∈ shiftedParabolicDyadicCell g Q →
            Set.EqOn D Du (shiftedParabolicDyadicCell g Q)) : μ E = 0 := by
  classical
  obtain ⟨n₀, hae⟩ := exists_frostman_ae_summable_gradient_trace
    μ (k + 1) hC hr₀ hρ hgrowth hdouble D hD hfinite
  obtain ⟨M, A, hA, hsmall, hrec⟩ := exists_suitableFixedScaleRecurrence hε
  have hM : 0 < M := by
    by_contra hnot
    have hzero : M = 0 := Nat.eq_zero_of_not_pos hnot
    norm_num [hzero] at hsmall
  have hMInt : 0 < (M : ℤ) := by exact_mod_cast hM
  obtain ⟨nFine, hnFine⟩ := (Set.finite_range n₀).bddAbove
  have hexcluded : ∀ᵐ z ∂μ, z ∉ E := by
    filter_upwards [hae] with z hzsum
    intro hzE
    obtain ⟨R, hR, hper⟩ := hpersistent z hzE
    obtain ⟨nRadius, _, hnRadius⟩ := exists_dyadicScale_near_radius
      (show 0 < R / 2 by positivity)
    have hrad : dyadicScale nRadius ≤ R := by linarith only [hnRadius]
    obtain ⟨N, hN, hwpos, hwanti, hwdiv, _⟩ :=
      exists_positive_antitone_nonsummable_dyadicLogWeight_tail k hMInt
        (max nFine (nRadius + 5))
    have hNfine : nFine ≤ N := (le_max_left _ _).trans hN
    have hNradius : nRadius ≤ N - 5 := by
      have h := (le_max_right nFine (nRadius + 5)).trans hN
      omega
    let r := dyadicActivityRadius N M
    let G : ℕ → ℝ := fun j ↦ rawSymmetricL3Activity u p z (r j)
    let e : ℕ → ℝ := fun j ↦ rawSymmetricMixedGradientActivity Du z (r j / 512)
    let w : ℕ → ℝ := fun j ↦ dyadicReciprocalLogWeight (k + 1)
      (dyadicLogLevel N (M : ℤ) j)
    have hrpos (j : ℕ) : 0 < r j := dyadicActivityRadius_pos N M j
    have hrR (j : ℕ) : r j ≤ R :=
      (dyadicActivityRadius_le_initial N M j).trans
        ((dyadicScale_antitone hNradius).trans hrad)
    have hp (j : ℕ) := hper (r j) (hrpos j) (hrR j)
    obtain ⟨P, hP, hPinj⟩ := exists_injective_dyadicActivity_cells Du z N hM
    let s : ℕ → Σ g, {Q : ParabolicDyadicIndex // n₀ g ≤ Q.scale} := fun j ↦
      ⟨(P j).1, ⟨(P j).2, by
        rw [(hP j).1]
        exact (hnFine (Set.mem_range_self (P j).1)).trans
          (hNfine.trans (dyadicLogLevel_ge_initial N (Int.natCast_nonneg M) j))⟩⟩
    have hsinj : Function.Injective s := by
      intro i j hij
      apply hPinj
      exact congrArg (fun a : Σ g, {Q : ParabolicDyadicIndex // n₀ g ≤ Q.scale} ↦
        (a.1, a.2.val)) hij
    have hs := hzsum.comp_injective hsinj
    have hcost (j : ℕ) : w j * e j / Real.sqrt (G j) ≤
        traceActivityConstant ε *
          (shiftedParabolicDyadicCell (s j).1 (s j).2).indicator
            (fun _ ↦ dyadicGradientTraceCost (k + 1) (s j).1 D (s j).2) z := by
      obtain ⟨hlevel, hlo, hhi, hz, _, hcmp⟩ := hP j
      have h := suitable_weighted_activity_le_cell_trace hsol (k + 1) D hD hfinite
        (P j).1 (P j).2 (hrpos j) hε (hp j).1 hz hlo hhi (hp j).2.1
        ((hp j).2.2 _ _ hhi hz) hcmp
      simpa only [s, Set.indicator_of_mem hz, hlevel, w, e, G, r] using h
    have hsum : Summable (fun j ↦ w j * e j / Real.sqrt (G j)) :=
      (hs.mul_left (traceActivityConstant ε)).of_nonneg_of_le
        (fun j ↦ div_nonneg (mul_nonneg (hwpos j).le
          (rawSymmetricMixedGradientActivity_nonneg Du z
            (div_nonneg (hrpos j).le (by norm_num))))
          (Real.sqrt_nonneg _)) hcost
    apply persistent_activity_weighted_not_summable G e w hε hA.le
      (fun j ↦ (hp j).1)
      (fun j ↦ rawSymmetricMixedGradientActivity_nonneg Du z
        (div_nonneg (hrpos j).le (by norm_num)))
      (fun j ↦ (hwpos j).le) hwanti hwdiv _ hsum
    intro j
    have h := hrec Ω I q u Du p hsol z (r j) (hrpos j) (hp j).2.1 (hp j).1
    simpa only [G, e, r, dyadicActivityRadius_succ] using h
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hexcluded

end FluidSingularSets
