module

public import CKN.Foundation.Euclidean.Dyadic
public import CKN.Foundation.Euclidean.Maximal.StrongType
public import CKN.Foundation.Measure.LayerCake
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic

/-!
# Carleson embedding for finite laminar families

The coefficient condition is imposed only on descendants of each family member. Maximal
members of a superlevel family give a disjoint cover, proving the distribution estimate
needed for the embedding.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- Descendant Carleson bounds control the coefficient sum on any finite subfamily by the
measure of its union. The nested-or-disjoint assumption is the laminar geometry of dyadic cubes. -/
theorem finite_laminar_carleson_sum_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (P S : Finset (Set X)) (α : Set X → ℝ≥0∞) {C : ℝ≥0∞}
    (hSP : S ⊆ P) (hmeas : ∀ A ∈ P, MeasurableSet A)
    (hlam : ∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hcar : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * μ A) :
    (∑ A ∈ S, α A) ≤ C * μ (⋃ A ∈ S, A) := by
  classical
  let R := S.filter (fun A ↦ Maximal (fun B ↦ B ∈ S) A)
  have hRS : R ⊆ S := filter_subset _ _
  have hRP : R ⊆ P := hRS.trans hSP
  have hroots : ∀ A ∈ S, ∃ B ∈ R, A ⊆ B := by
    intro A hA
    obtain ⟨B, hAB, hB⟩ := S.exists_le_maximal hA
    exact ⟨B, mem_filter.2 ⟨hB.1, hB⟩, hAB⟩
  have hdisj : (R : Set (Set X)).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain hAB | hBA | hd := hlam A (hRP hA) B (hRP hB)
    · have heq : A = B := Subset.antisymm hAB ((mem_filter.1 hA).2.2 (hRS hB) hAB)
      exact (hne heq).elim
    · have heq : A = B := Subset.antisymm ((mem_filter.1 hB).2.2 (hRS hA) hBA) hBA
      exact (hne heq).elim
    · exact hd
  calc
    (∑ A ∈ S, α A) ≤ ∑ B ∈ R, ∑ A ∈ S.filter (fun A ↦ A ⊆ B), α A := by
      simp_rw [sum_filter]
      rw [sum_comm]
      apply sum_le_sum
      intro A hA
      obtain ⟨B, hB, hAB⟩ := hroots A hA
      have hsingle := single_le_sum (fun B _ ↦
        show (0 : ℝ≥0∞) ≤ if A ⊆ B then α A else 0 from bot_le) hB
      simpa [hAB] using hsingle
    _ ≤ ∑ B ∈ R, C * μ B := by
      apply sum_le_sum
      intro B hB
      exact (sum_le_sum_of_subset (filter_subset_filter _ hSP)).trans (hcar B (hRP hB))
    _ = C * μ (⋃ B ∈ R, B) := by
      have hmeasure : μ (⋃ B ∈ R, B) = ∑ B ∈ R, μ B := by
        simpa only [id_eq] using
          measure_biUnion_finset hdisj (fun B hB ↦ hmeas B (hRP hB))
      rw [hmeasure, mul_sum]
    _ ≤ C * μ (⋃ A ∈ S, A) := by
      refine mul_le_mul_of_nonneg_left (measure_mono ?_) bot_le
      intro x hx
      obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion₂.2 ⟨B, hRS hB, hxB⟩

/-- Layer cake for a finite moment with extended nonnegative coefficients. -/
theorem finite_ennreal_coefficient_layercake {ι : Type*} (P : Finset ι)
    (α : ι → ℝ≥0∞) (b : ι → ℝ) :
    (∑ i ∈ P, α i * ENNReal.ofReal (b i)) =
      ∫⁻ t in Ioi (0 : ℝ),
        ∑ i ∈ P, (Iio (b i)).indicator (fun _ ↦ α i) t := by
  classical
  rw [lintegral_finsetSum P (fun i _ ↦ measurable_const.indicator measurableSet_Iio)]
  apply sum_congr rfl
  intro i _
  rw [setLIntegral_indicator measurableSet_Iio]
  have hset : Iio (b i) ∩ Ioi (0 : ℝ) = Ioo 0 (b i) := by ext t; simp; tauto
  rw [hset, setLIntegral_const, Real.volume_Ioo, sub_zero]

/-- Carleson coefficients embed into any measurable pointwise majorant of their local values.
The embedding follows from maximal-root stopping and layer cake. -/
theorem finite_carleson_embedding_le_majorant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (P : Finset (Set X)) (α : Set X → ℝ≥0∞) (b : Set X → ℝ)
    (F : X → ℝ≥0∞) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmeas : ∀ A ∈ P, MeasurableSet A)
    (hlam : ∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (hcar : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * μ A)
    (hF : Measurable F) (hfinite : ∀ᵐ x ∂μ, F x < ⊤)
    (hdom : ∀ A ∈ P, ∀ x ∈ A, ENNReal.ofReal (b A) ≤ F x) :
    (∑ A ∈ P, α A * ENNReal.ofReal (b A)) ≤ C * ∫⁻ x, F x ∂μ := by
  classical
  let T : ℝ → ℝ≥0∞ := fun t ↦ ∑ A ∈ P, (Iio (b A)).indicator (fun _ ↦ α A) t
  have hrepr (t : ℝ) : T t = ∑ A ∈ P.filter (fun A ↦ t < b A), α A := by
    dsimp [T]
    rw [sum_filter]
    apply sum_congr rfl
    intro A _
    by_cases hA : t < b A <;> simp [hA]
  have htail : ∀ t > 0, T t ≤ C * μ {x | ENNReal.ofReal t < F x} := by
    intro t ht
    rw [hrepr]
    refine (finite_laminar_carleson_sum_le μ P (P.filter (fun A ↦ t < b A)) α
      (filter_subset _ _) hmeas hlam hcar).trans ?_
    refine mul_le_mul_of_nonneg_left (measure_mono ?_) bot_le
    intro x hx
    obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨hAP, hAb⟩ := mem_filter.1 hA
    have hlt : ENNReal.ofReal t < ENNReal.ofReal (b A) :=
      (ENNReal.ofReal_lt_ofReal_iff (ht.trans hAb)).2 hAb
    exact hlt.trans_le (hdom A hAP x hxA)
  have hFcake : (∫⁻ x, F x ∂μ) = ∫⁻ t in Ioi (0 : ℝ),
      μ {x | ENNReal.ofReal t < F x} := by
    simpa using CKN.Foundation.Measure.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul
      μ hF (by norm_num : (0 : ℝ) < 1) hfinite
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), T t := finite_ennreal_coefficient_layercake P α b
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), C * μ {x | ENNReal.ofReal t < F x} := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htail t ht
    _ = C * ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < F x} :=
      lintegral_const_mul' _ _ hC
    _ = C * ∫⁻ x, F x ∂μ := by rw [← hFcake]

open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

/-- Every point of a dyadic cube controls its average by the Hardy--Littlewood maximal
function. The constant comes from the ratio between the enclosing ball and the cube. -/
theorem dyadic_average_le_maximal (f : Vec3 → ℝ≥0∞) (Q : DyadicIndex)
    {x : Vec3} (hx : x ∈ dyadicCube Q.scale Q.corner) :
    (⨍⁻ y in dyadicCube Q.scale Q.corner, f y ∂volume) ≤
      64 * maximalFunction f x := by
  have hs := dyadicScale_pos Q.scale
  have hsub : dyadicCube Q.scale Q.corner ⊆ Metric.ball x (2 * dyadicScale Q.scale) :=
    (dyadicCube_subset_closedBall hx).trans (Metric.closedBall_subset_ball (by linarith))
  have hvol : volume (Metric.ball x (2 * dyadicScale Q.scale)) =
      64 * volume (dyadicCube Q.scale Q.corner) := by
    rw [volume_metricBall_eq (by positivity), volume_dyadicCube]
    rw [← ENNReal.ofReal_pow hs.le]
    calc
      ENNReal.ofReal ((2 * (2 * dyadicScale Q.scale)) ^ 3) =
          ENNReal.ofReal (64 * dyadicScale Q.scale ^ 3) := by congr 1; ring
      _ = 64 * ENNReal.ofReal (dyadicScale Q.scale ^ 3) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
        norm_num
  calc
    _ ≤ (∫⁻ y in Metric.ball x (2 * dyadicScale Q.scale), f y ∂volume) /
        volume (dyadicCube Q.scale Q.corner) := by
      rw [setLAverage_eq]
      exact ENNReal.div_le_div_right (lintegral_mono_set hsub) _
    _ = 64 * (⨍⁻ y in Metric.ball x (2 * dyadicScale Q.scale), f y ∂volume) := by
      rw [setLAverage_eq, hvol, ← mul_div_assoc]
      exact (ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)).symm
    _ ≤ 64 * maximalFunction f x := by
      gcongr
      exact maximalFunction_average_le (Metric.mem_ball_self (by positivity))

/-- Dyadic Carleson embedding for every real exponent above one. Only descendant coefficient
bounds and membership in the dyadic grid are assumed; the maximal estimate is imported from CKN. -/
theorem finite_dyadic_carleson_embedding (P : Finset (Set Vec3))
    (α : Set Vec3 → ℝ≥0∞) (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ P, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ p ∂volume < ⊤) :
    (∑ A ∈ P, α A * (⨍⁻ x in A, f x ∂volume) ^ p) ≤
      C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p * ∫⁻ x, f x ^ p ∂volume := by
  classical
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hMfinite := ae_lt_top_maximalFunction hf hp hfp
  have havg : ∀ A ∈ P, (⨍⁻ x in A, f x ∂volume) < ⊤ := by
    intro A hA
    obtain ⟨Q, rfl⟩ := hdyadic A hA
    have hvol : volume (dyadicCube Q.scale Q.corner) ≠ 0 := by
      rw [volume_dyadicCube]
      exact ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.2 (dyadicScale_pos _)) _
    obtain ⟨x, hx, hMx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
      (ae_restrict_of_ae hMfinite)
    exact (dyadic_average_le_maximal f Q hx).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hMx)
  let b : Set Vec3 → ℝ := fun A ↦ ((⨍⁻ x in A, f x ∂volume).toReal) ^ p
  let F : Vec3 → ℝ≥0∞ := fun x ↦ (64 * maximalFunction f x) ^ p
  have hb : ∀ A ∈ P, ENNReal.ofReal (b A) = (⨍⁻ x in A, f x ∂volume) ^ p := by
    intro A hA
    dsimp [b]
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0]
    rw [ENNReal.ofReal_toReal (havg A hA).ne]
  have hmeas : ∀ A ∈ P, MeasurableSet A := by
    intro A hA
    obtain ⟨Q, rfl⟩ := hdyadic A hA
    exact dyadicCube_measurable _ _
  have hlam : ∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
    intro A hA B hB
    obtain ⟨Q, rfl⟩ := hdyadic A hA
    obtain ⟨R, rfl⟩ := hdyadic B hB
    exact dyadicCube_nested_or_disjoint Q R
  have hF : Measurable F :=
    ENNReal.continuous_rpow_const.measurable.comp
      (measurable_const.mul (measurable_maximalFunction f))
  have hFfinite : ∀ᵐ x ∂volume, F x < ⊤ := by
    filter_upwards [hMfinite] with x hx
    exact ENNReal.rpow_lt_top_of_nonneg hp0
      (ENNReal.mul_lt_top (by norm_num) hx).ne
  have hdom : ∀ A ∈ P, ∀ x ∈ A, ENNReal.ofReal (b A) ≤ F x := by
    intro A hA x hx
    rw [hb A hA]
    obtain ⟨Q, rfl⟩ := hdyadic A hA
    exact ENNReal.rpow_le_rpow (dyadic_average_le_maximal f Q hx) hp0
  have hFint : (∫⁻ x, F x ∂volume) =
      (64 : ℝ≥0∞) ^ p * ∫⁻ x, maximalFunction f x ^ p ∂volume := by
    dsimp [F]
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
    exact lintegral_const_mul' _ _
      (ENNReal.rpow_lt_top_of_nonneg hp0 (by norm_num)).ne
  calc
    _ = ∑ A ∈ P, α A * ENNReal.ofReal (b A) := by
      apply sum_congr rfl
      intro A hA
      rw [hb A hA]
    _ ≤ C * ∫⁻ x, F x ∂volume :=
      finite_carleson_embedding_le_majorant volume P α b F hC hmeas hlam hcar
        hF hFfinite hdom
    _ = C * ((64 : ℝ≥0∞) ^ p * ∫⁻ x, maximalFunction f x ^ p ∂volume) := by
      rw [hFint]
    _ ≤ C * ((64 : ℝ≥0∞) ^ p *
        (maximalStrongConstant p * ∫⁻ x, f x ^ p ∂volume)) := by
      gcongr
      exact lintegral_rpow_maximalFunction_le hf hp hfp
    _ = _ := by ac_rfl

/-- The exponent required by the dissipation trace argument. -/
theorem finite_dyadic_carleson_embedding_seven_sixths (P : Finset (Set Vec3))
    (α : Set Vec3 → ℝ≥0∞) (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞}
    (hC : C ≠ ⊤)
    (hdyadic : ∀ A ∈ P, ∃ Q : DyadicIndex, A = dyadicCube Q.scale Q.corner)
    (hcar : ∀ A ∈ P, (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ (7 / 6 : ℝ) ∂volume < ⊤) :
    (∑ A ∈ P, α A * (⨍⁻ x in A, f x ∂volume) ^ (7 / 6 : ℝ)) ≤
      C * (64 : ℝ≥0∞) ^ (7 / 6 : ℝ) * maximalStrongConstant (7 / 6) *
        ∫⁻ x, f x ^ (7 / 6 : ℝ) ∂volume :=
  finite_dyadic_carleson_embedding P α f hC (by norm_num) hdyadic hcar hf hfp

end FluidSingularSets
