-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.ShiftedParabolicDyadic
public import FluidSingularSets.CountableCarleson
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Spatial Carleson embedding in the adjacent grids

The same maximal-function proof applies to each coherent shifted grid. The actual cube
geometry supplies its measurable, laminar, volume and average bounds.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FluidSingularSets

/-- A cube in a shifted grid lies in the side-length closed ball around any of its points. -/
theorem shiftedDyadicCube_subset_closedBall (g : ParabolicGridShift)
    {n : ℤ} {a : DyadicCorner} {x : Vec3} (hx : x ∈ shiftedDyadicCube g n a) :
    shiftedDyadicCube g n a ⊆ Metric.closedBall x (dyadicScale n) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (dyadicScale_pos n).le).2
  intro i
  have hx' := mem_pi.mp hx i (mem_univ i)
  have hy' := mem_pi.mp hy i (mem_univ i)
  change _ ≤ _ ∧ _ < _ at hx' hy'
  change |y i - x i| ≤ dyadicScale n
  rw [abs_le]
  constructor <;> linarith

/-- Every coherent shifted spatial grid is laminar over all integer levels. -/
theorem shiftedDyadicCube_nested_or_disjoint (g : ParabolicGridShift)
    (Q R : DyadicIndex) :
    shiftedDyadicCube g Q.scale Q.corner ⊆ shiftedDyadicCube g R.scale R.corner ∨
      shiftedDyadicCube g R.scale R.corner ⊆ shiftedDyadicCube g Q.scale Q.corner ∨
      Disjoint (shiftedDyadicCube g Q.scale Q.corner) (shiftedDyadicCube g R.scale R.corner) := by
  by_cases hint : (shiftedDyadicCube g Q.scale Q.corner ∩
      shiftedDyadicCube g R.scale R.corner).Nonempty
  · rcases le_total Q.scale R.scale with hQR | hRQ
    · exact Or.inr (Or.inl (shiftedDyadicCube_subset_of_intersect g hQR hint))
    · exact Or.inl (shiftedDyadicCube_subset_of_intersect g hRQ
        (by simpa only [inter_comm] using hint))
  · exact Or.inr (Or.inr (Set.disjoint_left.mpr (by
      intro x hQ hR
      exact hint ⟨x, hQ, hR⟩)))

/-- Every point of a shifted cube controls its average by the actual maximal function. -/
theorem shifted_dyadic_average_le_maximal (g : ParabolicGridShift)
    (f : Vec3 → ℝ≥0∞) (Q : DyadicIndex)
    {x : Vec3} (hx : x ∈ shiftedDyadicCube g Q.scale Q.corner) :
    (⨍⁻ y in shiftedDyadicCube g Q.scale Q.corner, f y ∂volume) ≤
      64 * maximalFunction f x := by
  have hs := dyadicScale_pos Q.scale
  have hsub : shiftedDyadicCube g Q.scale Q.corner ⊆ Metric.ball x (2 * dyadicScale Q.scale) :=
    (shiftedDyadicCube_subset_closedBall g hx).trans (Metric.closedBall_subset_ball (by linarith))
  have hvol : volume (Metric.ball x (2 * dyadicScale Q.scale)) =
      64 * volume (shiftedDyadicCube g Q.scale Q.corner) := by
    rw [volume_metricBall_eq (by positivity), volume_shiftedDyadicCube]
    rw [← ENNReal.ofReal_pow hs.le]
    calc
      ENNReal.ofReal ((2 * (2 * dyadicScale Q.scale)) ^ 3) =
          ENNReal.ofReal (64 * dyadicScale Q.scale ^ 3) := by congr 1; ring
      _ = 64 * ENNReal.ofReal (dyadicScale Q.scale ^ 3) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
        norm_num
  calc
    _ ≤ (∫⁻ y in Metric.ball x (2 * dyadicScale Q.scale), f y ∂volume) /
        volume (shiftedDyadicCube g Q.scale Q.corner) := by
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
theorem finite_shifted_dyadic_carleson_embedding (g : ParabolicGridShift)
    (P : Finset (Set Vec3))
    (α : Set Vec3 → ℝ≥0∞) (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ P, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner)
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
    have hvol : volume (shiftedDyadicCube g Q.scale Q.corner) ≠ 0 := by
      rw [volume_shiftedDyadicCube]
      exact ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.2 (dyadicScale_pos _)) _
    obtain ⟨x, hx, hMx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
      (ae_restrict_of_ae hMfinite)
    exact (shifted_dyadic_average_le_maximal g f Q hx).trans_lt
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
    exact shiftedDyadicCube_measurable g _ _
  have hlam : ∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
    intro A hA B hB
    obtain ⟨Q, rfl⟩ := hdyadic A hA
    obtain ⟨R, rfl⟩ := hdyadic B hB
    exact shiftedDyadicCube_nested_or_disjoint g Q R
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
    exact ENNReal.rpow_le_rpow (shifted_dyadic_average_le_maximal g f Q hx) hp0
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

/-- Actual dyadic descendant-Carleson bounds imply the full extended nonnegative `Lp`
embedding. No embedding or maximal-function estimate is included in the hypotheses. -/
theorem shifted_dyadic_carleson_embedding (g : ParabolicGridShift)
    (𝒟 : Set (Set Vec3)) (α : Set Vec3 → ℝ≥0∞)
    (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} {p : ℝ} (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner)
    (hcar : ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ p ∂volume < ⊤) :
    (∑' A : 𝒟, α A * (⨍⁻ x in A, f x ∂volume) ^ p) ≤
      C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p * ∫⁻ x, f x ^ p ∂volume := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro P
  let Q : Finset (Set Vec3) := P.image Subtype.val
  have hQD : ∀ A ∈ Q, A ∈ 𝒟 := by
    intro A hA
    obtain ⟨B, _, rfl⟩ := mem_image.1 hA
    exact B.property
  have hbound := finite_shifted_dyadic_carleson_embedding g Q α f hC hp
    (fun A hA ↦ hdyadic A (hQD A hA))
    (fun A hA ↦ hcar A (hQD A hA) Q hQD) hf hfp
  have hsum : (∑ A ∈ Q, α A * (⨍⁻ x in A, f x ∂volume) ^ p) =
      ∑ A ∈ P, α A * (⨍⁻ x in A, f x ∂volume) ^ p := by
    exact sum_image (fun _ _ _ _ h ↦ Subtype.ext h)
  rwa [hsum] at hbound

/-- The full weighted dyadic `Lp` series is a summable real series, with the same explicit
bound as the extended nonnegative embedding. -/
theorem shifted_dyadic_carleson_embedding_summable (g : ParabolicGridShift) (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ≥0∞) (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner)
    (hcar : ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ p ∂volume < ⊤) :
    Summable (fun A : 𝒟 ↦ (α A * (⨍⁻ x in A, f x ∂volume) ^ p).toReal) ∧
      (∑' A : 𝒟, (α A * (⨍⁻ x in A, f x ∂volume) ^ p).toReal) ≤
        (C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
          ∫⁻ x, f x ^ p ∂volume).toReal := by
  have hbound := shifted_dyadic_carleson_embedding g 𝒟 α f hC hp hdyadic hcar hf hfp
  have hB : C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
      (∫⁻ x, f x ^ p ∂volume) ≠ ⊤ := by
    rw [mul_assoc C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hC (carleson_maximal_constant_ne_top hp)) hfp.ne
  have hsum : (∑' A : 𝒟, α A * (⨍⁻ x in A, f x ∂volume) ^ p) ≠ ⊤ :=
    ne_top_of_le_ne_top hB hbound
  have hterm (A : 𝒟) : α A * (⨍⁻ x in A, f x ∂volume) ^ p ≠ ⊤ :=
    ne_top_of_le_ne_top hsum
      (ENNReal.le_tsum (f := fun B : 𝒟 ↦ α B * (⨍⁻ x in B, f x ∂volume) ^ p) A)
  refine ⟨ENNReal.summable_toReal hsum, ?_⟩
  rw [← ENNReal.tsum_toReal_eq hterm]
  exact (ENNReal.toReal_le_toReal hsum hB).2 hbound

/-- The full-family embedding at the dissipation-trace exponent `7/6`. -/
theorem shifted_dyadic_carleson_embedding_summable_seven_sixths
    (g : ParabolicGridShift) (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ≥0∞) (f : Vec3 → ℝ≥0∞) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner)
    (hcar : ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B) ≤ C * volume A)
    (hf : Measurable f) (hfp : ∫⁻ x, f x ^ (7 / 6 : ℝ) ∂volume < ⊤) :
    Summable (fun A : 𝒟 ↦ (α A * (⨍⁻ x in A, f x ∂volume) ^ (7 / 6 : ℝ)).toReal) ∧
      (∑' A : 𝒟, (α A * (⨍⁻ x in A, f x ∂volume) ^ (7 / 6 : ℝ)).toReal) ≤
        (C * (64 : ℝ≥0∞) ^ (7 / 6 : ℝ) * maximalStrongConstant (7 / 6) *
          ∫⁻ x, f x ^ (7 / 6 : ℝ) ∂volume).toReal :=
  shifted_dyadic_carleson_embedding_summable g 𝒟 α f hC (by norm_num) hdyadic hcar hf hfp

/-- A family of cubes in the ordinary dyadic grid is countable. -/
theorem countable_shifted_dyadic_family (g : ParabolicGridShift) (𝒟 : Set (Set Vec3))
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner) :
    𝒟.Countable := by
  apply (Set.countable_range (fun q : ℤ × (Fin 3 → ℤ) ↦ shiftedDyadicCube g q.1 q.2)).mono
  intro A hA
  obtain ⟨Q, rfl⟩ := hdyadic A hA
  exact ⟨(Q.scale, Q.corner), rfl⟩

/-- Integrating the actual slice-wise dyadic embedding bounds the full coefficient series.
The time measure can be Lebesgue measure restricted to the time interval of a root. -/
theorem integrated_shifted_dyadic_carleson_embedding (g : ParabolicGridShift)
    (τ : Measure ℝ) (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ → ℝ≥0∞) (f : ℝ → Vec3 → ℝ≥0∞)
    {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner)
    (hcar : ∀ᵐ t ∂τ, ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B t) ≤ C * volume A)
    (hf : ∀ᵐ t ∂τ, Measurable (f t))
    (hfp : ∀ᵐ t ∂τ, (∫⁻ x, f t x ^ p ∂volume) < ⊤)
    (hmeas : ∀ A : 𝒟, AEMeasurable
      (fun t ↦ α A t * (⨍⁻ x in A, f t x ∂volume) ^ p) τ) :
    (∑' A : 𝒟, ∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≤
      C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        ∫⁻ t, ∫⁻ x, f t x ^ p ∂volume ∂τ := by
  let : Countable 𝒟 := (countable_shifted_dyadic_family g 𝒟 hdyadic).to_subtype
  rw [← lintegral_tsum hmeas]
  calc
    _ ≤ ∫⁻ t, C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        (∫⁻ x, f t x ^ p ∂volume) ∂τ := by
      apply lintegral_mono_ae
      filter_upwards [hcar, hf, hfp] with t htcar htf htfp
      exact shifted_dyadic_carleson_embedding g 𝒟 (fun A ↦ α A t) (f t) hC hp
        hdyadic htcar htf htfp
    _ = _ := by
      apply lintegral_const_mul'
      rw [mul_assoc C]
      exact ENNReal.mul_ne_top hC (carleson_maximal_constant_ne_top hp)

/-- Joint measurability and a finite product-space `Lp` integral supply all slice hypotheses
for the integrated Carleson bound. The coefficient measurability is imposed before averaging. -/
theorem integrated_shifted_dyadic_carleson_embedding_prod (g : ParabolicGridShift)
    (τ : Measure ℝ) (𝒟 : Set (Set Vec3))
    (α : Set Vec3 → ℝ → ℝ≥0∞) (f : ℝ → Vec3 → ℝ≥0∞)
    {C : ℝ≥0∞} {p : ℝ}
    (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner)
    (hcar : ∀ᵐ t ∂τ, ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B t) ≤ C * volume A)
    (hα : ∀ A ∈ 𝒟, Measurable (α A))
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume) < ⊤) :
    (∑' A : 𝒟, ∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≤
      C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
        ∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume := by
  have hpow : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2 ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hf
  have hI : Measurable (fun t ↦ ∫⁻ x, f t x ^ p ∂volume) :=
    hpow.lintegral_prod_right'
  have hprod := lintegral_prod (μ := τ) (ν := volume)
    (fun z : ℝ × Vec3 ↦ f z.1 z.2 ^ p) hpow.aemeasurable
  have hIfinite : (∫⁻ t, ∫⁻ x, f t x ^ p ∂volume ∂τ) ≠ ⊤ := by
    rw [← hprod]
    exact hfp.ne
  have hslice : ∀ᵐ t ∂τ, Measurable (f t) := by
    filter_upwards [] with t
    exact hf.comp (measurable_const.prodMk measurable_id)
  have hsliceFinite : ∀ᵐ t ∂τ, (∫⁻ x, f t x ^ p ∂volume) < ⊤ :=
    ae_lt_top' hI.aemeasurable hIfinite
  have hweighted (A : 𝒟) : AEMeasurable
      (fun t ↦ α A t * (⨍⁻ x in A, f t x ∂volume) ^ p) τ := by
    have havg : Measurable (fun t ↦ ⨍⁻ x in A, f t x ∂volume) := by
      simp_rw [setLAverage_eq]
      exact (hf.lintegral_prod_right' (ν := volume.restrict A)).div measurable_const
    exact ((hα A A.property).mul
      (ENNReal.continuous_rpow_const.measurable.comp havg)).aemeasurable
  have hbound := integrated_shifted_dyadic_carleson_embedding g τ 𝒟 α f hC hp hdyadic hcar
    hslice hsliceFinite hweighted
  rwa [← hprod] at hbound

/-- The integrated coefficients form a summable real series when the product-space `Lp`
mass is finite. The bound retains the explicit constant from the spatial embedding. -/
theorem integrated_shifted_dyadic_carleson_embedding_prod_summable
    (g : ParabolicGridShift) (τ : Measure ℝ)
    (𝒟 : Set (Set Vec3)) (α : Set Vec3 → ℝ → ℝ≥0∞) (f : ℝ → Vec3 → ℝ≥0∞)
    {C : ℝ≥0∞} {p : ℝ} (hC : C ≠ ⊤) (hp : 1 < p)
    (hdyadic : ∀ A ∈ 𝒟, ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner)
    (hcar : ∀ᵐ t ∂τ, ∀ A ∈ 𝒟, ∀ P : Finset (Set Vec3), (∀ B ∈ P, B ∈ 𝒟) →
      (∑ B ∈ P.filter (fun B ↦ B ⊆ A), α B t) ≤ C * volume A)
    (hα : ∀ A ∈ 𝒟, Measurable (α A))
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume) < ⊤) :
    Summable (fun A : 𝒟 ↦
      (∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ).toReal) ∧
      (∑' A : 𝒟, (∫⁻ t, α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ).toReal) ≤
        (C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
          ∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume).toReal := by
  have hbound := integrated_shifted_dyadic_carleson_embedding_prod g τ 𝒟 α f hC hp
    hdyadic hcar hα hf hfp
  have hB : C * (64 : ℝ≥0∞) ^ p * maximalStrongConstant p *
      (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ p ∂τ.prod volume) ≠ ⊤ := by
    rw [mul_assoc C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hC (carleson_maximal_constant_ne_top hp)) hfp.ne
  have hsum : (∑' A : 𝒟, ∫⁻ t,
      α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≠ ⊤ :=
    ne_top_of_le_ne_top hB hbound
  have hterm (A : 𝒟) : (∫⁻ t,
      α A t * (⨍⁻ x in A, f t x ∂volume) ^ p ∂τ) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum
      (ENNReal.le_tsum (f := fun B : 𝒟 ↦
        ∫⁻ t, α B t * (⨍⁻ x in B, f t x ∂volume) ^ p ∂τ) A)
  refine ⟨ENNReal.summable_toReal hsum, ?_⟩
  rw [← ENNReal.tsum_toReal_eq hterm]
  exact (ENNReal.toReal_le_toReal hsum hB).2 hbound

end FluidSingularSets
