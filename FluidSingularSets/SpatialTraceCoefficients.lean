module

public import FluidSingularSets.FrostmanCarleson
public import FluidSingularSets.ParabolicRefinement

/-!
# Actual slice coefficients from parabolic mass growth

The time selector and spatial descendant partition turn the scalar Cauchy–Schwarz
bound into a Carleson coefficient bound for a finite measure on the actual cells.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- The parabolic cell over a spatial cube that contains the specified time. -/
def shiftedTraceIndex (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) (t : ℝ) :
    ParabolicDyadicIndex := ⟨n, a, shiftedTimeCellSelector g n t⟩

def shiftedTraceCell (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) (t : ℝ) :
    Set ParabolicPoint := shiftedParabolicDyadicCell g (shiftedTraceIndex g n a t)

/-- The floor time selector locates the actual containing interval. -/
theorem mem_shiftedTimeCellSelector (g : ParabolicGridShift) (n : ℤ) (t : ℝ) :
    t ∈ shiftedParabolicDyadicTime g n (shiftedTimeCellSelector g n t) :=
  mem_shiftedGridInterval_of_floor (dyadicScale_pos (2 * n)) _ _

/-- Fine slice cells over spatial descendants lie inside the root slice cell. -/
theorem shiftedTraceCell_subset_root (g : ParabolicGridShift) (n : ℤ)
    (a : DyadicCorner) (k : ℕ) (t : ℝ) {b : DyadicCorner}
    (hb : b ∈ shiftedSpatialDescendants g n a k) :
    shiftedTraceCell g (n + k) b t ⊆ shiftedTraceCell g n a t := by
  change shiftedDyadicCube g (n + k) b ×ˢ
    shiftedParabolicDyadicTime g (n + k) (shiftedTimeCellSelector g (n + k) t) ⊆
    shiftedDyadicCube g n a ×ˢ
    shiftedParabolicDyadicTime g n (shiftedTimeCellSelector g n t)
  apply Set.prod_mono
  · exact (mem_shiftedSpatialDescendants_iff_subset g n a k b).1 hb
  · exact shiftedParabolicDyadicTime_subset_of_intersect g (by omega)
      ⟨t, mem_shiftedTimeCellSelector g n t, mem_shiftedTimeCellSelector g (n + k) t⟩

/-- At each spatial depth, the slice-cell masses sum to at most the root mass. -/
theorem sum_shiftedTraceCell_mass_le_root (μ : Measure ParabolicPoint) [IsFiniteMeasure μ]
    (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) (k : ℕ) (t : ℝ) :
    (∑ b ∈ shiftedSpatialDescendants g n a k, (μ (shiftedTraceCell g (n + k) b t)).toReal) ≤
      (μ (shiftedTraceCell g n a t)).toReal := by
  have hdisj : ((shiftedSpatialDescendants g n a k : Finset DyadicCorner) :
      Set DyadicCorner).PairwiseDisjoint (fun b ↦ shiftedTraceCell g (n + k) b t) := by
    intro b _hb c _hc hbc
    change Disjoint (shiftedParabolicDyadicCell g (shiftedTraceIndex g (n + k) b t))
      (shiftedParabolicDyadicCell g (shiftedTraceIndex g (n + k) c t))
    apply shiftedParabolicDyadicCell_disjoint_at_scale g
      (Q := shiftedTraceIndex g (n + k) b t) (R := shiftedTraceIndex g (n + k) c t) rfl
    intro h
    exact hbc (congrArg ParabolicDyadicIndex.corner h)
  rw [← ENNReal.toReal_sum (fun b _ ↦ measure_ne_top μ _)]
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  rw [← measure_biUnion_finset hdisj (fun b _ ↦
    shiftedParabolicDyadicCell_measurable g (shiftedTraceIndex g (n + k) b t))]
  apply measure_mono
  intro z hz
  obtain ⟨b, hzb⟩ := mem_iUnion.mp hz
  obtain ⟨hb, hzb⟩ := mem_iUnion.mp hzb
  exact shiftedTraceCell_subset_root g n a k t hb hzb

/-- Side lengths at a fixed depth follow the dyadic geometric sequence. -/
theorem dyadicScale_nat_add_geom (n : ℤ) (k : ℕ) :
    dyadicScale (n + k) = dyadicScale n * (1 / 2 : ℝ) ^ k := by
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ k ≠ 0)).2
  simpa only [mul_comm] using (dyadicScale_nat_add n k).symm

/-- The spatial Carleson coefficient obtained from the actual parabolic cell mass. -/
def spatialTraceCoefficient (μ : Measure ParabolicPoint) (F : ℤ → ℝ)
    (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) (t : ℝ) : ℝ :=
  dyadicScale n * Real.sqrt (dyadicScale n ^ 3 / F n) *
    Real.sqrt ((μ (shiftedTraceCell g n a t)).toReal)

/-- Root Frostman growth alone gives the actual finite-generation spatial Carleson bound.
The constant is uniform in time, in the root, and in the number of generations. -/
theorem finite_spatialTraceCoefficient_sum_le (μ : Measure ParabolicPoint) [IsFiniteMeasure μ]
    (F : ℤ → ℝ) (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) (t : ℝ)
    (L : ℕ) {A : ℝ} (hA : 0 ≤ A) (hF : 0 < F n)
    (hmono : ∀ k : ℕ, F n ≤ F (n + k))
    (hgrowth : (μ (shiftedTraceCell g n a t)).toReal ≤ A * dyadicScale n * F n) :
    (∑ k ∈ range L, ∑ b ∈ shiftedSpatialDescendants g n a k,
      spatialTraceCoefficient μ F g (n + k) b t) ≤
      2 * Real.sqrt A * dyadicScale n ^ 3 := by
  simp only [spatialTraceCoefficient, dyadicScale_nat_add_geom]
  apply dyadic_frostman_carleson_bound L (shiftedSpatialDescendants g n a)
    (fun k b ↦ (μ (shiftedTraceCell g (n + k) b t)).toReal)
    (fun k ↦ F (n + k)) (dyadicScale_pos n).le hF ENNReal.toReal_nonneg hA
  · intro k _
    exact hmono k
  · intro k _ b _
    exact ENNReal.toReal_nonneg
  · intro k _
    exact sum_shiftedTraceCell_mass_le_root μ g n a k t
  · intro k _
    exact (card_shiftedSpatialDescendants g n a k).le
  · exact hgrowth

/-- The actual coefficients are nonnegative whenever their scale weight is positive. -/
theorem spatialTraceCoefficient_nonneg (μ : Measure ParabolicPoint) (F : ℤ → ℝ)
    (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) (t : ℝ) :
    0 ≤ spatialTraceCoefficient μ F g n a t := by
  exact mul_nonneg (mul_nonneg (dyadicScale_pos n).le (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- Every concrete slice coefficient is measurable in time, including grid boundaries. -/
theorem measurable_spatialTraceCoefficient (μ : Measure ParabolicPoint) (F : ℤ → ℝ)
    (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) :
    Measurable (spatialTraceCoefficient μ F g n a) := by
  have hmass : Measurable (fun t : ℝ ↦ (μ (shiftedTraceCell g n a t)).toReal) := by
    exact (measurable_of_countable (fun b : ℤ ↦
      (μ (shiftedParabolicDyadicCell g ⟨n, a, b⟩)).toReal)).comp
        (measurable_shiftedTimeCellSelector g n)
  exact (Real.continuous_sqrt.measurable.comp hmass).const_mul _

/-- The complete descendant coefficient sum has the same Carleson bound as its finite stages. -/
theorem spatialTraceCoefficient_descendant_sum_le (μ : Measure ParabolicPoint)
    [IsFiniteMeasure μ] (F : ℤ → ℝ) (g : ParabolicGridShift)
    (n : ℤ) (a : DyadicCorner) (t : ℝ) {A : ℝ} (hA : 0 ≤ A) (hF : 0 < F n)
    (hmono : ∀ k : ℕ, F n ≤ F (n + k))
    (hgrowth : (μ (shiftedTraceCell g n a t)).toReal ≤ A * dyadicScale n * F n) :
    Summable (fun k ↦ ∑ b ∈ shiftedSpatialDescendants g n a k,
      spatialTraceCoefficient μ F g (n + k) b t) ∧
      (∑' k, ∑ b ∈ shiftedSpatialDescendants g n a k,
        spatialTraceCoefficient μ F g (n + k) b t) ≤
        2 * Real.sqrt A * dyadicScale n ^ 3 := by
  have hnonneg (k : ℕ) : 0 ≤ ∑ b ∈ shiftedSpatialDescendants g n a k,
      spatialTraceCoefficient μ F g (n + k) b t :=
    sum_nonneg (fun b _ ↦ spatialTraceCoefficient_nonneg μ F g (n + k) b t)
  have hbound (L : ℕ) := finite_spatialTraceCoefficient_sum_le μ F g n a t L
    hA hF hmono hgrowth
  have hsum := summable_of_sum_range_le hnonneg hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hbound⟩

/-- An actual spatial descendant index records its depth and its descendant corner. -/
abbrev SpatialTraceDescendant (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) :=
  Σ k : ℕ, (shiftedSpatialDescendants g n a k)

/-- The complete nonnegative coefficient mass has a finite Carleson bound. -/
theorem ennreal_spatialTraceCoefficient_descendant_sum_le (μ : Measure ParabolicPoint)
    [IsFiniteMeasure μ] (F : ℤ → ℝ) (g : ParabolicGridShift)
    (n : ℤ) (a : DyadicCorner) (t : ℝ) {A : ℝ} (hA : 0 ≤ A) (hF : 0 < F n)
    (hmono : ∀ k : ℕ, F n ≤ F (n + k))
    (hgrowth : (μ (shiftedTraceCell g n a t)).toReal ≤ A * dyadicScale n * F n) :
    (∑' q : SpatialTraceDescendant g n a,
      ENNReal.ofReal (spatialTraceCoefficient μ F g (n + q.1) q.2 t)) ≤
      ENNReal.ofReal (2 * Real.sqrt A * dyadicScale n ^ 3) := by
  have hsum := spatialTraceCoefficient_descendant_sum_le μ F g n a t hA hF hmono hgrowth
  have hnonneg (k : ℕ) : 0 ≤ ∑ b ∈ shiftedSpatialDescendants g n a k,
      spatialTraceCoefficient μ F g (n + k) b t :=
    sum_nonneg (fun b _ ↦ spatialTraceCoefficient_nonneg μ F g (n + k) b t)
  calc
    _ = ∑' k, ENNReal.ofReal (∑ b ∈ shiftedSpatialDescendants g n a k,
        spatialTraceCoefficient μ F g (n + k) b t) := by
      rw [show (∑' q : SpatialTraceDescendant g n a,
          ENNReal.ofReal (spatialTraceCoefficient μ F g (n + q.1) q.2 t)) =
          ∑' k, ∑' b : (shiftedSpatialDescendants g n a k),
            ENNReal.ofReal (spatialTraceCoefficient μ F g (n + k) b t) from
        ENNReal.tsum_sigma (fun (k : ℕ) (b : (shiftedSpatialDescendants g n a k)) ↦
          ENNReal.ofReal (spatialTraceCoefficient μ F g (n + k) b t))]
      apply tsum_congr
      intro k
      calc
        _ = ∑ b ∈ shiftedSpatialDescendants g n a k,
            ENNReal.ofReal (spatialTraceCoefficient μ F g (n + k) b t) :=
          Finset.tsum_subtype _ (fun b ↦
            ENNReal.ofReal (spatialTraceCoefficient μ F g (n + k) b t))
        _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun b _ ↦
          spatialTraceCoefficient_nonneg μ F g (n + k) b t)).symm
    _ = ENNReal.ofReal (∑' k, ∑ b ∈ shiftedSpatialDescendants g n a k,
        spatialTraceCoefficient μ F g (n + k) b t) :=
      (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum.2

end FluidSingularSets
