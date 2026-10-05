-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Euclidean.Dyadic
public import Mathlib.Tactic

/-!
# The parabolic dyadic product grid

At spatial level `n : ℤ`, the temporal interval is a dyadic interval at level
`2 * n`. Thus its length is the square of the spatial side length. Half-open
cells form an exact partition at every level, including grid boundaries, and
cells at different levels are nested or disjoint.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Integral spatial level, spatial corner, and temporal corner of a cell. -/
structure ParabolicDyadicIndex where
  scale : ℤ
  corner : DyadicCorner
  timeCorner : ℤ
  deriving DecidableEq

instance : Countable ParabolicDyadicIndex := by
  let f : ParabolicDyadicIndex → ℤ × DyadicCorner × ℤ := fun Q =>
    (Q.scale, Q.corner, Q.timeCorner)
  apply Function.Injective.countable (f := f)
  intro Q R h
  obtain ⟨n, a, b⟩ := Q
  obtain ⟨m, c, d⟩ := R
  have hn : n = m := congrArg Prod.fst h
  have ha : a = c := congrArg (fun p => p.2.1) h
  have hb : b = d := congrArg (fun p => p.2.2) h
  subst m
  subst c
  subst d
  rfl

/-- A half-open temporal interval with length `dyadicScale n ^ 2`. -/
def parabolicDyadicTime (n a : ℤ) : Set ℝ :=
  Ico ((a : ℝ) * dyadicScale (2 * n)) (((a : ℝ) + 1) * dyadicScale (2 * n))

/-- A parabolic cell: a spatial cube times a temporal interval of squared length. -/
def parabolicDyadicCell (Q : ParabolicDyadicIndex) : Set ParabolicPoint :=
  dyadicCube Q.scale Q.corner ×ˢ parabolicDyadicTime Q.scale Q.timeCorner

/-- The unique index at the prescribed spatial level containing the point. -/
def parabolicDyadicContaining (n : ℤ) (z : ParabolicPoint) : ParabolicDyadicIndex :=
  ⟨n, dyadicCorner n z.1, ⌊z.2 / dyadicScale (2 * n)⌋⟩

/-- Doubling the grid level squares its side length. -/
theorem dyadicScale_two_mul (n : ℤ) :
    dyadicScale (2 * n) = dyadicScale n ^ (2 : ℕ) := by
  dsimp [dyadicScale]
  rw [show -(2 * n) = (-n) * 2 by ring, zpow_mul]
  simp only [zpow_ofNat]

/-- Temporal membership is an ordinary half-open interval condition. -/
@[simp] theorem mem_parabolicDyadicTime {n a : ℤ} {t : ℝ} :
    t ∈ parabolicDyadicTime n a ↔
      (a : ℝ) * dyadicScale (2 * n) ≤ t ∧
        t < ((a : ℝ) + 1) * dyadicScale (2 * n) := Iff.rfl

/-- A scalar interval embeds as the constant-coordinate spatial dyadic cube. -/
theorem mem_parabolicDyadicTime_iff_cube {n a : ℤ} {t : ℝ} :
    t ∈ parabolicDyadicTime n a ↔
      (fun _ : Fin 3 => t) ∈ dyadicCube (2 * n) (fun _ => a) := by
  rw [mem_dyadicCube]
  exact ⟨fun ht _ => ht, fun ht => ht 0⟩

/-- Time intervals, and hence their product cells, are measurable. -/
theorem parabolicDyadicTime_measurable (n a : ℤ) :
    MeasurableSet (parabolicDyadicTime n a) := measurableSet_Ico

/-- Every product cell is measurable in the parabolic point's Borel sigma algebra. -/
theorem parabolicDyadicCell_measurable (Q : ParabolicDyadicIndex) :
    MeasurableSet (parabolicDyadicCell Q) :=
  (dyadicCube_measurable Q.scale Q.corner).prod
    (parabolicDyadicTime_measurable Q.scale Q.timeCorner)

/-- The temporal interval has exactly the square of the spatial side length as volume. -/
theorem volume_parabolicDyadicTime (n a : ℤ) :
    volume (parabolicDyadicTime n a) = ENNReal.ofReal (dyadicScale n ^ 2) := by
  rw [parabolicDyadicTime, Real.volume_Ico]
  congr 1
  rw [dyadicScale_two_mul]
  ring

/-- A three-dimensional parabolic product cell has exactly side length to the fifth volume. -/
theorem volume_parabolicDyadicCell (Q : ParabolicDyadicIndex) :
    volume (parabolicDyadicCell Q) = ENNReal.ofReal (dyadicScale Q.scale ^ 5) := by
  change (volume : Measure (Vec3 × ℝ))
    (dyadicCube Q.scale Q.corner ×ˢ parabolicDyadicTime Q.scale Q.timeCorner) = _
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_dyadicCube,
    volume_parabolicDyadicTime, ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le,
    ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le]
  rw [← pow_add]

/-- Cell volume is positive at every integral level. -/
theorem volume_parabolicDyadicCell_pos (Q : ParabolicDyadicIndex) :
    0 < volume (parabolicDyadicCell Q) := by
  rw [volume_parabolicDyadicCell]
  exact ENNReal.ofReal_pos.mpr (pow_pos (dyadicScale_pos Q.scale) _)

/-- Cell volume is finite at every integral level. -/
theorem volume_parabolicDyadicCell_lt_top (Q : ParabolicDyadicIndex) :
    volume (parabolicDyadicCell Q) < (∞ : ℝ≥0∞) := by
  rw [volume_parabolicDyadicCell]
  exact ENNReal.ofReal_lt_top

/-- Every cell contains a point, independently of its volume calculation. -/
theorem parabolicDyadicCell_nonempty (Q : ParabolicDyadicIndex) :
    (parabolicDyadicCell Q).Nonempty := by
  obtain ⟨x, hx⟩ := dyadicCube_nonempty Q.scale Q.corner
  refine ⟨(x, (Q.timeCorner : ℝ) * dyadicScale (2 * Q.scale)), hx, le_rfl, ?_⟩
  have hs := dyadicScale_pos (2 * Q.scale)
  nlinarith only [hs]

/-- The floor of normalized time locates its half-open temporal cell. -/
theorem mem_parabolicDyadicTime_of_floor (n : ℤ) (t : ℝ) :
    t ∈ parabolicDyadicTime n ⌊t / dyadicScale (2 * n)⌋ := by
  constructor
  · exact (le_div_iff₀ (dyadicScale_pos (2 * n))).mp (Int.floor_le _)
  · exact (div_lt_iff₀ (dyadicScale_pos (2 * n))).mp (Int.lt_floor_add_one _)

/-- Half-open temporal cells have unique corners at each level. -/
theorem parabolicDyadicTime_corner_unique {n a b : ℤ} {t : ℝ}
    (ha : t ∈ parabolicDyadicTime n a) (hb : t ∈ parabolicDyadicTime n b) : a = b := by
  have h := dyadicCorner_unique (mem_parabolicDyadicTime_iff_cube.mp ha)
    (mem_parabolicDyadicTime_iff_cube.mp hb)
  exact congrFun h 0

/-- Every point belongs to its canonical cell. -/
theorem mem_parabolicDyadicContaining (n : ℤ) (z : ParabolicPoint) :
    z ∈ parabolicDyadicCell (parabolicDyadicContaining n z) :=
  ⟨mem_dyadicCube_of_corner n z.1, mem_parabolicDyadicTime_of_floor n z.2⟩

/-- Two cells at the same level containing one point have identical indices. -/
theorem parabolicDyadicIndex_unique_at_scale
    {Q R : ParabolicDyadicIndex} (hscale : Q.scale = R.scale) {z : ParabolicPoint}
    (hQ : z ∈ parabolicDyadicCell Q) (hR : z ∈ parabolicDyadicCell R) : Q = R := by
  obtain ⟨n, a, b⟩ := Q
  obtain ⟨m, c, d⟩ := R
  dsimp at hscale
  subst m
  have hac : a = c := dyadicCorner_unique hQ.1 hR.1
  have hbd : b = d := parabolicDyadicTime_corner_unique hQ.2 hR.2
  subst c
  subst d
  rfl

/-- Distinct integral-scale indices represent distinct cells. -/
theorem parabolicDyadicCell_injective : Function.Injective parabolicDyadicCell := by
  intro Q R hcell
  have hvol := congrArg (fun A => (volume A).toReal) hcell
  rw [volume_parabolicDyadicCell, volume_parabolicDyadicCell,
    ENNReal.toReal_ofReal (pow_nonneg (dyadicScale_pos Q.scale).le _),
    ENNReal.toReal_ofReal (pow_nonneg (dyadicScale_pos R.scale).le _)] at hvol
  have hs : dyadicScale Q.scale = dyadicScale R.scale :=
    (pow_left_inj₀ (dyadicScale_pos Q.scale).le (dyadicScale_pos R.scale).le
      (by norm_num : (5 : ℕ) ≠ 0)).mp hvol
  have hn : Q.scale = R.scale := by
    have hneg := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hs
    exact neg_injective hneg
  obtain ⟨z, hz⟩ := parabolicDyadicCell_nonempty Q
  exact parabolicDyadicIndex_unique_at_scale hn hz (hcell ▸ hz)

/-- The product cells give a unique cell at each integral spatial level. -/
theorem parabolicDyadicCell_unique_at_scale (n : ℤ) (z : ParabolicPoint) :
    ∃! Q : ParabolicDyadicIndex, Q.scale = n ∧ z ∈ parabolicDyadicCell Q := by
  refine ⟨parabolicDyadicContaining n z, ⟨rfl, mem_parabolicDyadicContaining n z⟩, ?_⟩
  intro Q hQ
  exact parabolicDyadicIndex_unique_at_scale hQ.1 hQ.2 (mem_parabolicDyadicContaining n z)

/-- The cells at a fixed scale partition all space-time, including grid boundaries. -/
theorem iUnion_parabolicDyadicCell_at_scale (n : ℤ) :
    (⋃ c : DyadicCorner × ℤ, parabolicDyadicCell ⟨n, c.1, c.2⟩) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨⟨dyadicCorner n z.1, ⌊z.2 / dyadicScale (2 * n)⌋⟩,
    mem_parabolicDyadicContaining n z⟩

/-- Distinct cells at one scale are disjoint. -/
theorem parabolicDyadicCell_disjoint_at_scale
    {Q R : ParabolicDyadicIndex} (hscale : Q.scale = R.scale) (hne : Q ≠ R) :
    Disjoint (parabolicDyadicCell Q) (parabolicDyadicCell R) := by
  apply Set.disjoint_left.mpr
  intro z hQ hR
  exact hne (parabolicDyadicIndex_unique_at_scale hscale hQ hR)

/-- Intersecting temporal cells are nested in the direction prescribed by their levels. -/
theorem parabolicDyadicTime_subset_of_intersect {n m a b : ℤ} (hnm : n ≤ m)
    (hint : (parabolicDyadicTime n a ∩ parabolicDyadicTime m b).Nonempty) :
    parabolicDyadicTime m b ⊆ parabolicDyadicTime n a := by
  obtain ⟨t, ht, ht'⟩ := hint
  have htwo : 2 * n ≤ 2 * m := mul_le_mul_of_nonneg_left hnm (by norm_num)
  have hcube := dyadicCube_subset_of_intersect htwo
    ⟨fun _ : Fin 3 => t, mem_parabolicDyadicTime_iff_cube.mp ht,
      mem_parabolicDyadicTime_iff_cube.mp ht'⟩
  intro s hs
  exact mem_parabolicDyadicTime_iff_cube.mpr
    (hcube (mem_parabolicDyadicTime_iff_cube.mp hs))

/-- Intersecting product cells inherit nesting simultaneously in space and time. -/
theorem parabolicDyadicCell_subset_of_intersect
    {Q R : ParabolicDyadicIndex} (hscale : Q.scale ≤ R.scale)
    (hint : (parabolicDyadicCell Q ∩ parabolicDyadicCell R).Nonempty) :
    parabolicDyadicCell R ⊆ parabolicDyadicCell Q := by
  obtain ⟨z, hQ, hR⟩ := hint
  have hx := dyadicCube_subset_of_intersect hscale ⟨z.1, hQ.1, hR.1⟩
  have ht := parabolicDyadicTime_subset_of_intersect hscale ⟨z.2, hQ.2, hR.2⟩
  exact Set.prod_mono hx ht

/-- The whole integral-scale parabolic grid is laminar. -/
theorem parabolicDyadicCell_nested_or_disjoint (Q R : ParabolicDyadicIndex) :
    parabolicDyadicCell Q ⊆ parabolicDyadicCell R ∨
      parabolicDyadicCell R ⊆ parabolicDyadicCell Q ∨
      Disjoint (parabolicDyadicCell Q) (parabolicDyadicCell R) := by
  by_cases hint : (parabolicDyadicCell Q ∩ parabolicDyadicCell R).Nonempty
  · rcases le_total Q.scale R.scale with hQR | hRQ
    · exact Or.inr (Or.inl (parabolicDyadicCell_subset_of_intersect hQR hint))
    · exact Or.inl (parabolicDyadicCell_subset_of_intersect hRQ
        (by simpa only [inter_comm] using hint))
  · exact Or.inr (Or.inr (Set.disjoint_left.mpr (by
      intro z hQ hR
      exact hint ⟨z, hQ, hR⟩)))

end FluidSingularSets
