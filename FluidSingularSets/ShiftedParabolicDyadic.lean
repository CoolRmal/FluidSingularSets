-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.ParabolicDyadic
public import FluidSingularSets.AdjacentIntervals
public import CKN.Foundation.Parabolic.Vec3Norm
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Sixteen coherent adjacent parabolic dyadic grids

The spatial shift alternates between one third and two thirds at consecutive
integer levels. The temporal shift is one third at every level of the base-four
time grid. A fixed choice of shifted or unshifted grid in each of the four
coordinates yields a laminar grid. Adjacent interval containment then produces
an actual cell containing any sufficiently small product rectangle.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The spatial phase of the shifted grid alternates at every integral level. -/
def alternatingDyadicPhase (n : ℤ) : ℝ := if Even n then 1 / 3 else 2 / 3

/-- A fixed choice of grid in the three spatial coordinates and in time. -/
abbrev ParabolicGridShift := (Fin 3 → Bool) × Bool

/-- There are exactly sixteen coordinate shift choices. -/
theorem card_parabolicGridShift : Fintype.card ParabolicGridShift = 16 := by
  norm_num [ParabolicGridShift, Fintype.card_prod, Fintype.card_fun]

/-- The selected spatial phase at a level and coordinate. -/
def shiftedSpatialPhase (g : ParabolicGridShift) (n : ℤ) (i : Fin 3) : ℝ :=
  if g.1 i then alternatingDyadicPhase n else 0

/-- The selected temporal phase is fixed across the base-four time levels. -/
def shiftedTimePhase (g : ParabolicGridShift) : ℝ := if g.2 then 1 / 3 else 0

/-- A half-open grid interval with the specified side length, phase, and integer corner. -/
def shiftedGridInterval (ℓ σ : ℝ) (a : ℤ) : Set ℝ :=
  Ico (((a : ℝ) + σ) * ℓ) (((a : ℝ) + σ + 1) * ℓ)

/-- A spatial cube in one of the eight coherent shifted spatial grids. -/
def shiftedDyadicCube (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) : Set Vec3 :=
  univ.pi (fun i => shiftedGridInterval (dyadicScale n) (shiftedSpatialPhase g n i) (a i))

/-- A temporal cell in one of the two coherent base-four grids. -/
def shiftedParabolicDyadicTime (g : ParabolicGridShift) (n a : ℤ) : Set ℝ :=
  shiftedGridInterval (dyadicScale (2 * n)) (shiftedTimePhase g) a

/-- A product cell of one of the sixteen adjacent parabolic grids. -/
def shiftedParabolicDyadicCell (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) : Set ParabolicPoint :=
  shiftedDyadicCube g Q.scale Q.corner ×ˢ
    shiftedParabolicDyadicTime g Q.scale Q.timeCorner

/-- The nonzero spatial phase always lies between one third and two thirds. -/
theorem alternatingDyadicPhase_bounds (n : ℤ) :
    1 / 3 ≤ alternatingDyadicPhase n ∧ alternatingDyadicPhase n ≤ 2 / 3 := by
  unfold alternatingDyadicPhase
  split <;> norm_num

/-- The alternating phases have an integer discrepancy at adjacent spatial levels. -/
theorem alternatingDyadicPhase_coherent (n : ℤ) :
    ∃ c : ℤ, 2 * alternatingDyadicPhase n - alternatingDyadicPhase (n + 1) = c := by
  have hpar : Even (n + 1) ↔ ¬Even n := by
    rw [even_iff_two_dvd, even_iff_two_dvd, Int.dvd_iff_emod_eq_zero,
      Int.dvd_iff_emod_eq_zero]
    omega
  by_cases hn : Even n
  · refine ⟨0, ?_⟩
    simp only [alternatingDyadicPhase, ite_eq_left hn,
      ite_eq_right (mt hpar.mp (not_not.mpr hn))]
    norm_num
  · refine ⟨1, ?_⟩
    simp only [alternatingDyadicPhase, ite_eq_right hn, ite_eq_left (hpar.mpr hn)]
    norm_num

/-- Each selected spatial phase satisfies the same base-two coherence law. -/
theorem shiftedSpatialPhase_coherent (g : ParabolicGridShift) (n : ℤ) (i : Fin 3) :
    ∃ c : ℤ, 2 * shiftedSpatialPhase g n i - shiftedSpatialPhase g (n + 1) i = c := by
  cases h : g.1 i
  · exact ⟨0, by simp [shiftedSpatialPhase, h]⟩
  · simpa only [shiftedSpatialPhase, h, Bool.true_eq, ite_true] using
      alternatingDyadicPhase_coherent n

/-- Each selected temporal phase satisfies the base-four coherence law. -/
theorem shiftedTimePhase_coherent (g : ParabolicGridShift) :
    ∃ c : ℤ, 4 * shiftedTimePhase g - shiftedTimePhase g = c := by
  cases h : g.2
  · exact ⟨0, by simp [shiftedTimePhase, h]⟩
  · exact ⟨1, by norm_num [shiftedTimePhase, h]⟩

/-- The spatial side length doubles on passing from a fine level to its predecessor. -/
theorem dyadicScale_step (n : ℤ) : dyadicScale n = 2 * dyadicScale (n + 1) := by
  dsimp [dyadicScale]
  rw [show -n = -(n + 1) + 1 by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The temporal side length quadruples on the corresponding step. -/
theorem dyadicTimeScale_step (n : ℤ) :
    dyadicScale (2 * n) = 4 * dyadicScale (2 * (n + 1)) := by
  rw [dyadicScale_two_mul, dyadicScale_two_mul, dyadicScale_step n]
  ring

/-- Adjacent-level coherence gives an integral side ratio and phase discrepancy
between any two ordered integer levels. -/
theorem coherent_grid_ratio (b : ℤ) (ℓ σ : ℤ → ℝ) (hb : 0 < b)
    (hstep : ∀ n, ℓ n = (b : ℝ) * ℓ (n + 1))
    (hphase : ∀ n, ∃ c : ℤ, (b : ℝ) * σ n - σ (n + 1) = c)
    (n m : ℤ) (hnm : n ≤ m) :
    ∃ M c : ℤ, 0 < M ∧ ℓ n = (M : ℝ) * ℓ m ∧
      (M : ℝ) * σ n - σ m = c := by
  induction m, hnm using Int.leInduction with
  | base => exact ⟨1, 0, by norm_num, by simp, by simp⟩
  | succ m _ ih =>
      obtain ⟨M, c, hM, hℓ, hc⟩ := ih
      obtain ⟨j, hj⟩ := hphase m
      refine ⟨M * b, b * c + j, mul_pos hM hb, ?_, ?_⟩
      · calc
          ℓ n = (M : ℝ) * ℓ m := hℓ
          _ = (M : ℝ) * ((b : ℝ) * ℓ (m + 1)) := by rw [hstep m]
          _ = ((M * b : ℤ) : ℝ) * ℓ (m + 1) := by push_cast; ring
      · calc
          ((M * b : ℤ) : ℝ) * σ n - σ (m + 1) =
              (b : ℝ) * ((M : ℝ) * σ n - σ m) +
                ((b : ℝ) * σ m - σ (m + 1)) := by push_cast; ring
          _ = (b : ℝ) * (c : ℝ) + (j : ℝ) := by rw [hc, hj]
          _ = ((b * c + j : ℤ) : ℝ) := by push_cast; rfl

/-- Integral side ratios and phase discrepancies force intersecting half-open
grid intervals to be nested. -/
theorem shiftedGridInterval_subset_of_intersect
    {L ℓ σ τ : ℝ} {M c a b : ℤ} (hℓ : 0 < ℓ)
    (hscale : L = (M : ℝ) * ℓ) (hphase : (M : ℝ) * σ - τ = c)
    (hint : (shiftedGridInterval L σ a ∩ shiftedGridInterval ℓ τ b).Nonempty) :
    shiftedGridInterval ℓ τ b ⊆ shiftedGridInterval L σ a := by
  have horigin (d : ℤ) : ((d : ℝ) + σ) * L =
      (((d * M + c : ℤ) : ℝ) + τ) * ℓ := by
    rw [hscale]
    push_cast
    nlinarith [congrArg (fun x : ℝ => x * ℓ) hphase]
  have hend : ((a : ℝ) + σ + 1) * L =
      ((((a + 1) * M + c : ℤ) : ℝ) + τ) * ℓ := by
    convert horigin (a + 1) using 1
    push_cast
    ring
  obtain ⟨x, hxa, hxb⟩ := hint
  change ((a : ℝ) + σ) * L ≤ x ∧ x < ((a : ℝ) + σ + 1) * L at hxa
  change ((b : ℝ) + τ) * ℓ ≤ x ∧ x < ((b : ℝ) + τ + 1) * ℓ at hxb
  rw [horigin a, hend] at hxa
  have hleft : a * M + c ≤ b := by
    apply Int.lt_add_one_iff.mp
    have hreal := lt_of_mul_lt_mul_right (hxa.1.trans_lt hxb.2) hℓ.le
    have hreal' : (((a * M + c : ℤ) : ℝ)) < (b : ℝ) + 1 := by linarith
    exact_mod_cast hreal'
  have hright : b + 1 ≤ (a + 1) * M + c := by
    apply Int.add_one_le_iff.mpr
    have hreal := lt_of_mul_lt_mul_right (hxb.1.trans_lt hxa.2) hℓ.le
    have hreal' : (b : ℝ) < (((a + 1) * M + c : ℤ) : ℝ) := by linarith
    exact_mod_cast hreal'
  intro y hy
  change ((a : ℝ) + σ) * L ≤ y ∧ y < ((a : ℝ) + σ + 1) * L
  rw [horigin a, hend]
  change ((b : ℝ) + τ) * ℓ ≤ y ∧ y < ((b : ℝ) + τ + 1) * ℓ at hy
  have hl : (((a * M + c : ℤ) : ℝ)) ≤ (b : ℝ) := by exact_mod_cast hleft
  have hr : (b : ℝ) + 1 ≤ (((a + 1) * M + c : ℤ) : ℝ) := by exact_mod_cast hright
  constructor
  · have hl' : (((a * M + c : ℤ) : ℝ)) + τ ≤ (b : ℝ) + τ := by linarith
    exact (mul_le_mul_of_nonneg_right hl' hℓ.le).trans hy.1
  · apply hy.2.trans_le
    apply mul_le_mul_of_nonneg_right _ hℓ.le
    linarith

/-- Intersecting spatial coordinate intervals are nested at ordered grid levels. -/
theorem shiftedSpatialInterval_subset_of_intersect
    (g : ParabolicGridShift) (i : Fin 3) {n m a b : ℤ} (hnm : n ≤ m)
    (hint : (shiftedGridInterval (dyadicScale n) (shiftedSpatialPhase g n i) a ∩
      shiftedGridInterval (dyadicScale m) (shiftedSpatialPhase g m i) b).Nonempty) :
    shiftedGridInterval (dyadicScale m) (shiftedSpatialPhase g m i) b ⊆
      shiftedGridInterval (dyadicScale n) (shiftedSpatialPhase g n i) a := by
  obtain ⟨M, c, _, hℓ, hc⟩ := coherent_grid_ratio 2 dyadicScale
    (fun k => shiftedSpatialPhase g k i) (by norm_num) dyadicScale_step
    (fun k => shiftedSpatialPhase_coherent g k i) n m hnm
  exact shiftedGridInterval_subset_of_intersect (dyadicScale_pos m) hℓ hc hint

/-- Intersecting shifted spatial cubes are nested at ordered grid levels. -/
theorem shiftedDyadicCube_subset_of_intersect
    (g : ParabolicGridShift) {n m : ℤ} {a b : DyadicCorner} (hnm : n ≤ m)
    (hint : (shiftedDyadicCube g n a ∩ shiftedDyadicCube g m b).Nonempty) :
    shiftedDyadicCube g m b ⊆ shiftedDyadicCube g n a := by
  obtain ⟨x, hxa, hxb⟩ := hint
  intro y hy
  apply mem_pi.mpr
  intro i _
  apply shiftedSpatialInterval_subset_of_intersect g i hnm
    ⟨x i, mem_pi.mp hxa i (mem_univ i), mem_pi.mp hxb i (mem_univ i)⟩
  exact mem_pi.mp hy i (mem_univ i)

/-- Intersecting shifted temporal cells are nested at ordered spatial levels. -/
theorem shiftedParabolicDyadicTime_subset_of_intersect
    (g : ParabolicGridShift) {n m a b : ℤ} (hnm : n ≤ m)
    (hint : (shiftedParabolicDyadicTime g n a ∩
      shiftedParabolicDyadicTime g m b).Nonempty) :
    shiftedParabolicDyadicTime g m b ⊆ shiftedParabolicDyadicTime g n a := by
  obtain ⟨M, c, _, hℓ, hc⟩ := coherent_grid_ratio 4 (fun k => dyadicScale (2 * k))
    (fun _ => shiftedTimePhase g) (by norm_num) dyadicTimeScale_step
    (fun _ => shiftedTimePhase_coherent g) n m hnm
  exact shiftedGridInterval_subset_of_intersect (dyadicScale_pos (2 * m)) hℓ hc hint

/-- Within a fixed coordinate shift choice, intersecting parabolic cells are nested. -/
theorem shiftedParabolicDyadicCell_subset_of_intersect
    (g : ParabolicGridShift) {Q R : ParabolicDyadicIndex} (hscale : Q.scale ≤ R.scale)
    (hint : (shiftedParabolicDyadicCell g Q ∩ shiftedParabolicDyadicCell g R).Nonempty) :
    shiftedParabolicDyadicCell g R ⊆ shiftedParabolicDyadicCell g Q := by
  obtain ⟨z, hQ, hR⟩ := hint
  exact Set.prod_mono
    (shiftedDyadicCube_subset_of_intersect g hscale ⟨z.1, hQ.1, hR.1⟩)
    (shiftedParabolicDyadicTime_subset_of_intersect g hscale ⟨z.2, hQ.2, hR.2⟩)

/-- Each of the sixteen adjacent grids is laminar over all integral levels. -/
theorem shiftedParabolicDyadicCell_nested_or_disjoint
    (g : ParabolicGridShift) (Q R : ParabolicDyadicIndex) :
    shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R ∨
      shiftedParabolicDyadicCell g R ⊆ shiftedParabolicDyadicCell g Q ∨
      Disjoint (shiftedParabolicDyadicCell g Q) (shiftedParabolicDyadicCell g R) := by
  by_cases hint : (shiftedParabolicDyadicCell g Q ∩ shiftedParabolicDyadicCell g R).Nonempty
  · rcases le_total Q.scale R.scale with hQR | hRQ
    · exact Or.inr (Or.inl (shiftedParabolicDyadicCell_subset_of_intersect g hQR hint))
    · exact Or.inl (shiftedParabolicDyadicCell_subset_of_intersect g hRQ
        (by simpa only [inter_comm] using hint))
  · exact Or.inr (Or.inr (Set.disjoint_left.mpr (by
      intro z hQ hR
      exact hint ⟨z, hQ, hR⟩)))

/-- Every shifted spatial cube is measurable. -/
theorem shiftedDyadicCube_measurable (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) :
    MeasurableSet (shiftedDyadicCube g n a) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i _
  exact measurableSet_Ico

/-- Every shifted product cell is measurable. -/
theorem shiftedParabolicDyadicCell_measurable
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    MeasurableSet (shiftedParabolicDyadicCell g Q) :=
  (shiftedDyadicCube_measurable g Q.scale Q.corner).prod measurableSet_Ico

/-- A shift changes neither the interval length nor its volume. -/
theorem volume_shiftedGridInterval (ℓ σ : ℝ) (a : ℤ) :
    volume (shiftedGridInterval ℓ σ a) = ENNReal.ofReal ℓ := by
  rw [shiftedGridInterval, Real.volume_Ico]
  congr 1
  ring

/-- Shifted spatial cubes have exactly side length cubed as volume. -/
theorem volume_shiftedDyadicCube (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) :
    volume (shiftedDyadicCube g n a) = ENNReal.ofReal (dyadicScale n) ^ (3 : ℕ) := by
  rw [shiftedDyadicCube]
  simp only [shiftedGridInterval]
  rw [Real.volume_pi_Ico]
  have hwidth (i : Fin 3) :
      ((a i : ℝ) + shiftedSpatialPhase g n i + 1) * dyadicScale n -
        ((a i : ℝ) + shiftedSpatialPhase g n i) * dyadicScale n = dyadicScale n := by ring
  simp_rw [hwidth]
  norm_num [Fin.prod_univ_succ]

/-- Shifted parabolic cells retain exact side length to the fifth volume. -/
theorem volume_shiftedParabolicDyadicCell (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) :
    volume (shiftedParabolicDyadicCell g Q) = ENNReal.ofReal (dyadicScale Q.scale ^ 5) := by
  change (volume : Measure (Vec3 × ℝ))
    (shiftedDyadicCube g Q.scale Q.corner ×ˢ
      shiftedParabolicDyadicTime g Q.scale Q.timeCorner) = _
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_shiftedDyadicCube,
    shiftedParabolicDyadicTime, volume_shiftedGridInterval, dyadicScale_two_mul,
    ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le,
    ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le, ← pow_add]

/-- The floor of normalized and shifted position locates a grid interval. -/
theorem mem_shiftedGridInterval_of_floor {ℓ : ℝ} (hℓ : 0 < ℓ) (σ t : ℝ) :
    t ∈ shiftedGridInterval ℓ σ ⌊t / ℓ - σ⌋ := by
  constructor
  · apply (le_div_iff₀ hℓ).mp
    linarith [Int.floor_le (t / ℓ - σ)]
  · apply (div_lt_iff₀ hℓ).mp
    linarith [Int.lt_floor_add_one (t / ℓ - σ)]

/-- Shifted half-open interval corners are unique for positive side length. -/
theorem shiftedGridInterval_corner_unique {ℓ σ t : ℝ} (hℓ : 0 < ℓ) {a b : ℤ}
    (ha : t ∈ shiftedGridInterval ℓ σ a) (hb : t ∈ shiftedGridInterval ℓ σ b) : a = b := by
  apply le_antisymm
  · apply Int.lt_add_one_iff.mp
    have h := lt_of_mul_lt_mul_right (ha.1.trans_lt hb.2) hℓ.le
    have hreal : (a : ℝ) < (b : ℝ) + 1 := by linarith
    exact_mod_cast hreal
  · apply Int.lt_add_one_iff.mp
    have h := lt_of_mul_lt_mul_right (hb.1.trans_lt ha.2) hℓ.le
    have hreal : (b : ℝ) < (a : ℝ) + 1 := by linarith
    exact_mod_cast hreal

/-- The canonical containing index in a fixed shifted grid and at a fixed level. -/
def shiftedParabolicDyadicContaining (g : ParabolicGridShift) (n : ℤ)
    (z : ParabolicPoint) : ParabolicDyadicIndex :=
  ⟨n, fun i => ⌊z.1 i / dyadicScale n - shiftedSpatialPhase g n i⌋,
    ⌊z.2 / dyadicScale (2 * n) - shiftedTimePhase g⌋⟩

/-- Every point belongs to its canonical cell in each shifted grid. -/
theorem mem_shiftedParabolicDyadicContaining
    (g : ParabolicGridShift) (n : ℤ) (z : ParabolicPoint) :
    z ∈ shiftedParabolicDyadicCell g (shiftedParabolicDyadicContaining g n z) := by
  constructor
  · apply mem_pi.mpr
    intro i _
    exact mem_shiftedGridInterval_of_floor (dyadicScale_pos n) _ _
  · exact mem_shiftedGridInterval_of_floor (dyadicScale_pos (2 * n)) _ _

/-- Two same-level cells in a fixed grid containing one point have the same index. -/
theorem shiftedParabolicDyadicIndex_unique_at_scale
    (g : ParabolicGridShift) {Q R : ParabolicDyadicIndex} (hscale : Q.scale = R.scale)
    {z : ParabolicPoint} (hQ : z ∈ shiftedParabolicDyadicCell g Q)
    (hR : z ∈ shiftedParabolicDyadicCell g R) : Q = R := by
  obtain ⟨n, a, b⟩ := Q
  obtain ⟨m, c, d⟩ := R
  dsimp at hscale
  subst m
  have hac : a = c := by
    funext i
    exact shiftedGridInterval_corner_unique (dyadicScale_pos n)
      (mem_pi.mp hQ.1 i (mem_univ i)) (mem_pi.mp hR.1 i (mem_univ i))
  have hbd : b = d := shiftedGridInterval_corner_unique (dyadicScale_pos (2 * n)) hQ.2 hR.2
  subst c
  subst d
  rfl

/-- A fixed shifted grid has exactly one containing cell at every integer level. -/
theorem shiftedParabolicDyadicCell_unique_at_scale
    (g : ParabolicGridShift) (n : ℤ) (z : ParabolicPoint) :
    ∃! Q : ParabolicDyadicIndex, Q.scale = n ∧ z ∈ shiftedParabolicDyadicCell g Q := by
  refine ⟨shiftedParabolicDyadicContaining g n z,
    ⟨rfl, mem_shiftedParabolicDyadicContaining g n z⟩, ?_⟩
  intro Q hQ
  exact shiftedParabolicDyadicIndex_unique_at_scale g hQ.1 hQ.2
    (mem_shiftedParabolicDyadicContaining g n z)

/-- Distinct same-level cells in a fixed shifted grid are disjoint. -/
theorem shiftedParabolicDyadicCell_disjoint_at_scale
    (g : ParabolicGridShift) {Q R : ParabolicDyadicIndex} (hscale : Q.scale = R.scale)
    (hne : Q ≠ R) : Disjoint (shiftedParabolicDyadicCell g Q) (shiftedParabolicDyadicCell g R) := by
  apply Set.disjoint_left.mpr
  intro z hQ hR
  exact hne (shiftedParabolicDyadicIndex_unique_at_scale g hscale hQ hR)

/-- Each shifted grid partitions all space-time at each level without discarding boundaries. -/
theorem iUnion_shiftedParabolicDyadicCell_at_scale (g : ParabolicGridShift) (n : ℤ) :
    (⋃ c : DyadicCorner × ℤ, shiftedParabolicDyadicCell g ⟨n, c.1, c.2⟩) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨⟨(shiftedParabolicDyadicContaining g n z).corner,
      (shiftedParabolicDyadicContaining g n z).timeCorner⟩,
    mem_shiftedParabolicDyadicContaining g n z⟩

/-- The interval containment theorem gives an actual Boolean grid choice. -/
theorem exists_bool_shift_interval {a b ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσ₁ : 1 / 3 ≤ σ) (hσ₂ : σ ≤ 2 / 3) (hwidth : b - a < ℓ / 3) :
    ∃ c : Bool × ℤ,
      Icc a b ⊆ shiftedGridInterval ℓ (if c.1 then σ else 0) c.2 := by
  obtain ⟨θ, hθ, m, hm⟩ := exists_adjacent_interval_cell hℓ hσ₁ hσ₂ hwidth
  rcases mem_insert_iff.mp hθ with hzero | hphase
  · refine ⟨(false, m), ?_⟩
    simpa only [shiftedGridInterval, Bool.false_eq_true, ite_false, hzero] using hm
  · have heq : θ = σ := mem_singleton_iff.mp hphase
    refine ⟨(true, m), ?_⟩
    simpa only [shiftedGridInterval, Bool.true_eq, ite_true, heq] using hm

/-- A sufficiently small product rectangle lies in a cell of one of the sixteen
adjacent parabolic grids, at the prescribed level. -/
theorem exists_shiftedParabolicDyadicCell_contains_rectangle
    (n : ℤ) (a b : Vec3) (s t : ℝ)
    (hwidth : ∀ i, b i - a i < dyadicScale n / 3)
    (htime : t - s < dyadicScale (2 * n) / 3) :
    ∃ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex), Q.scale = n ∧
      (univ.pi (fun i => Icc (a i) (b i)) ×ˢ Icc s t : Set ParabolicPoint) ⊆
        shiftedParabolicDyadicCell g Q := by
  have hsp (i : Fin 3) : ∃ c : Bool × ℤ,
      Icc (a i) (b i) ⊆ shiftedGridInterval (dyadicScale n)
        (if c.1 then alternatingDyadicPhase n else 0) c.2 :=
    exists_bool_shift_interval (dyadicScale_pos n)
      (alternatingDyadicPhase_bounds n).1 (alternatingDyadicPhase_bounds n).2 (hwidth i)
  choose c hc using hsp
  obtain ⟨d, hd⟩ := exists_bool_shift_interval (dyadicScale_pos (2 * n))
    (by norm_num : (1 / 3 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3) htime
  refine ⟨(fun i => (c i).1, d.1), ⟨n, fun i => (c i).2, d.2⟩, rfl, ?_⟩
  intro z hz
  constructor
  · apply mem_pi.mpr
    intro i _
    exact hc i (mem_pi.mp hz.1 i (mem_univ i))
  · exact hd hz.2

/-- A symmetric parabolic box of radius `r` is contained in an adjacent cell
whenever the cell side is at least `16 * r`. -/
theorem exists_shiftedParabolicDyadicCell_contains_box
    (n : ℤ) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hside : 16 * r ≤ dyadicScale n) :
    ∃ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex), Q.scale = n ∧
      (univ.pi (fun i => Icc (z.1 i - r) (z.1 i + r)) ×ˢ
        Icc (z.2 - r ^ 2) (z.2 + r ^ 2) : Set ParabolicPoint) ⊆
          shiftedParabolicDyadicCell g Q := by
  apply exists_shiftedParabolicDyadicCell_contains_rectangle
  · intro i
    linarith
  · rw [dyadicScale_two_mul]
    have hsq : (16 * r) ^ 2 ≤ dyadicScale n ^ 2 :=
      (sq_le_sq₀ (by positivity) (dyadicScale_pos n).le).mpr hside
    nlinarith [sq_pos_of_pos hr]

/-- Every positive radius admits an actual integer dyadic side in the desired range. -/
theorem exists_dyadicScale_for_radius {r : ℝ} (hr : 0 < r) :
    ∃ n : ℤ, 16 * r ≤ dyadicScale n ∧ dyadicScale n < 32 * r := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_mem_Ioc_zpow (by positivity : 0 < 16 * r)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨-(m + 1), ?_, ?_⟩
  · simpa only [dyadicScale, neg_neg] using hm₂
  · rw [dyadicScale, neg_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    linarith

/-- The actual parabolic closed ball is contained in its coordinate box. -/
theorem parabolic_closedBall_subset_box (z : ParabolicPoint) {r : ℝ} (hr : 0 ≤ r) :
    Metric.closedBall z r ⊆ (univ.pi (fun i => Icc (z.1 i - r) (z.1 i + r)) ×ˢ
      Icc (z.2 - r ^ 2) (z.2 + r ^ 2) : Set ParabolicPoint) := by
  intro w hw
  rw [Metric.mem_closedBall, dist_eq_parabolicDist, parabolicDist, max_le_iff] at hw
  constructor
  · apply mem_pi.mpr
    intro i _
    have hi := (abs_apply_le_vec3EuclideanNorm (w.1 - z.1) i).trans hw.1
    change |w.1 i - z.1 i| ≤ r at hi
    rcases abs_le.mp hi with ⟨hlo, hhi⟩
    constructor <;> linarith
  · have htime : |w.2 - z.2| ≤ r ^ 2 := by
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hr).mpr hw.2
      simpa only [Real.sq_sqrt (abs_nonneg _)] using hs
    rcases abs_le.mp htime with ⟨hlo, hhi⟩
    constructor <;> linarith

/-- Every parabolic closed ball is contained in a cell of one of the sixteen grids
whose side lies between sixteen and thirty-two times the radius. -/
theorem exists_adjacent_parabolic_cell (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    ∃ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex),
      16 * r ≤ dyadicScale Q.scale ∧ dyadicScale Q.scale < 32 * r ∧
        Metric.closedBall z r ⊆ shiftedParabolicDyadicCell g Q := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_dyadicScale_for_radius hr
  obtain ⟨g, Q, hQ, hcontain⟩ := exists_shiftedParabolicDyadicCell_contains_box n z hr hn₁
  refine ⟨g, Q, ?_, ?_, (parabolic_closedBall_subset_box z hr.le).trans hcontain⟩
  · simpa only [hQ] using hn₁
  · simpa only [hQ] using hn₂

end FluidSingularSets
