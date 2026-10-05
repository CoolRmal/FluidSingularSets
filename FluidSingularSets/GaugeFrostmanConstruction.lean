-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.ParabolicFrostmanGeometry
public import FluidSingularSets.GaugeFrostmanApproximations
public import FluidSingularSets.GaugeFrostmanLimit

/-!
# Gauge capacities on the actual parabolic grid

Positive metric gauge measure supplies a positive fixed-scale content. A
countable grid partition then supplies one root region with positive content.
Occupied nodes have gauge capacity at twice their spatial side; empty nodes
have zero capacity. The finite minimum-cut construction gives one positive mass
that can be allocated at every depth of this actual geometric tree.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Convert local real-radius monotonicity to monotonicity on finite extended
nonnegative radii. -/
theorem monotoneOn_gauge_of_monotoneOn_ofReal (h : ℝ≥0∞ → ℝ≥0∞) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hmono : MonotoneOn (fun r => h (ENNReal.ofReal r)) (Icc 0 ρ)) :
    MonotoneOn h (Icc 0 (ENNReal.ofReal ρ)) := by
  intro a ha b hb hab
  have hafin : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha.2
  have hbfin : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb.2
  have harel : a.toReal ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ ha.2
  have hbrel : b.toReal ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ hb.2
  simpa only [ENNReal.ofReal_toReal hafin, ENNReal.ofReal_toReal hbfin] using
    hmono ⟨ENNReal.toReal_nonneg, harel⟩ ⟨ENNReal.toReal_nonneg, hbrel⟩
      (ENNReal.toReal_mono hbfin hab)

/-- Positive content cannot vanish on every member of a countable grid partition. -/
theorem exists_positive_gaugePrecontent_root (h : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞)
    (K : Set ParabolicPoint) (g : ParabolicGridShift) (n : ℤ)
    (hpos : 0 < gaugePrecontent h δ K) :
    ∃ a : DyadicCorner × ℤ,
      0 < gaugePrecontent h δ (K ∩ shiftedParabolicDyadicCell g ⟨n, a.1, a.2⟩) := by
  classical
  by_contra hnone
  have hzero (a : DyadicCorner × ℤ) :
      gaugePrecontent h δ (K ∩ shiftedParabolicDyadicCell g ⟨n, a.1, a.2⟩) = 0 := by
    apply le_antisymm _ zero_le
    apply le_of_not_gt
    exact fun hpositive => hnone ⟨a, hpositive⟩
  have hunion : gaugePrecontent h δ
      (⋃ a : DyadicCorner × ℤ, K ∩ shiftedParabolicDyadicCell g ⟨n, a.1, a.2⟩) = 0 :=
    measure_iUnion_null hzero
  have hcover : K ⊆ ⋃ a : DyadicCorner × ℤ,
      K ∩ shiftedParabolicDyadicCell g ⟨n, a.1, a.2⟩ := by
    intro z hz
    have hcell : z ∈ ⋃ a : DyadicCorner × ℤ,
        shiftedParabolicDyadicCell g ⟨n, a.1, a.2⟩ := by
      rw [iUnion_shiftedParabolicDyadicCell_at_scale]
      exact mem_univ _
    obtain ⟨a, ha⟩ := mem_iUnion.mp hcell
    exact mem_iUnion.mpr ⟨a, hz, ha⟩
  have hKzero : gaugePrecontent h δ K = 0 :=
    le_antisymm ((measure_mono hcover).trans_eq hunion) zero_le
  exact hpos.ne' hKzero

theorem dyadicScale_parabolicTreeIndex_le (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (p : List (Fin 32)) : dyadicScale (parabolicTreeIndex g Q p).scale ≤ dyadicScale Q.scale := by
  rw [parabolicTreeIndex_scale]
  have hratio := dyadicScale_nat_add Q.scale p.length
  have hpow : 1 ≤ (2 : ℝ) ^ p.length := one_le_pow₀ (by norm_num)
  have hpos := dyadicScale_pos (Q.scale + p.length)
  nlinarith only [hratio, hpow, hpos]

/-- Gauge capacity at an occupied node, and zero capacity at an empty node. -/
def parabolicGaugeCapacity (h : ℝ≥0∞ → ℝ≥0∞) (K : Set ParabolicPoint)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (p : List (Fin 32)) : ℝ≥0 := by
  classical
  exact if (parabolicTreeRegion K g Q p).Nonempty then
    (h (ENNReal.ofReal (2 * dyadicScale (parabolicTreeIndex g Q p).scale))).toNNReal else 0

theorem parabolicGaugeCapacity_empty (h : ℝ≥0∞ → ℝ≥0∞) (K : Set ParabolicPoint)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (p : List (Fin 32))
    (hempty : parabolicTreeRegion K g Q p = ∅) : parabolicGaugeCapacity h K g Q p = 0 := by
  simp only [parabolicGaugeCapacity, hempty, Set.not_nonempty_empty, ite_false]

theorem parabolicGaugeCapacity_le (h : ℝ≥0∞ → ℝ≥0∞) (K : Set ParabolicPoint)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (p : List (Fin 32)) :
    (parabolicGaugeCapacity h K g Q p : ℝ≥0∞) ≤
      h (ENNReal.ofReal (2 * dyadicScale (parabolicTreeIndex g Q p).scale)) := by
  classical
  unfold parabolicGaugeCapacity
  split
  · exact ENNReal.coe_toNNReal_le_self
  · exact zero_le

/-- Local monotonicity and one finite gauge value justify every occupied-node
capacity as an upper bound on the gauge cost of its actual region. -/
theorem gauge_cost_le_parabolicGaugeCapacity (h : ℝ≥0∞ → ℝ≥0∞)
    (K : Set ParabolicPoint) (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (ρ : ℝ) (hzero : h 0 = 0) (hmono : MonotoneOn h (Icc 0 (ENNReal.ofReal ρ)))
    (hfinite : h (ENNReal.ofReal ρ) ≠ ∞) (hroot : 2 * dyadicScale Q.scale ≤ ρ)
    (p : List (Fin 32)) :
    h (Metric.ediam (parabolicTreeRegion K g Q p)) ≤
      (parabolicGaugeCapacity h K g Q p : ℝ≥0∞) := by
  classical
  by_cases hregion : (parabolicTreeRegion K g Q p).Nonempty
  · have hnodeρ : ENNReal.ofReal (2 * dyadicScale (parabolicTreeIndex g Q p).scale) ≤
        ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left (dyadicScale_parabolicTreeIndex_le g Q p) (by norm_num)).trans
        hroot)
    have hdiam : Metric.ediam (parabolicTreeRegion K g Q p) ≤
        ENNReal.ofReal (2 * dyadicScale (parabolicTreeIndex g Q p).scale) :=
      (Metric.ediam_mono inter_subset_right).trans
        (ediam_shiftedParabolicDyadicCell_le g (parabolicTreeIndex g Q p))
    have hnodefinite : h (ENNReal.ofReal (2 * dyadicScale (parabolicTreeIndex g Q p).scale)) ≠ ∞ :=
      ne_top_of_le_ne_top hfinite
        (hmono ⟨zero_le, hnodeρ⟩ ⟨zero_le, le_rfl⟩ hnodeρ)
    rw [parabolicGaugeCapacity, ite_eq_left hregion, ENNReal.coe_toNNReal hnodefinite]
    exact hmono ⟨zero_le, hdiam.trans hnodeρ⟩ ⟨zero_le, hnodeρ⟩ hdiam
  · have hempty := not_nonempty_iff_eq_empty.mp hregion
    rw [parabolicGaugeCapacity_empty h K g Q p hempty, hempty, Metric.ediam_empty,
      hzero, ENNReal.coe_zero]

/-- The actual geometric capacities admit one positive mass at every depth. -/
theorem exists_positive_uniform_parabolicGaugeCapacity (h : ℝ≥0∞ → ℝ≥0∞)
    (K : Set ParabolicPoint) (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (δ : ℝ≥0∞) (ρ : ℝ) (hzero : h 0 = 0)
    (hmono : MonotoneOn h (Icc 0 (ENNReal.ofReal ρ)))
    (hfinite : h (ENNReal.ofReal ρ) ≠ ∞) (hrootρ : 2 * dyadicScale Q.scale ≤ ρ)
    (hrootδ : ENNReal.ofReal (2 * dyadicScale Q.scale) ≤ δ)
    (hpos : 0 < gaugePrecontent h δ (K ∩ shiftedParabolicDyadicCell g Q)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ n,
      c ≤ gaugeTreeCapacity (parabolicGaugeCapacity h K g Q) [] n := by
  apply exists_positive_uniform_gaugeTreeCapacity (parabolicTreeRegion K g Q)
    (parabolicGaugeCapacity h K g Q) h δ (parabolicTreeRegion_refines K g Q)
    (fun p => (ediam_parabolicTreeRegion_le_root K g Q p).trans hrootδ)
    (gauge_cost_le_parabolicGaugeCapacity h K g Q ρ hzero hmono hfinite hrootρ) []
  exact hpos

/-- Each chosen atom lies in the original compact set; occupied leaves additionally
place the atom inside its actual terminal region. -/
def parabolicGaugePoint (K : Set ParabolicPoint)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (fallback : K)
    (n : ℕ) (p : Fin n → Fin 32) : K :=
  ⟨gaugeTreeSelectedPoint (parabolicTreeRegion K g Q) fallback (List.ofFn p),
    gaugeTreeSelectedPoint_mem_set (parabolicTreeRegion K g Q) K fallback fallback.property
      (fun _ => inter_subset_left) (List.ofFn p)⟩

theorem parabolicGaugePoint_mem_leaf (h : ℝ≥0∞ → ℝ≥0∞) (K : Set ParabolicPoint)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (fallback : K)
    (n : ℕ) (m : ℝ≥0)
    (hm : m ≤ gaugeTreeCapacity (parabolicGaugeCapacity h K g Q) [] n)
    (p : Fin n → Fin 32)
    (hpos : gaugeTreeNodeMass (parabolicGaugeCapacity h K g Q) [] n m (List.ofFn p) ≠ 0) :
    (parabolicGaugePoint K g Q fallback n p : ParabolicPoint) ∈
      parabolicTreeRegion K g Q (List.ofFn p) := by
  simpa only [parabolicGaugePoint, List.nil_append] using
    gaugeTreeSelectedPoint_mem_of_mass_ne_zero (parabolicTreeRegion K g Q)
      (parabolicGaugeCapacity h K g Q) fallback (parabolicGaugeCapacity_empty h K g Q)
      n [] m hm (List.ofFn p) (by rw [List.length_ofFn]) hpos

/-- The actual finite-stage probability measure on the original compact subtype. -/
def parabolicGaugeProbabilityMeasure (h : ℝ≥0∞ → ℝ≥0∞) (K : Set ParabolicPoint)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) (fallback : K)
    (c : ℝ≥0) (hcpos : 0 < c)
    (hc : ∀ n, c ≤ gaugeTreeCapacity (parabolicGaugeCapacity h K g Q) [] n)
    (n : ℕ) : ProbabilityMeasure K :=
  gaugeTreeProbabilityMeasure (parabolicGaugeCapacity h K g Q) n [] c (hc n) hcpos
    (parabolicGaugePoint K g Q fallback n)

/-- The finite measures obey a uniform bound on every ball at any available
coarse level, using the actual geometric cell count. -/
theorem parabolicGaugeProbabilityMeasure_ball_le (h : ℝ≥0∞ → ℝ≥0∞)
    (K : Set ParabolicPoint) (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (fallback : K) (c : ℝ≥0) (hcpos : 0 < c)
    (hc : ∀ n, c ≤ gaugeTreeCapacity (parabolicGaugeCapacity h K g Q) [] n)
    (k t : ℕ) (z : ParabolicPoint) {r : ℝ} (hr : 0 ≤ r)
    (hside : r ≤ dyadicScale (Q.scale + k)) :
    (parabolicGaugeProbabilityMeasure h K g Q fallback c hcpos hc (k + t) : Measure K)
      (Subtype.val ⁻¹' Metric.ball z r) ≤
        (c : ℝ≥0∞)⁻¹ * (81 * h (ENNReal.ofReal (2 * dyadicScale (Q.scale + k)))) := by
  classical
  let cap := parabolicGaugeCapacity h K g Q
  let P := parabolicTreeBallCells g Q k z r
  let points := parabolicGaugePoint K g Q fallback (k + t)
  have hcover (p : Fin k → Fin 32) (q : Fin t → Fin 32)
      (hmass : gaugeTreeNodeMass cap [] (k + t) c (List.ofFn p ++ List.ofFn q) ≠ 0)
      (hball : points (Fin.append p q) ∈ Subtype.val ⁻¹' Metric.ball z r) : p ∈ P := by
    have hmass' : gaugeTreeNodeMass cap [] (k + t) c (List.ofFn (Fin.append p q)) ≠ 0 := by
      simpa only [List.ofFn_fin_append] using hmass
    have hleaf := parabolicGaugePoint_mem_leaf h K g Q fallback (k + t) c (hc (k + t))
      (Fin.append p q) hmass'
    have hcell := hleaf.2
    rw [List.ofFn_fin_append, parabolicTreeIndex_append] at hcell
    have hparent := parabolicTreeCell_subset_root g (parabolicTreeIndex g Q (List.ofFn p))
      (List.ofFn q) hcell
    change p ∈ Finset.univ.filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨points (Fin.append p q), hparent, Metric.ball_subset_closedBall hball⟩⟩
  have hatomic := gaugeTreeAtomicMeasure_apply_le_nodes cap k t [] c (hc (k + t)) points
    (Subtype.val ⁻¹' Metric.ball z r) P hcover
  have hsum : (∑ p ∈ P, (cap ([] ++ List.ofFn p) : ℝ≥0∞)) ≤
      81 * h (ENNReal.ofReal (2 * dyadicScale (Q.scale + k))) := by
    calc
      _ ≤ ∑ _p ∈ P, h (ENNReal.ofReal (2 * dyadicScale (Q.scale + k))) := by
        apply Finset.sum_le_sum
        intro p _
        simpa only [List.nil_append, parabolicTreeIndex_scale, List.length_ofFn] using
          parabolicGaugeCapacity_le h K g Q (List.ofFn p)
      _ = (P.card : ℝ≥0∞) * h (ENNReal.ofReal (2 * dyadicScale (Q.scale + k))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 81 * h (ENNReal.ofReal (2 * dyadicScale (Q.scale + k))) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_parabolicTreeCells_intersect_ball_le g Q k z hr hside) zero_le
  change ((c : ℝ≥0∞)⁻¹ • gaugeTreeAtomicMeasure cap (k + t) [] c points)
    (Subtype.val ⁻¹' Metric.ball z r) ≤ _
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hatomic.trans hsum) zero_le

/-- A positive radius has a dyadic side between that radius and twice it. -/
theorem exists_dyadicScale_near_radius {r : ℝ} (hr : 0 < r) :
    ∃ n : ℤ, r ≤ dyadicScale n ∧ dyadicScale n < 2 * r := by
  obtain ⟨n, hlo, hhi⟩ := exists_dyadicScale_for_radius (show 0 < r / 16 by positivity)
  exact ⟨n, by linarith only [hlo], by linarith only [hhi]⟩

theorem dyadicScale_lt_imp_lt {n m : ℤ} (h : dyadicScale n < dyadicScale m) : m < n := by
  have hneg : -n < -m := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h
  omega

/-- Local doubling and monotonicity turn the uniform coarse-grid estimates
into eventual bounds in the actual radius of every open ball. -/
theorem parabolicGaugeProbabilityMeasure_eventual_ball_bound (h : ℝ≥0∞ → ℝ≥0∞)
    (K : Set ParabolicPoint) (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (fallback : K) (c : ℝ≥0) (hcpos : 0 < c)
    (hc : ∀ n, c ≤ gaugeTreeCapacity (parabolicGaugeCapacity h K g Q) [] n)
    (ρ : ℝ) (hmono : MonotoneOn h (Icc 0 (ENNReal.ofReal ρ)))
    (hdouble : ∀ r : ℝ, 0 < r → 2 * r ≤ ρ →
      h (ENNReal.ofReal (2 * r)) ≤ 2 * h (ENNReal.ofReal r))
    (z : ParabolicPoint) (r : ℝ) (hr : 0 < r)
    (hrsmall : r < min (dyadicScale Q.scale / 2) (ρ / 4)) :
    ∀ᶠ N in atTop,
      (parabolicGaugeProbabilityMeasure h K g Q fallback c hcpos hc N : Measure K)
        (Subtype.val ⁻¹' Metric.ball z r) ≤
          ((c : ℝ≥0∞)⁻¹ * 324) * h (ENNReal.ofReal r) := by
  obtain ⟨n, hside, hsideUpper⟩ := exists_dyadicScale_near_radius hr
  have hrootlt : dyadicScale n < dyadicScale Q.scale := by
    linarith only [hsideUpper, (lt_min_iff.mp hrsmall).1]
  have hn : Q.scale ≤ n := (dyadicScale_lt_imp_lt hrootlt).le
  let k := (n - Q.scale).toNat
  have hk : Q.scale + (k : ℤ) = n := by dsimp [k]; omega
  have hr4 : 4 * r ≤ ρ := by linarith only [(lt_min_iff.mp hrsmall).2]
  have hr2 : 2 * r ≤ ρ := by linarith only [hr, hr4]
  have hnode4 : ENNReal.ofReal (2 * dyadicScale n) ≤ ENNReal.ofReal (4 * r) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hsideUpper])
  have h4ρ : ENNReal.ofReal (4 * r) ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hr4
  have hgauge : h (ENNReal.ofReal (2 * dyadicScale n)) ≤ 4 * h (ENNReal.ofReal r) := by
    calc
      _ ≤ h (ENNReal.ofReal (4 * r)) :=
        hmono ⟨zero_le, hnode4.trans h4ρ⟩ ⟨zero_le, h4ρ⟩ hnode4
      _ ≤ 2 * h (ENNReal.ofReal (2 * r)) := by
        simpa only [show 2 * (2 * r) = 4 * r by ring] using
          hdouble (2 * r) (by linarith only [hr]) (by linarith only [hr4])
      _ ≤ 2 * (2 * h (ENNReal.ofReal r)) :=
        mul_le_mul_of_nonneg_left (hdouble r hr hr2) (by norm_num)
      _ = 4 * h (ENNReal.ofReal r) := by ring
  filter_upwards [eventually_ge_atTop k] with N hN
  have hdepth : k + (N - k) = N := Nat.add_sub_of_le hN
  have hbase := parabolicGaugeProbabilityMeasure_ball_le h K g Q fallback c hcpos hc
    k (N - k) z hr.le (by simpa only [hk] using hside)
  rw [hdepth, hk] at hbase
  calc
    _ ≤ (c : ℝ≥0∞)⁻¹ * (81 * h (ENNReal.ofReal (2 * dyadicScale n))) := hbase
    _ ≤ (c : ℝ≥0∞)⁻¹ * (81 * (4 * h (ENNReal.ofReal r))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgauge (by norm_num)) zero_le
    _ = ((c : ℝ≥0∞)⁻¹ * 324) * h (ENNReal.ofReal r) := by ring

/-- Positive metric gauge measure has a positive-content root at a level fine
enough for both the content threshold and the gauge's local regularity radius. -/
theorem exists_admissible_positive_gauge_root (h : ℝ≥0∞ → ℝ≥0∞)
    (K : Set ParabolicPoint) (g : ParabolicGridShift)
    (hpos : 0 < (Measure.mkMetric h : Measure ParabolicPoint) K)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (δ : ℝ≥0∞) (Q : ParabolicDyadicIndex), 2 * dyadicScale Q.scale ≤ ρ ∧
      ENNReal.ofReal (2 * dyadicScale Q.scale) ≤ δ ∧
      0 < gaugePrecontent h δ (K ∩ shiftedParabolicDyadicCell g Q) := by
  obtain ⟨δ, c, hδpos, hcpos, hc⟩ := exists_positive_gaugePrecontent h K hpos
  have hcontent : 0 < gaugePrecontent h δ K :=
    (show 0 < (c : ℝ≥0∞) by exact_mod_cast hcpos).trans hc
  obtain ⟨d, hdpos, hdδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδpos
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hdpos
  let B : ℝ := min (d : ℝ) ρ
  have hB : 0 < B := lt_min hdreal hρ
  obtain ⟨n, _, hn⟩ := exists_dyadicScale_for_radius (show 0 < B / 64 by positivity)
  have hside : 2 * dyadicScale n ≤ B := by linarith only [hn]
  have hsideρ : 2 * dyadicScale n ≤ ρ := hside.trans (min_le_right _ _)
  have hsideδ : ENNReal.ofReal (2 * dyadicScale n) ≤ δ := by
    calc
      _ ≤ ENNReal.ofReal (d : ℝ) := ENNReal.ofReal_le_ofReal (hside.trans (min_le_left _ _))
      _ = (d : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
      _ ≤ δ := hdδ.le
  obtain ⟨a, ha⟩ := exists_positive_gaugePrecontent_root h δ K g n hcontent
  exact ⟨δ, ⟨n, a.1, a.2⟩, hsideρ, hsideδ, ha⟩

/-- **Gauge Frostman construction in parabolic space-time.** Positive metric
gauge measure on a compact set yields an actual finite nonzero supported measure
with small-ball growth bounded by the gauge. The assumptions are local gauge
regularity conditions, not existence of a measure or a mass allocation. -/
theorem exists_parabolic_gauge_frostman_measure (h : ℝ≥0∞ → ℝ≥0∞)
    (K : Set ParabolicPoint) (hK : IsCompact K)
    (hpos : 0 < (Measure.mkMetric h : Measure ParabolicPoint) K)
    (ρ : ℝ) (hρ : 0 < ρ) (hzero : h 0 = 0)
    (hmono : MonotoneOn h (Icc 0 (ENNReal.ofReal ρ)))
    (hfinite : h (ENNReal.ofReal ρ) ≠ ∞)
    (hdouble : ∀ r : ℝ, 0 < r → 2 * r ≤ ρ →
      h (ENNReal.ofReal (2 * r)) ≤ 2 * h (ENNReal.ofReal r)) :
    ∃ (μ : Measure ParabolicPoint) (C : ℝ≥0∞) (r₀ : ℝ),
      IsFiniteMeasure μ ∧ μ ≠ 0 ∧ μ Kᶜ = 0 ∧ μ K = 1 ∧ C ≠ ∞ ∧ 0 < r₀ ∧
        ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r < r₀ →
          μ (Metric.ball z r) ≤ C * h (ENNReal.ofReal r) := by
  classical
  let g : ParabolicGridShift := (fun _ => false, false)
  obtain ⟨δ, Q, hrootρ, hrootδ, hrootpos⟩ :=
    exists_admissible_positive_gauge_root h K g hpos ρ hρ
  obtain ⟨c, hcpos, hc⟩ := exists_positive_uniform_parabolicGaugeCapacity h K g Q δ ρ
    hzero hmono hfinite hrootρ hrootδ hrootpos
  have hKnonempty : K.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro hKempty
    rw [hKempty, measure_empty] at hpos
    exact (lt_irrefl 0) hpos
  let fallback : K := ⟨hKnonempty.choose, hKnonempty.choose_spec⟩
  let seq := parabolicGaugeProbabilityMeasure h K g Q fallback c hcpos hc
  let C : ℝ≥0∞ := (c : ℝ≥0∞)⁻¹ * 324
  let r₀ : ℝ := min (dyadicScale Q.scale / 2) (ρ / 4)
  have hr₀ : 0 < r₀ := lt_min
    (div_pos (dyadicScale_pos Q.scale) (by norm_num)) (div_pos hρ (by norm_num))
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (by exact_mod_cast hcpos.ne')) (by norm_num)
  have hbound : ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r < r₀ →
      ∀ᶠ N in atTop, (seq N : Measure K) (Subtype.val ⁻¹' Metric.ball z r) ≤
        C * h (ENNReal.ofReal r) :=
    parabolicGaugeProbabilityMeasure_eventual_ball_bound h K g Q fallback c hcpos hc ρ
      hmono hdouble
  obtain ⟨μ, hsupport, hgrowth⟩ :=
    exists_supported_probabilityMeasure_of_eventual_ball_bounds K hK seq h C r₀ hbound
  have hmass : (μ : Measure ParabolicPoint) K = 1 := by
    have hadd := measure_add_measure_compl hK.measurableSet (μ := (μ : Measure ParabolicPoint))
    simpa only [hsupport, add_zero, measure_univ] using hadd
  exact ⟨μ, C, r₀, inferInstance, IsProbabilityMeasure.ne_zero _, hsupport, hmass,
    hC, hr₀, hgrowth⟩

end FluidSingularSets
