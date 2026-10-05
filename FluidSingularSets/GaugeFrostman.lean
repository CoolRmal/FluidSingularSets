-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

/-!
# Finite capacity construction for a gauge Frostman measure

Positive gauge Hausdorff measure gives a positive fixed-scale covering cost. The
finite tree construction below identifies the least cost of a tree cut and
allocates this cost as conserved masses bounded by the capacity of each node.
These are the finite stages of the Frostman construction; passage to a measure
and geometric bounds on balls require additional compactness and grid estimates.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

section Content

variable {X : Type*} [EMetricSpace X]

/-- The covering cost at a fixed diameter threshold. -/
def gaugePrecontent (h : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞) : OuterMeasure X :=
  OuterMeasure.mkMetric'.pre (fun A => h (Metric.ediam A)) δ

/-- Every finite admissible cover bounds the fixed-scale covering cost. -/
theorem gaugePrecontent_le_finite_cover (h : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞)
    (K : Set X) (P : Finset (Set X)) (hcover : K ⊆ ⋃ A ∈ P, A)
    (hdiam : ∀ A ∈ P, Metric.ediam A ≤ δ) :
    gaugePrecontent h δ K ≤ ∑ A ∈ P, h (Metric.ediam A) := by
  classical
  calc
    gaugePrecontent h δ K ≤ gaugePrecontent h δ (⋃ A ∈ P, A) :=
      measure_mono hcover
    _ ≤ ∑ A ∈ P, gaugePrecontent h δ A := measure_biUnion_finset_le P id
    _ ≤ ∑ A ∈ P, h (Metric.ediam A) :=
      Finset.sum_le_sum fun A hA => OuterMeasure.mkMetric'.pre_le (hdiam A hA)

variable [MeasurableSpace X] [BorelSpace X]

/-- Positive gauge Hausdorff measure supplies a positive, finite lower bound at
one positive diameter threshold. No compactness or gauge regularity is needed. -/
theorem exists_positive_gaugePrecontent (h : ℝ≥0∞ → ℝ≥0∞) (K : Set X)
    (hpos : 0 < (Measure.mkMetric h : Measure X) K) :
    ∃ (δ : ℝ≥0∞) (c : ℝ≥0), 0 < δ ∧ 0 < c ∧
      (c : ℝ≥0∞) < gaugePrecontent h δ K := by
  rw [← OuterMeasure.coe_mkMetric] at hpos
  simp only [OuterMeasure.mkMetric, OuterMeasure.mkMetric', OuterMeasure.iSup_apply] at hpos
  obtain ⟨δ, hδ⟩ := lt_iSup_iff.mp hpos
  obtain ⟨hδpos, hδ⟩ := lt_iSup_iff.mp hδ
  obtain ⟨c, hcpos, hc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  exact ⟨δ, c, hδpos, by exact_mod_cast hcpos, hc⟩

end Content

/-- The capacity remaining below a node in a finite homogeneous tree. A cut can
either select the current node or cut all of its children. -/
def gaugeTreeCapacity {b : ℕ} (cap : List (Fin b) → ℝ≥0) (v : List (Fin b)) : ℕ → ℝ≥0
  | 0 => cap v
  | n + 1 => min (cap v) (∑ i : Fin b, gaugeTreeCapacity cap (v ++ [i]) n)

/-- A finite cut chooses the root or a cut in each child subtree. -/
def GaugeTreeCut (b : ℕ) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Sum PUnit (Fin b → GaugeTreeCut b n)

/-- The sum of the capacities selected by a finite cut. -/
def gaugeTreeCutCost {b : ℕ} (cap : List (Fin b) → ℝ≥0) (v : List (Fin b)) :
    {n : ℕ} → GaugeTreeCut b n → ℝ≥0
  | 0, _ => cap v
  | _ + 1, .inl _ => cap v
  | _ + 1, .inr f => ∑ i : Fin b, gaugeTreeCutCost cap (v ++ [i]) (f i)

theorem gaugeTreeCapacity_le_node {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (v : List (Fin b)) (n : ℕ) : gaugeTreeCapacity cap v n ≤ cap v := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_left _ _

theorem gaugeTreeCapacity_le_children {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (v : List (Fin b)) (n : ℕ) :
    gaugeTreeCapacity cap v (n + 1) ≤ ∑ i : Fin b, gaugeTreeCapacity cap (v ++ [i]) n :=
  min_le_right _ _

/-- Further refinement can only decrease the available capacity. -/
theorem gaugeTreeCapacity_succ_le {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (n : ℕ) (v : List (Fin b)) :
    gaugeTreeCapacity cap v (n + 1) ≤ gaugeTreeCapacity cap v n := by
  induction n generalizing v with
  | zero => exact min_le_left _ _
  | succ n ih =>
    exact min_le_min le_rfl (Finset.sum_le_sum fun i _ => ih (v ++ [i]))

/-- Every finite cut has cost at least the recursively computed capacity. -/
theorem gaugeTreeCapacity_le_cut {b : ℕ} (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (cut : GaugeTreeCut b n) :
    gaugeTreeCapacity cap v n ≤ gaugeTreeCutCost cap v cut := by
  induction n generalizing v with
  | zero => exact le_rfl
  | succ n ih =>
    cases cut with
    | inl _ => exact min_le_left _ _
    | inr f =>
      exact (min_le_right _ _).trans (Finset.sum_le_sum fun i _ => ih (v ++ [i]) (f i))

/-- The minimum cut is attained, even when some or all capacities vanish. -/
theorem exists_gaugeTreeCut_of_capacity {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (n : ℕ) (v : List (Fin b)) :
    ∃ cut : GaugeTreeCut b n, gaugeTreeCutCost cap v cut = gaugeTreeCapacity cap v n := by
  classical
  induction n generalizing v with
  | zero => exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
    by_cases h : cap v ≤ ∑ i : Fin b, gaugeTreeCapacity cap (v ++ [i]) n
    · exact ⟨Sum.inl PUnit.unit, (min_eq_left h).symm⟩
    · choose cuts hcuts using fun i : Fin b => ih (v ++ [i])
      refine ⟨Sum.inr cuts, ?_⟩
      simp only [gaugeTreeCutCost, gaugeTreeCapacity, hcuts]
      exact (min_eq_right (le_of_not_ge h)).symm

/-- Any uniform lower bound on cut costs is a lower bound on tree capacity. -/
theorem le_gaugeTreeCapacity_of_le_cut {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (n : ℕ) (v : List (Fin b)) (c : ℝ≥0)
    (hc : ∀ cut : GaugeTreeCut b n, c ≤ gaugeTreeCutCost cap v cut) :
    c ≤ gaugeTreeCapacity cap v n := by
  obtain ⟨cut, hcut⟩ := exists_gaugeTreeCut_of_capacity cap n v
  simpa only [hcut] using hc cut

/-- If tree cuts give admissible covers at one fixed scale, their capacities
dominate the gauge precontent of the covered set. -/
theorem gaugePrecontent_le_gaugeTreeCapacity {X : Type*} [EMetricSpace X]
    {b : ℕ} (cap : List (Fin b) → ℝ≥0) (n : ℕ) (v : List (Fin b))
    (h : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞) (K : Set X)
    (cover : GaugeTreeCut b n → Finset (Set X))
    (hcover : ∀ cut, K ⊆ ⋃ A ∈ cover cut, A)
    (hdiam : ∀ cut A, A ∈ cover cut → Metric.ediam A ≤ δ)
    (hcost : ∀ cut, ∑ A ∈ cover cut, h (Metric.ediam A) ≤
      (gaugeTreeCutCost cap v cut : ℝ≥0∞)) :
    gaugePrecontent h δ K ≤ (gaugeTreeCapacity cap v n : ℝ≥0∞) := by
  obtain ⟨cut, hcut⟩ := exists_gaugeTreeCut_of_capacity cap n v
  exact (gaugePrecontent_le_finite_cover h δ K (cover cut) (hcover cut)
    (hdiam cut)).trans (hcut ▸ hcost cut)

/-- The sets selected by a cut, expressed as a recursive finite union. -/
def gaugeTreeCutCover {X : Type*} {b : ℕ} (region : List (Fin b) → Set X)
    (v : List (Fin b)) : {n : ℕ} → GaugeTreeCut b n → Set X
  | 0, _ => region v
  | _ + 1, .inl _ => region v
  | _ + 1, .inr f => ⋃ i : Fin b, gaugeTreeCutCover region (v ++ [i]) (f i)

/-- A refining family of regions is covered by every finite tree cut. -/
theorem subset_gaugeTreeCutCover {X : Type*} {b : ℕ}
    (region : List (Fin b) → Set X)
    (hrefine : ∀ v, region v ⊆ ⋃ i : Fin b, region (v ++ [i]))
    (n : ℕ) (v : List (Fin b)) (cut : GaugeTreeCut b n) :
    region v ⊆ gaugeTreeCutCover region v cut := by
  induction n generalizing v with
  | zero => exact Subset.rfl
  | succ n ih =>
    cases cut with
    | inl _ => exact Subset.rfl
    | inr f =>
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hrefine v hx)
      exact mem_iUnion.mpr ⟨i, ih (v ++ [i]) (f i) hi⟩

/-- The covering cost of a cut is bounded by its sum of node capacities. -/
theorem gaugePrecontent_cutCover_le_cost {X : Type*} [EMetricSpace X] {b : ℕ}
    (region : List (Fin b) → Set X) (cap : List (Fin b) → ℝ≥0)
    (h : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hdiam : ∀ v, Metric.ediam (region v) ≤ δ)
    (hcap : ∀ v, h (Metric.ediam (region v)) ≤ (cap v : ℝ≥0∞))
    (n : ℕ) (v : List (Fin b)) (cut : GaugeTreeCut b n) :
    gaugePrecontent h δ (gaugeTreeCutCover region v cut) ≤
      (gaugeTreeCutCost cap v cut : ℝ≥0∞) := by
  induction n generalizing v with
  | zero => exact (OuterMeasure.mkMetric'.pre_le (hdiam v)).trans (hcap v)
  | succ n ih =>
    cases cut with
    | inl _ => exact (OuterMeasure.mkMetric'.pre_le (hdiam v)).trans (hcap v)
    | inr f =>
      calc
        gaugePrecontent h δ (⋃ i : Fin b, gaugeTreeCutCover region (v ++ [i]) (f i)) ≤
            ∑ i : Fin b, gaugePrecontent h δ (gaugeTreeCutCover region (v ++ [i]) (f i)) :=
          measure_iUnion_fintype_le _ _
        _ ≤ ∑ i : Fin b, (gaugeTreeCutCost cap (v ++ [i]) (f i) : ℝ≥0∞) :=
          Finset.sum_le_sum fun i _ => ih (v ++ [i]) (f i)
        _ = (gaugeTreeCutCost cap v (n := n + 1) (Sum.inr f) : ℝ≥0∞) :=
          (ENNReal.ofNNReal_finsetSum _ _).symm

/-- A refining geometric tree with admissible node capacities has root capacity
at least the fixed-scale gauge content, uniformly in the final depth. -/
theorem gaugePrecontent_le_capacity_of_refinement {X : Type*} [EMetricSpace X] {b : ℕ}
    (region : List (Fin b) → Set X) (cap : List (Fin b) → ℝ≥0)
    (h : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hrefine : ∀ v, region v ⊆ ⋃ i : Fin b, region (v ++ [i]))
    (hdiam : ∀ v, Metric.ediam (region v) ≤ δ)
    (hcap : ∀ v, h (Metric.ediam (region v)) ≤ (cap v : ℝ≥0∞))
    (n : ℕ) (v : List (Fin b)) :
    gaugePrecontent h δ (region v) ≤ (gaugeTreeCapacity cap v n : ℝ≥0∞) := by
  obtain ⟨cut, hcut⟩ := exists_gaugeTreeCut_of_capacity cap n v
  calc
    gaugePrecontent h δ (region v) ≤ gaugePrecontent h δ (gaugeTreeCutCover region v cut) :=
      measure_mono (subset_gaugeTreeCutCover region hrefine n v cut)
    _ ≤ (gaugeTreeCutCost cap v cut : ℝ≥0∞) :=
      gaugePrecontent_cutCover_le_cost region cap h δ hdiam hcap n v cut
    _ = (gaugeTreeCapacity cap v n : ℝ≥0∞) := by rw [hcut]

/-- Positive content gives one positive root mass that is feasible at every
finite depth of the geometric tree. -/
theorem exists_positive_uniform_gaugeTreeCapacity {X : Type*} [EMetricSpace X] {b : ℕ}
    (region : List (Fin b) → Set X) (cap : List (Fin b) → ℝ≥0)
    (h : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hrefine : ∀ v, region v ⊆ ⋃ i : Fin b, region (v ++ [i]))
    (hdiam : ∀ v, Metric.ediam (region v) ≤ δ)
    (hcap : ∀ v, h (Metric.ediam (region v)) ≤ (cap v : ℝ≥0∞))
    (v : List (Fin b)) (hpos : 0 < gaugePrecontent h δ (region v)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ n, c ≤ gaugeTreeCapacity cap v n := by
  obtain ⟨c, hcpos, hc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  refine ⟨c, by exact_mod_cast hcpos, fun n => ?_⟩
  exact_mod_cast (hc.trans_le
    (gaugePrecontent_le_capacity_of_refinement region cap h δ hrefine hdiam hcap n v)).le

/-- Divide a node mass in proportion to the capacities of its children. -/
def proportionalTreeMass {b : ℕ} (m : ℝ≥0) (w : Fin b → ℝ≥0) (i : Fin b) : ℝ≥0 :=
  m * w i / ∑ j, w j

theorem proportionalTreeMass_le {b : ℕ} (m : ℝ≥0) (w : Fin b → ℝ≥0)
    (hm : m ≤ ∑ j, w j) (i : Fin b) : proportionalTreeMass m w i ≤ w i := by
  by_cases hw : (∑ j, w j) = 0
  · have hm0 : m = 0 := le_antisymm (hw ▸ hm) (zero_le : 0 ≤ m)
    simp [proportionalTreeMass, hm0]
  · rw [proportionalTreeMass, div_le_iff₀ (pos_iff_ne_zero.mpr hw)]
    exact (mul_le_mul_of_nonneg_right hm (zero_le : 0 ≤ w i)).trans_eq (mul_comm _ _)

theorem sum_proportionalTreeMass {b : ℕ} (m : ℝ≥0) (w : Fin b → ℝ≥0)
    (hm : m ≤ ∑ j, w j) : ∑ i, proportionalTreeMass m w i = m := by
  by_cases hw : (∑ j, w j) = 0
  · have hm0 : m = 0 := le_antisymm (hw ▸ hm) (zero_le : 0 ≤ m)
    simp [proportionalTreeMass, hm0]
  · simp only [proportionalTreeMass, ← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ m hw

/-- The mass at a node reached by a word, obtained by the actual recursive
proportional allocation. Words below the final depth carry mass zero. -/
def gaugeTreeNodeMass {b : ℕ} (cap : List (Fin b) → ℝ≥0) (v : List (Fin b)) :
    ℕ → ℝ≥0 → List (Fin b) → ℝ≥0
  | _, m, [] => m
  | 0, _, _ :: _ => 0
  | n + 1, m, i :: p => gaugeTreeNodeMass cap (v ++ [i]) n
      (proportionalTreeMass m (fun j => gaugeTreeCapacity cap (v ++ [j]) n) i) p

/-- Every allocated node mass is bounded by its prescribed capacity. -/
theorem gaugeTreeNodeMass_le_node {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (n : ℕ) (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (p : List (Fin b)) (hp : p.length ≤ n) :
    gaugeTreeNodeMass cap v n m p ≤ cap (v ++ p) := by
  induction n generalizing v m p with
  | zero =>
    have hp0 : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
    subst p
    simpa only [gaugeTreeNodeMass, gaugeTreeCapacity, List.append_nil] using hm
  | succ n ih =>
    cases p with
    | nil =>
      simpa only [gaugeTreeNodeMass, List.append_nil] using
        hm.trans (gaugeTreeCapacity_le_node cap v (n + 1))
    | cons i p =>
      have hmchildren := hm.trans (gaugeTreeCapacity_le_children cap v n)
      have hmi := proportionalTreeMass_le m
        (fun j => gaugeTreeCapacity cap (v ++ [j]) n) hmchildren i
      have hplen : p.length ≤ n := by simpa using hp
      simpa only [gaugeTreeNodeMass, List.append_assoc, List.singleton_append] using
        ih (v ++ [i]) _ hmi p hplen

/-- At every nonterminal node the sum of its children is exactly its mass. -/
theorem sum_gaugeTreeNodeMass_children {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (n : ℕ) (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (p : List (Fin b)) (hp : p.length < n) :
    ∑ i : Fin b, gaugeTreeNodeMass cap v n m (p ++ [i]) =
      gaugeTreeNodeMass cap v n m p := by
  induction n generalizing v m p with
  | zero => exact (Nat.not_lt_zero _ hp).elim
  | succ n ih =>
    have hmchildren := hm.trans (gaugeTreeCapacity_le_children cap v n)
    cases p with
    | nil =>
      simpa only [List.nil_append, gaugeTreeNodeMass] using
        sum_proportionalTreeMass m (fun j => gaugeTreeCapacity cap (v ++ [j]) n)
          hmchildren
    | cons i p =>
      have hmi := proportionalTreeMass_le m
        (fun j => gaugeTreeCapacity cap (v ++ [j]) n) hmchildren i
      have hplen : p.length < n := by simpa using hp
      simpa only [List.cons_append, gaugeTreeNodeMass] using
        ih (v ++ [i]) _ hmi p hplen

/-- The total mass on terminal nodes is the root mass. -/
theorem sum_gaugeTreeNodeMass_leaves {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (n : ℕ) (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n) :
    ∑ p : Fin n → Fin b, gaugeTreeNodeMass cap v n m (List.ofFn p) = m := by
  induction n generalizing v m with
  | zero => simp [List.ofFn_zero, gaugeTreeNodeMass]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin b)).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ i : Fin b, ∑ p : Fin n → Fin b,
      gaugeTreeNodeMass cap v (n + 1) m (List.ofFn (Fin.cons i p))) = m
    simp only [List.ofFn_cons, gaugeTreeNodeMass]
    have hmchildren := hm.trans (gaugeTreeCapacity_le_children cap v n)
    calc
      _ = ∑ i : Fin b,
          proportionalTreeMass m (fun j => gaugeTreeCapacity cap (v ++ [j]) n) i := by
        apply Finset.sum_congr rfl
        intro i _
        exact ih (v ++ [i]) _
          (proportionalTreeMass_le m _ hmchildren i)
      _ = m := sum_proportionalTreeMass m _ hmchildren

/-- The sum of the masses of all terminal descendants of a fixed prefix is
exactly the mass allocated to that prefix. -/
theorem sum_gaugeTreeNodeMass_descendants {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (p : List (Fin b)) (t : ℕ) (v : List (Fin b)) (m : ℝ≥0)
    (hm : m ≤ gaugeTreeCapacity cap v (p.length + t)) :
    ∑ q : Fin t → Fin b,
      gaugeTreeNodeMass cap v (p.length + t) m (p ++ List.ofFn q) =
      gaugeTreeNodeMass cap v (p.length + t) m p := by
  induction p generalizing v m with
  | nil =>
    simp only [List.length_nil, zero_add] at hm ⊢
    simpa only [List.nil_append, gaugeTreeNodeMass] using
      sum_gaugeTreeNodeMass_leaves cap t v m hm
  | cons i p ih =>
    simp only [List.length_cons, Nat.succ_add] at hm
    have hmchildren : m ≤ ∑ j : Fin b, gaugeTreeCapacity cap (v ++ [j]) (p.length + t) :=
      hm.trans (gaugeTreeCapacity_le_children cap v (p.length + t))
    simpa only [List.length_cons, Nat.succ_add, List.cons_append, gaugeTreeNodeMass] using
      ih (v ++ [i]) _ (proportionalTreeMass_le m _ hmchildren i)

theorem sum_gaugeTreeNodeMass_descendants_le_node {b : ℕ}
    (cap : List (Fin b) → ℝ≥0) (p : List (Fin b)) (t : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v (p.length + t)) :
    ∑ q : Fin t → Fin b,
      gaugeTreeNodeMass cap v (p.length + t) m (p ++ List.ofFn q) ≤ cap (v ++ p) := by
  rw [sum_gaugeTreeNodeMass_descendants cap p t v m hm]
  exact gaugeTreeNodeMass_le_node cap (p.length + t) v m hm p (Nat.le_add_right _ _)

/-- Choose a point in a nonempty node region, using a fixed fallback in empty
regions. Empty regions carry zero mass in the application. -/
def gaugeTreeSelectedPoint {X : Type*} {b : ℕ} (region : List (Fin b) → Set X)
    (fallback : X) (v : List (Fin b)) : X := by
  classical
  exact if hv : (region v).Nonempty then hv.choose else fallback

theorem gaugeTreeSelectedPoint_mem {X : Type*} {b : ℕ}
    (region : List (Fin b) → Set X) (fallback : X) (v : List (Fin b))
    (hv : (region v).Nonempty) :
    gaugeTreeSelectedPoint region fallback v ∈ region v := by
  rw [gaugeTreeSelectedPoint, dite_eq_left hv]
  exact hv.choose_spec

/-- Selected points stay in the target set even at empty leaves. -/
theorem gaugeTreeSelectedPoint_mem_set {X : Type*} {b : ℕ}
    (region : List (Fin b) → Set X) (K : Set X) (fallback : X) (hfallback : fallback ∈ K)
    (hregion : ∀ v, region v ⊆ K) (v : List (Fin b)) :
    gaugeTreeSelectedPoint region fallback v ∈ K := by
  by_cases hv : (region v).Nonempty
  · exact hregion v (gaugeTreeSelectedPoint_mem region fallback v hv)
  · simpa only [gaugeTreeSelectedPoint, dite_eq_right hv] using hfallback

/-- Every selected point carrying positive mass belongs to its own node region.
This follows from zero capacity on empty regions, rather than a point-selection
assumption for leaves that may be empty. -/
theorem gaugeTreeSelectedPoint_mem_of_mass_ne_zero {X : Type*} {b : ℕ}
    (region : List (Fin b) → Set X) (cap : List (Fin b) → ℝ≥0) (fallback : X)
    (hempty : ∀ v, region v = ∅ → cap v = 0)
    (n : ℕ) (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (p : List (Fin b)) (hp : p.length ≤ n)
    (hpos : gaugeTreeNodeMass cap v n m p ≠ 0) :
    gaugeTreeSelectedPoint region fallback (v ++ p) ∈ region (v ++ p) := by
  apply gaugeTreeSelectedPoint_mem
  apply nonempty_iff_ne_empty.mpr
  intro hregion
  have hbound := gaugeTreeNodeMass_le_node cap n v m hm p hp
  rw [hempty _ hregion] at hbound
  exact hpos (le_antisymm hbound zero_le)

section AtomicMeasure

variable {X : Type*} [MeasurableSpace X] {b : ℕ}

/-- Put the allocated leaf masses at chosen points. The points can be selected
inside the compact set in the geometric application. -/
def gaugeTreeAtomicMeasure (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (points : (Fin n → Fin b) → X) : Measure X :=
  ∑ p : Fin n → Fin b,
    (gaugeTreeNodeMass cap v n m (List.ofFn p) : ℝ≥0∞) • Measure.dirac (points p)

theorem gaugeTreeAtomicMeasure_univ (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (points : (Fin n → Fin b) → X) :
    gaugeTreeAtomicMeasure cap n v m points univ = (m : ℝ≥0∞) := by
  simp only [gaugeTreeAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofNNReal_finsetSum, sum_gaugeTreeNodeMass_leaves cap n v m hm]

/-- Each finite-stage atomic measure is finite. -/
theorem isFiniteMeasure_gaugeTreeAtomicMeasure (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (points : (Fin n → Fin b) → X) :
    IsFiniteMeasure (gaugeTreeAtomicMeasure cap n v m points) := by
  constructor
  rw [gaugeTreeAtomicMeasure_univ cap n v m hm points]
  exact ENNReal.coe_lt_top

/-- Positive root mass produces a nonzero atomic measure. -/
theorem gaugeTreeAtomicMeasure_ne_zero (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (hmpos : 0 < m) (points : (Fin n → Fin b) → X) :
    gaugeTreeAtomicMeasure cap n v m points ≠ 0 := by
  intro hzero
  have hmzero : (m : ℝ≥0∞) = 0 := by
    simpa only [hzero, Measure.coe_zero, Pi.zero_apply] using
      (gaugeTreeAtomicMeasure_univ cap n v m hm points).symm
  exact hmpos.ne' (ENNReal.coe_eq_zero.mp hmzero)

/-- The measure is supported on any measurable set containing all selected points. -/
theorem gaugeTreeAtomicMeasure_compl (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (points : (Fin n → Fin b) → X)
    (K : Set X) (hK : MeasurableSet K) (hpoints : ∀ p, points p ∈ K) :
    gaugeTreeAtomicMeasure cap n v m points Kᶜ = 0 := by
  rw [gaugeTreeAtomicMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro p _
  rw [Measure.smul_apply, Measure.dirac_apply' _ hK.compl,
    indicator_of_notMem (by simpa only [mem_compl_iff, not_not] using hpoints p), smul_zero]

/-- Normalization of the actual leaf measure gives a probability measure. -/
def gaugeTreeProbabilityMeasure (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (hmpos : 0 < m) (points : (Fin n → Fin b) → X) : ProbabilityMeasure X :=
  ⟨(m : ℝ≥0∞)⁻¹ • gaugeTreeAtomicMeasure cap n v m points, ⟨by
    rw [Measure.smul_apply, smul_eq_mul, gaugeTreeAtomicMeasure_univ cap n v m hm points]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hmpos.ne') ENNReal.coe_ne_top⟩⟩

theorem gaugeTreeProbabilityMeasure_compl (cap : List (Fin b) → ℝ≥0) (n : ℕ)
    (v : List (Fin b)) (m : ℝ≥0) (hm : m ≤ gaugeTreeCapacity cap v n)
    (hmpos : 0 < m) (points : (Fin n → Fin b) → X)
    (K : Set X) (hK : MeasurableSet K) (hpoints : ∀ p, points p ∈ K) :
    (gaugeTreeProbabilityMeasure cap n v m hm hmpos points : Measure X) Kᶜ = 0 := by
  change ((m : ℝ≥0∞)⁻¹ • gaugeTreeAtomicMeasure cap n v m points) Kᶜ = 0
  rw [Measure.smul_apply, gaugeTreeAtomicMeasure_compl cap n v m points K hK hpoints,
    smul_zero]

end AtomicMeasure

end FluidSingularSets
