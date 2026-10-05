-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.ParabolicRefinement
public import FluidSingularSets.GaugeFrostman

/-!
# The actual parabolic tree for the gauge capacity construction

Nodes are actual cells in a fixed shifted grid. Their thirty-two children refine
them exactly. The diameter estimate uses the Euclidean spatial norm and the
square-root time distance of the parabolic metric.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Two points in one scalar grid interval differ by at most its side length. -/
theorem abs_sub_le_of_mem_shiftedGridInterval {ℓ σ x y : ℝ} {a : ℤ}
    (hx : x ∈ shiftedGridInterval ℓ σ a) (hy : y ∈ shiftedGridInterval ℓ σ a) :
    |x - y| ≤ ℓ := by
  apply abs_le.mpr
  constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]

/-- The parabolic diameter of a spatial-side-`ℓ` cell is at most `2 * ℓ`. -/
theorem ediam_shiftedParabolicDyadicCell_le (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) :
    Metric.ediam (shiftedParabolicDyadicCell g Q) ≤
      ENNReal.ofReal (2 * dyadicScale Q.scale) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hside := dyadicScale_pos Q.scale
  have hnorm : ‖x.1 - y.1‖ ≤ dyadicScale Q.scale := by
    apply (pi_norm_le_iff_of_nonneg hside.le).mpr
    intro i
    change |x.1 i - y.1 i| ≤ dyadicScale Q.scale
    exact abs_sub_le_of_mem_shiftedGridInterval
      (mem_pi.mp hx.1 i (mem_univ i)) (mem_pi.mp hy.1 i (mem_univ i))
  have hsqrt3 : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hspace : vec3EuclideanNorm (x.1 - y.1) ≤ 2 * dyadicScale Q.scale :=
    (vec3EuclideanNorm_le_sqrt_three_mul_norm _).trans
      ((mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg 3)).trans
        (mul_le_mul_of_nonneg_right hsqrt3 hside.le))
  have htime := abs_sub_le_of_mem_shiftedGridInterval hx.2 hy.2
  rw [dyadicScale_two_mul] at htime
  have htimeRoot : Real.sqrt |x.2 - y.2| ≤ dyadicScale Q.scale :=
    Real.sqrt_le_iff.mpr ⟨hside.le, htime⟩
  rw [dist_eq_parabolicDist, parabolicDist, max_le_iff]
  exact ⟨hspace, htimeRoot.trans (by linarith only [hside])⟩

theorem shiftedParabolicDyadicCell_nonempty (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) : (shiftedParabolicDyadicCell g Q).Nonempty := by
  obtain ⟨x, hx⟩ := shiftedDyadicCube_nonempty g Q.scale Q.corner
  refine ⟨(x, ((Q.timeCorner : ℝ) + shiftedTimePhase g) * dyadicScale (2 * Q.scale)),
    hx, le_rfl, ?_⟩
  have hpos := dyadicScale_pos (2 * Q.scale)
  nlinarith only [hpos]

/-- The finite digits of the capacity construction enumerate the actual children. -/
def parabolicChildEquiv : Fin 32 ≃ ParabolicChildDigit :=
  (Fintype.equivFinOfCardEq card_parabolicChildDigit).symm

/-- Follow a finite word of actual children in one fixed shifted grid. -/
def parabolicTreeIndex (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    List (Fin 32) → ParabolicDyadicIndex
  | [] => Q
  | i :: p => parabolicTreeIndex g (shiftedParabolicChild g Q (parabolicChildEquiv i)) p

theorem parabolicTreeIndex_append (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (p q : List (Fin 32)) :
    parabolicTreeIndex g Q (p ++ q) = parabolicTreeIndex g (parabolicTreeIndex g Q p) q := by
  induction p generalizing Q with
  | nil => rfl
  | cons i p ih =>
    exact ih (shiftedParabolicChild g Q (parabolicChildEquiv i))

theorem parabolicTreeIndex_scale (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (p : List (Fin 32)) : (parabolicTreeIndex g Q p).scale = Q.scale + p.length := by
  induction p generalizing Q with
  | nil => simp [parabolicTreeIndex]
  | cons i p ih =>
    rw [parabolicTreeIndex, ih]
    dsimp [shiftedParabolicChild]
    omega

/-- Every tree cell is contained in its root. -/
theorem parabolicTreeCell_subset_root (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (p : List (Fin 32)) :
    shiftedParabolicDyadicCell g (parabolicTreeIndex g Q p) ⊆
      shiftedParabolicDyadicCell g Q := by
  induction p generalizing Q with
  | nil => exact Subset.rfl
  | cons i p ih =>
    exact (ih (shiftedParabolicChild g Q (parabolicChildEquiv i))).trans
      (shiftedParabolicChild_subset g Q (parabolicChildEquiv i))

theorem parabolicTreeCell_child_subset (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (p : List (Fin 32)) (i : Fin 32) :
    shiftedParabolicDyadicCell g (parabolicTreeIndex g Q (p ++ [i])) ⊆
      shiftedParabolicDyadicCell g (parabolicTreeIndex g Q p) := by
  rw [parabolicTreeIndex_append]
  exact shiftedParabolicChild_subset g (parabolicTreeIndex g Q p) (parabolicChildEquiv i)

/-- Each node is exactly the union of its thirty-two successor regions. -/
theorem parabolicTreeCell_eq_iUnion_children (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (p : List (Fin 32)) :
    shiftedParabolicDyadicCell g (parabolicTreeIndex g Q p) =
      ⋃ i : Fin 32, shiftedParabolicDyadicCell g (parabolicTreeIndex g Q (p ++ [i])) := by
  rw [shiftedParabolicDyadicCell_eq_iUnion_children]
  rw [← parabolicChildEquiv.surjective.iUnion_comp
    (fun d => shiftedParabolicDyadicCell g
      (shiftedParabolicChild g (parabolicTreeIndex g Q p) d))]
  congr 1
  funext i
  rw [parabolicTreeIndex_append]
  rfl

/-- The occupied region used in the finite capacity construction. -/
def parabolicTreeRegion (K : Set ParabolicPoint) (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (p : List (Fin 32)) : Set ParabolicPoint :=
  K ∩ shiftedParabolicDyadicCell g (parabolicTreeIndex g Q p)

theorem parabolicTreeRegion_refines (K : Set ParabolicPoint) (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (p : List (Fin 32)) :
    parabolicTreeRegion K g Q p ⊆ ⋃ i : Fin 32, parabolicTreeRegion K g Q (p ++ [i]) := by
  intro x hx
  have hcell := hx.2
  rw [parabolicTreeCell_eq_iUnion_children] at hcell
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcell
  exact mem_iUnion.mpr ⟨i, hx.1, hi⟩

theorem parabolicTreeRegion_child_subset (K : Set ParabolicPoint) (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (p : List (Fin 32)) (i : Fin 32) :
    parabolicTreeRegion K g Q (p ++ [i]) ⊆ parabolicTreeRegion K g Q p :=
  inter_subset_inter_right K (parabolicTreeCell_child_subset g Q p i)

theorem ediam_parabolicTreeRegion_le_root (K : Set ParabolicPoint) (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (p : List (Fin 32)) :
    Metric.ediam (parabolicTreeRegion K g Q p) ≤ ENNReal.ofReal (2 * dyadicScale Q.scale) :=
  (Metric.ediam_mono (inter_subset_right.trans (parabolicTreeCell_subset_root g Q p))).trans
    (ediam_shiftedParabolicDyadicCell_le g Q)

/-- Distinct equal-length words give distinct cells. This is proved from actual
child disjointness, including all half-open boundary cases. -/
theorem parabolicTreeIndex_injective_at_length (g : ParabolicGridShift) (n : ℕ)
    (Q : ParabolicDyadicIndex) (p q : List (Fin 32)) (hp : p.length = n) (hq : q.length = n)
    (heq : parabolicTreeIndex g Q p = parabolicTreeIndex g Q q) : p = q := by
  induction n generalizing Q p q with
  | zero =>
    have hp0 := List.length_eq_zero_iff.mp hp
    have hq0 := List.length_eq_zero_iff.mp hq
    exact hp0.trans hq0.symm
  | succ n ih =>
    cases p with
    | nil => simp only [List.length_nil] at hp; omega
    | cons i p =>
      cases q with
      | nil => simp only [List.length_nil] at hq; omega
      | cons j q =>
        have hp' : p.length = n := by simpa only [List.length_cons, Nat.succ.injEq] using hp
        have hq' : q.length = n := by simpa only [List.length_cons, Nat.succ.injEq] using hq
        obtain ⟨z, hz⟩ := shiftedParabolicDyadicCell_nonempty g (parabolicTreeIndex g Q (i :: p))
        have hzj : z ∈ shiftedParabolicDyadicCell g (parabolicTreeIndex g Q (j :: q)) :=
          heq ▸ hz
        have hzi := parabolicTreeCell_subset_root g
          (shiftedParabolicChild g Q (parabolicChildEquiv i)) p hz
        have hzj' := parabolicTreeCell_subset_root g
          (shiftedParabolicChild g Q (parabolicChildEquiv j)) q hzj
        have hchild := shiftedParabolicDyadicIndex_unique_at_scale g
          (Q := shiftedParabolicChild g Q (parabolicChildEquiv i))
          (R := shiftedParabolicChild g Q (parabolicChildEquiv j)) rfl hzi hzj'
        have hij : i = j := parabolicChildEquiv.injective
          (shiftedParabolicChild_injective g Q hchild)
        subst j
        exact congrArg (List.cons i)
          (ih (shiftedParabolicChild g Q (parabolicChildEquiv i)) p q hp' hq' heq)

theorem parabolicTreeIndex_ofFn_injective (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (n : ℕ) : Function.Injective (fun p : Fin n → Fin 32 =>
      parabolicTreeIndex g Q (List.ofFn p)) := by
  intro p q hpq
  apply List.ofFn_injective
  exact parabolicTreeIndex_injective_at_length g n Q _ _ List.length_ofFn List.length_ofFn hpq

/-- The finite set of tree nodes at a fixed depth whose cells meet a ball. -/
def parabolicTreeBallCells (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (n : ℕ) (z : ParabolicPoint) (r : ℝ) : Finset (Fin n → Fin 32) := by
  classical
  exact Finset.univ.filter fun p =>
    (shiftedParabolicDyadicCell g (parabolicTreeIndex g Q (List.ofFn p)) ∩
      Metric.closedBall z r).Nonempty

/-- At any depth, only eighty-one tree cells can meet a ball whose radius is at
most the side length of the cells at that depth. -/
theorem card_parabolicTreeCells_intersect_ball_le (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (n : ℕ) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 ≤ r) (hside : r ≤ dyadicScale (Q.scale + n)) :
    (parabolicTreeBallCells g Q n z r).card ≤ 81 := by
  classical
  let P := Finset.univ.filter fun p : Fin n → Fin 32 =>
    (shiftedParabolicDyadicCell g (parabolicTreeIndex g Q (List.ofFn p)) ∩
      Metric.closedBall z r).Nonempty
  change P.card ≤ 81
  calc
    P.card = (P.image (fun p => parabolicTreeIndex g Q (List.ofFn p))).card :=
      (Finset.card_image_of_injective _ (parabolicTreeIndex_ofFn_injective g Q n)).symm
    _ ≤ (nearbyParabolicCells g (Q.scale + n) z).card := by
      apply Finset.card_le_card
      intro R hR
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hR
      have hp' := (Finset.mem_filter.mp hp).2
      exact mem_nearbyParabolicCells_of_intersect_ball g (Q.scale + n) z hr hside _
        (by rw [parabolicTreeIndex_scale, List.length_ofFn]) hp'
    _ = 81 := card_nearbyParabolicCells g (Q.scale + n) z

end FluidSingularSets
