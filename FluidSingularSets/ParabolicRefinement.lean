-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.ShiftedParabolicDyadic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Finite refinement of the shifted parabolic grids

The coherent spatial grids split into eight spatial children, while their time
intervals split into four children. Their products therefore have thirty-two
children. All selectors use half-open intervals, including at grid boundaries.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The temporal corner selected at a prescribed level of a shifted grid. -/
def shiftedTimeCellSelector (g : ParabolicGridShift) (n : ℤ) (t : ℝ) : ℤ :=
  ⌊t / dyadicScale (2 * n) - shiftedTimePhase g⌋

/-- The unique temporal cell selector is measurable. -/
theorem measurable_shiftedTimeCellSelector (g : ParabolicGridShift) (n : ℤ) :
    Measurable (shiftedTimeCellSelector g n) :=
  Int.measurable_floor.comp ((measurable_id.div_const _).sub_const _)

theorem shiftedTimeCellSelector_unique (g : ParabolicGridShift) (n : ℤ) (t : ℝ) :
    ∃! a : ℤ, t ∈ shiftedParabolicDyadicTime g n a := by
  refine ⟨shiftedTimeCellSelector g n t,
    mem_shiftedGridInterval_of_floor (dyadicScale_pos (2 * n)) _ _, ?_⟩
  intro a ha
  exact shiftedGridInterval_corner_unique (dyadicScale_pos (2 * n)) ha
    (mem_shiftedGridInterval_of_floor (dyadicScale_pos (2 * n)) _ _)

/-- Interval membership after dividing by its positive length. -/
theorem mem_shiftedGridInterval_iff_div {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : ℝ)
    (a : ℤ) (x : ℝ) :
    x ∈ shiftedGridInterval ℓ σ a ↔ (a : ℝ) + σ ≤ x / ℓ ∧
      x / ℓ < (a : ℝ) + σ + 1 := by
  exact ⟨fun hx => ⟨(le_div_iff₀ hℓ).mpr hx.1, (div_lt_iff₀ hℓ).mpr hx.2⟩,
    fun hx => ⟨(le_div_iff₀ hℓ).mp hx.1, (div_lt_iff₀ hℓ).mp hx.2⟩⟩

/-- A parent interval, normalized using the finer length and integral phase
discrepancy, is an interval of exactly `b` consecutive integer cells. -/
theorem mem_shiftedGridInterval_parent_iff {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : ℕ) (σ τ : ℝ) (c a : ℤ) (hphase : (b : ℝ) * σ - τ = c) (x : ℝ) :
    x ∈ shiftedGridInterval ((b : ℝ) * ℓ) σ a ↔
      ((b : ℤ) * a + c : ℤ) ≤ x / ℓ - τ ∧
        x / ℓ - τ < (((b : ℤ) * a + c + b : ℤ) : ℝ) := by
  have hlo : ((a : ℝ) + σ) * ((b : ℝ) * ℓ) =
      ((((b : ℤ) * a + c : ℤ) : ℝ) + τ) * ℓ := by
    push_cast
    rw [← hphase]
    ring
  have hhi : ((a : ℝ) + σ + 1) * ((b : ℝ) * ℓ) =
      ((((b : ℤ) * a + c + b : ℤ) : ℝ) + τ) * ℓ := by
    push_cast
    rw [← hphase]
    ring
  change (_ ≤ x ∧ x < _) ↔ _
  rw [hlo, hhi, ← le_div_iff₀ hℓ, ← div_lt_iff₀ hℓ]
  constructor <;> intro hx <;> constructor <;> linarith only [hx.1, hx.2]

/-- Each of the consecutive fine cells lies inside its coherent parent. -/
theorem shiftedGridInterval_child_subset {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : ℕ) (σ τ : ℝ) (c a : ℤ) (hphase : (b : ℝ) * σ - τ = c) (d : Fin b) :
    shiftedGridInterval ℓ τ ((b : ℤ) * a + c + (d : ℕ)) ⊆
      shiftedGridInterval ((b : ℝ) * ℓ) σ a := by
  intro x hx
  rw [mem_shiftedGridInterval_iff_div hℓ] at hx
  rw [mem_shiftedGridInterval_parent_iff hℓ b σ τ c a hphase]
  have hdlo : (0 : ℝ) ≤ (d : ℕ) := by positivity
  have hdhi : (d : ℕ) + (1 : ℝ) ≤ b := by exact_mod_cast d.isLt
  push_cast at hx ⊢
  constructor <;> linarith only [hx.1, hx.2, hdlo, hdhi]

/-- The coherent parent is exactly the union of its `b` fine children. -/
theorem shiftedGridInterval_eq_iUnion_children {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : ℕ) (σ τ : ℝ) (c a : ℤ) (hphase : (b : ℝ) * σ - τ = c) :
    shiftedGridInterval ((b : ℝ) * ℓ) σ a =
      ⋃ d : Fin b, shiftedGridInterval ℓ τ ((b : ℤ) * a + c + (d : ℕ)) := by
  apply Subset.antisymm
  · intro x hx
    have hnorm := (mem_shiftedGridInterval_parent_iff hℓ b σ τ c a hphase x).mp hx
    let j : ℤ := ⌊x / ℓ - τ⌋
    have hjlo : (b : ℤ) * a + c ≤ j := Int.le_floor.mpr hnorm.1
    have hjhi : j < (b : ℤ) * a + c + b := Int.floor_lt.mpr hnorm.2
    let d : Fin b := ⟨(j - ((b : ℤ) * a + c)).toNat, by omega⟩
    have hcorner : (b : ℤ) * a + c + (d : ℕ) = j := by
      dsimp [d]
      omega
    exact mem_iUnion.mpr ⟨d, hcorner ▸ mem_shiftedGridInterval_of_floor hℓ τ x⟩
  · intro x hx
    obtain ⟨d, hd⟩ := mem_iUnion.mp hx
    exact shiftedGridInterval_child_subset hℓ b σ τ c a hphase d hd

/-- Integral phase correction for the eight spatial child cubes. -/
def shiftedSpatialChildOffset (g : ParabolicGridShift) (n : ℤ) (i : Fin 3) : ℤ :=
  (shiftedSpatialPhase_coherent g n i).choose

theorem shiftedSpatialChildOffset_spec (g : ParabolicGridShift) (n : ℤ) (i : Fin 3) :
    2 * shiftedSpatialPhase g n i - shiftedSpatialPhase g (n + 1) i =
      shiftedSpatialChildOffset g n i :=
  (shiftedSpatialPhase_coherent g n i).choose_spec

/-- Integral phase correction for the four temporal children. -/
def shiftedTimeChildOffset (g : ParabolicGridShift) : ℤ :=
  (shiftedTimePhase_coherent g).choose

theorem shiftedTimeChildOffset_spec (g : ParabolicGridShift) :
    4 * shiftedTimePhase g - shiftedTimePhase g = shiftedTimeChildOffset g :=
  (shiftedTimePhase_coherent g).choose_spec

/-- Eight spatial choices and four temporal choices. -/
abbrev ParabolicChildDigit := (Fin 3 → Fin 2) × Fin 4

theorem card_parabolicChildDigit : Fintype.card ParabolicChildDigit = 32 := by
  norm_num [ParabolicChildDigit, Fintype.card_prod, Fintype.card_fun]

/-- The actual thirty-two children of a cell in a fixed coherent shifted grid. -/
def shiftedParabolicChild (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (d : ParabolicChildDigit) : ParabolicDyadicIndex :=
  ⟨Q.scale + 1,
    fun i => 2 * Q.corner i + shiftedSpatialChildOffset g Q.scale i + (d.1 i : ℕ),
    4 * Q.timeCorner + shiftedTimeChildOffset g + (d.2 : ℕ)⟩

theorem shiftedParabolicChild_injective (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    Function.Injective (shiftedParabolicChild g Q) := by
  intro d e h
  apply Prod.ext
  · funext i
    apply Fin.ext
    have hc := congrArg (fun R => R.corner i) h
    dsimp [shiftedParabolicChild] at hc
    omega
  · apply Fin.ext
    have ht := congrArg ParabolicDyadicIndex.timeCorner h
    dsimp [shiftedParabolicChild] at ht
    omega

/-- Every child is geometrically contained in the parent. -/
theorem shiftedParabolicChild_subset (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (d : ParabolicChildDigit) :
    shiftedParabolicDyadicCell g (shiftedParabolicChild g Q d) ⊆
      shiftedParabolicDyadicCell g Q := by
  intro z hz
  constructor
  · apply mem_pi.mpr
    intro i hi
    have hzi := mem_pi.mp hz.1 i hi
    have hsub := shiftedGridInterval_child_subset (dyadicScale_pos (Q.scale + 1)) 2
      (shiftedSpatialPhase g Q.scale i) (shiftedSpatialPhase g (Q.scale + 1) i)
      (shiftedSpatialChildOffset g Q.scale i) (Q.corner i)
      (shiftedSpatialChildOffset_spec g Q.scale i) (d.1 i)
    norm_num only at hsub
    rw [← dyadicScale_step Q.scale] at hsub
    exact hsub hzi
  · have hsub := shiftedGridInterval_child_subset (dyadicScale_pos (2 * (Q.scale + 1))) 4
      (shiftedTimePhase g) (shiftedTimePhase g) (shiftedTimeChildOffset g)
      Q.timeCorner (shiftedTimeChildOffset_spec g) d.2
    norm_num only at hsub
    rw [← dyadicTimeScale_step Q.scale] at hsub
    exact hsub hz.2

/-- The product of the spatial and temporal refinements covers the parent exactly. -/
theorem shiftedParabolicDyadicCell_eq_iUnion_children
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    shiftedParabolicDyadicCell g Q =
      ⋃ d : ParabolicChildDigit, shiftedParabolicDyadicCell g (shiftedParabolicChild g Q d) := by
  apply Subset.antisymm
  · intro z hz
    have hspatial : ∀ i : Fin 3, ∃ d : Fin 2,
        z.1 i ∈ shiftedGridInterval (dyadicScale (Q.scale + 1))
          (shiftedSpatialPhase g (Q.scale + 1) i)
          (2 * Q.corner i + shiftedSpatialChildOffset g Q.scale i + (d : ℕ)) := by
      intro i
      have hzi := mem_pi.mp hz.1 i (mem_univ i)
      have hpart := shiftedGridInterval_eq_iUnion_children (dyadicScale_pos (Q.scale + 1)) 2
          (shiftedSpatialPhase g Q.scale i) (shiftedSpatialPhase g (Q.scale + 1) i)
          (shiftedSpatialChildOffset g Q.scale i) (Q.corner i)
          (shiftedSpatialChildOffset_spec g Q.scale i)
      norm_num only at hpart
      rw [dyadicScale_step Q.scale, hpart] at hzi
      exact mem_iUnion.mp hzi
    choose ds hds using hspatial
    have ht := hz.2
    have hpart := shiftedGridInterval_eq_iUnion_children (dyadicScale_pos (2 * (Q.scale + 1))) 4
        (shiftedTimePhase g) (shiftedTimePhase g) (shiftedTimeChildOffset g)
        Q.timeCorner (shiftedTimeChildOffset_spec g)
    norm_num only at hpart
    rw [shiftedParabolicDyadicTime, dyadicTimeScale_step Q.scale, hpart] at ht
    obtain ⟨dt, hdt⟩ := mem_iUnion.mp ht
    refine mem_iUnion.mpr ⟨(ds, dt), ?_, hdt⟩
    exact mem_pi.mpr fun i _ => hds i
  · intro z hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp hz
    exact shiftedParabolicChild_subset g Q d hd

/-- Exact spatial side ratio over a prescribed number of refinement steps. -/
theorem dyadicScale_nat_add (n : ℤ) (k : ℕ) :
    dyadicScale n = (2 : ℝ) ^ k * dyadicScale (n + k) := by
  calc
    dyadicScale n = (2 : ℝ) ^ ((k : ℤ) + -(n + k)) := by
      dsimp [dyadicScale]
      congr 1
      omega
    _ = (2 : ℝ) ^ (k : ℤ) * (2 : ℝ) ^ (-(n + k) : ℤ) :=
      zpow_add₀ (by norm_num) _ _
    _ = (2 : ℝ) ^ k * dyadicScale (n + k) := by rw [zpow_natCast]; rfl

theorem exists_shiftedSpatialRefinementOffset (g : ParabolicGridShift)
    (n : ℤ) (k : ℕ) (i : Fin 3) :
    ∃ c : ℤ, (2 : ℝ) ^ k * shiftedSpatialPhase g n i -
      shiftedSpatialPhase g (n + k) i = c := by
  obtain ⟨M, c, _, hscale, hphase⟩ := coherent_grid_ratio 2 dyadicScale
    (fun m => shiftedSpatialPhase g m i) (by norm_num) dyadicScale_step
    (fun m => shiftedSpatialPhase_coherent g m i) n (n + k) (by omega)
  have hM : (M : ℝ) = (2 : ℝ) ^ k := by
    apply mul_right_cancel₀ (dyadicScale_pos (n + k)).ne'
    exact hscale.symm.trans (dyadicScale_nat_add n k)
  exact ⟨c, hM ▸ hphase⟩

/-- The accumulated integral phase correction across `k` spatial steps. -/
def shiftedSpatialRefinementOffset (g : ParabolicGridShift) (n : ℤ) (k : ℕ)
    (i : Fin 3) : ℤ := (exists_shiftedSpatialRefinementOffset g n k i).choose

theorem shiftedSpatialRefinementOffset_spec (g : ParabolicGridShift)
    (n : ℤ) (k : ℕ) (i : Fin 3) :
    (2 : ℝ) ^ k * shiftedSpatialPhase g n i - shiftedSpatialPhase g (n + k) i =
      shiftedSpatialRefinementOffset g n k i :=
  (exists_shiftedSpatialRefinementOffset g n k i).choose_spec

/-- All spatial positions at depth `k` relative to a fixed root cube. -/
abbrev SpatialRefinementDigit (k : ℕ) := Fin 3 → Fin (2 ^ k)

theorem card_spatialRefinementDigit (k : ℕ) :
    Fintype.card (SpatialRefinementDigit k) = 8 ^ k := by
  simp only [SpatialRefinementDigit, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm k 3, pow_mul]
  norm_num

def shiftedSpatialDescendantCorner (g : ParabolicGridShift) (n : ℤ)
    (a : DyadicCorner) (k : ℕ) (d : SpatialRefinementDigit k) : DyadicCorner :=
  fun i => (2 ^ k : ℕ) * a i + shiftedSpatialRefinementOffset g n k i + (d i : ℕ)

theorem shiftedSpatialDescendantCorner_injective (g : ParabolicGridShift)
    (n : ℤ) (a : DyadicCorner) (k : ℕ) :
    Function.Injective (shiftedSpatialDescendantCorner g n a k) := by
  intro d e h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  dsimp [shiftedSpatialDescendantCorner] at hi
  omega

theorem shiftedSpatialDescendant_subset (g : ParabolicGridShift) (n : ℤ)
    (a : DyadicCorner) (k : ℕ) (d : SpatialRefinementDigit k) :
    shiftedDyadicCube g (n + k) (shiftedSpatialDescendantCorner g n a k d) ⊆
      shiftedDyadicCube g n a := by
  intro x hx
  apply mem_pi.mpr
  intro i hi
  have hsub := shiftedGridInterval_child_subset (dyadicScale_pos (n + k)) (2 ^ k)
    (shiftedSpatialPhase g n i) (shiftedSpatialPhase g (n + k) i)
    (shiftedSpatialRefinementOffset g n k i) (a i)
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      shiftedSpatialRefinementOffset_spec g n k i) (d i)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hsub
  rw [← dyadicScale_nat_add n k] at hsub
  exact hsub (mem_pi.mp hx i hi)

/-- Every root cube is exactly partitioned by the spatial cubes at depth `k`. -/
theorem shiftedDyadicCube_eq_iUnion_descendants (g : ParabolicGridShift) (n : ℤ)
    (a : DyadicCorner) (k : ℕ) :
    shiftedDyadicCube g n a = ⋃ d : SpatialRefinementDigit k,
      shiftedDyadicCube g (n + k) (shiftedSpatialDescendantCorner g n a k d) := by
  apply Subset.antisymm
  · intro x hx
    have hdigits : ∀ i : Fin 3, ∃ d : Fin (2 ^ k),
        x i ∈ shiftedGridInterval (dyadicScale (n + k)) (shiftedSpatialPhase g (n + k) i)
          ((2 ^ k : ℕ) * a i + shiftedSpatialRefinementOffset g n k i + (d : ℕ)) := by
      intro i
      have hi := mem_pi.mp hx i (mem_univ i)
      have hpart := shiftedGridInterval_eq_iUnion_children (dyadicScale_pos (n + k))
        (2 ^ k) (shiftedSpatialPhase g n i) (shiftedSpatialPhase g (n + k) i)
        (shiftedSpatialRefinementOffset g n k i) (a i)
        (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          shiftedSpatialRefinementOffset_spec g n k i)
      simp only [Nat.cast_pow, Nat.cast_ofNat] at hpart
      rw [dyadicScale_nat_add n k, hpart] at hi
      exact mem_iUnion.mp hi
    choose d hd using hdigits
    exact mem_iUnion.mpr ⟨d, mem_pi.mpr fun i _ => hd i⟩
  · intro x hx
    obtain ⟨d, hd⟩ := mem_iUnion.mp hx
    exact shiftedSpatialDescendant_subset g n a k d hd

/-- The actual finite set of spatial descendant corners. -/
def shiftedSpatialDescendants (g : ParabolicGridShift) (n : ℤ)
    (a : DyadicCorner) (k : ℕ) : Finset DyadicCorner :=
  Finset.univ.image (shiftedSpatialDescendantCorner g n a k)

/-- A root has exactly `8 ^ k` spatial descendants at depth `k`. -/
theorem card_shiftedSpatialDescendants (g : ParabolicGridShift) (n : ℤ)
    (a : DyadicCorner) (k : ℕ) : (shiftedSpatialDescendants g n a k).card = 8 ^ k := by
  rw [shiftedSpatialDescendants,
    Finset.card_image_of_injective _ (shiftedSpatialDescendantCorner_injective g n a k),
    Finset.card_univ, card_spatialRefinementDigit]

theorem shiftedDyadicCube_nonempty (g : ParabolicGridShift) (n : ℤ) (a : DyadicCorner) :
    (shiftedDyadicCube g n a).Nonempty := by
  refine ⟨fun i => ((a i : ℝ) + shiftedSpatialPhase g n i) * dyadicScale n, ?_⟩
  apply mem_pi.mpr
  intro i _
  constructor
  · exact le_rfl
  · have hpos := dyadicScale_pos n
    nlinarith only [hpos]

theorem shiftedDyadicCorner_unique (g : ParabolicGridShift) (n : ℤ) {a b : DyadicCorner}
    {x : Vec3} (ha : x ∈ shiftedDyadicCube g n a) (hb : x ∈ shiftedDyadicCube g n b) :
    a = b := by
  funext i
  exact shiftedGridInterval_corner_unique (dyadicScale_pos n)
    (mem_pi.mp ha i (mem_univ i)) (mem_pi.mp hb i (mem_univ i))

/-- The enumeration contains all and only fine cubes inside the root. -/
theorem mem_shiftedSpatialDescendants_iff_subset (g : ParabolicGridShift) (n : ℤ)
    (a : DyadicCorner) (k : ℕ) (b : DyadicCorner) :
    b ∈ shiftedSpatialDescendants g n a k ↔
      shiftedDyadicCube g (n + k) b ⊆ shiftedDyadicCube g n a := by
  classical
  constructor
  · intro hb
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hb
    exact shiftedSpatialDescendant_subset g n a k d
  · intro hsub
    obtain ⟨x, hx⟩ := shiftedDyadicCube_nonempty g (n + k) b
    have hroot := hsub hx
    rw [shiftedDyadicCube_eq_iUnion_descendants g n a k] at hroot
    obtain ⟨d, hd⟩ := mem_iUnion.mp hroot
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _,
      (shiftedDyadicCorner_unique g (n + k) hx hd).symm⟩

/-- An interval of radius at most one grid length meets only the three cells
adjacent to its center's containing cell. -/
theorem shiftedGridInterval_corner_near {ℓ : ℝ} (hℓ : 0 < ℓ) (σ x t : ℝ) (a : ℤ)
    (ht : t ∈ shiftedGridInterval ℓ σ a) (hdist : |t - x| ≤ ℓ) :
    ⌊x / ℓ - σ⌋ - 1 ≤ a ∧ a ≤ ⌊x / ℓ - σ⌋ + 1 := by
  have htnorm := (mem_shiftedGridInterval_iff_div hℓ σ a t).mp ht
  have hxlo := Int.floor_le (x / ℓ - σ)
  have hxhi := Int.lt_floor_add_one (x / ℓ - σ)
  have htlo : x / ℓ - 1 ≤ t / ℓ := by
    rw [le_div_iff₀ hℓ]
    nlinarith only [(abs_le.mp hdist).1, div_mul_cancel₀ x hℓ.ne']
  have hthi : t / ℓ ≤ x / ℓ + 1 := by
    rw [div_le_iff₀ hℓ]
    nlinarith only [(abs_le.mp hdist).2, div_mul_cancel₀ x hℓ.ne']
  have hlo : (⌊x / ℓ - σ⌋ : ℝ) < (a : ℝ) + 2 := by
    linarith only [hxlo, htnorm.2, htlo]
  have hhi : (a : ℝ) < (⌊x / ℓ - σ⌋ : ℝ) + 2 := by
    linarith only [hxhi, htnorm.1, hthi]
  have hloInt : ⌊x / ℓ - σ⌋ < a + 2 := by exact_mod_cast hlo
  have hhiInt : a < ⌊x / ℓ - σ⌋ + 2 := by exact_mod_cast hhi
  omega

/-- Three neighboring choices in every spatial coordinate and in time. -/
abbrev NearbyParabolicCellDigit := (Fin 3 → Fin 3) × Fin 3

theorem card_nearbyParabolicCellDigit : Fintype.card NearbyParabolicCellDigit = 81 := by
  norm_num [NearbyParabolicCellDigit, Fintype.card_prod, Fintype.card_fun]

def nearbyParabolicCell (g : ParabolicGridShift) (n : ℤ) (z : ParabolicPoint)
    (d : NearbyParabolicCellDigit) : ParabolicDyadicIndex :=
  ⟨n, fun i => ⌊z.1 i / dyadicScale n - shiftedSpatialPhase g n i⌋ - 1 + (d.1 i : ℕ),
    shiftedTimeCellSelector g n z.2 - 1 + (d.2 : ℕ)⟩

theorem nearbyParabolicCell_injective (g : ParabolicGridShift) (n : ℤ) (z : ParabolicPoint) :
    Function.Injective (nearbyParabolicCell g n z) := by
  intro d e h
  apply Prod.ext
  · funext i
    apply Fin.ext
    have hc := congrArg (fun Q => Q.corner i) h
    dsimp [nearbyParabolicCell] at hc
    omega
  · apply Fin.ext
    have ht := congrArg ParabolicDyadicIndex.timeCorner h
    dsimp [nearbyParabolicCell] at ht
    omega

/-- A fixed explicit set of eighty-one neighboring cells. -/
def nearbyParabolicCells (g : ParabolicGridShift) (n : ℤ) (z : ParabolicPoint) :
    Finset ParabolicDyadicIndex := Finset.univ.image (nearbyParabolicCell g n z)

theorem card_nearbyParabolicCells (g : ParabolicGridShift) (n : ℤ) (z : ParabolicPoint) :
    (nearbyParabolicCells g n z).card = 81 := by
  rw [nearbyParabolicCells, Finset.card_image_of_injective _
    (nearbyParabolicCell_injective g n z), Finset.card_univ, card_nearbyParabolicCellDigit]

/-- Every cell at this level meeting a ball of radius at most its side length
belongs to the explicit eighty-one-element set. -/
theorem mem_nearbyParabolicCells_of_intersect_ball (g : ParabolicGridShift) (n : ℤ)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 ≤ r) (hside : r ≤ dyadicScale n)
    (Q : ParabolicDyadicIndex) (hscale : Q.scale = n)
    (hint : (shiftedParabolicDyadicCell g Q ∩ Metric.closedBall z r).Nonempty) :
    Q ∈ nearbyParabolicCells g n z := by
  classical
  obtain ⟨m, a, b⟩ := Q
  dsimp at hscale
  subst m
  obtain ⟨w, hw, hball⟩ := hint
  have hbox := parabolic_closedBall_subset_box z hr hball
  have hspatial : ∀ i : Fin 3, ∃ d : Fin 3,
      a i = ⌊z.1 i / dyadicScale n - shiftedSpatialPhase g n i⌋ - 1 + (d : ℕ) := by
    intro i
    have hwi := mem_pi.mp hw.1 i (mem_univ i)
    have hbi := mem_pi.mp hbox.1 i (mem_univ i)
    have hdist : |w.1 i - z.1 i| ≤ dyadicScale n :=
      (abs_le.mpr (by constructor <;> linarith only [hbi.1, hbi.2])).trans hside
    have ha := shiftedGridInterval_corner_near (dyadicScale_pos n)
      (shiftedSpatialPhase g n i) (z.1 i) (w.1 i) (a i) hwi hdist
    let d : Fin 3 := ⟨(a i - (⌊z.1 i / dyadicScale n - shiftedSpatialPhase g n i⌋ - 1)).toNat,
      by omega⟩
    refine ⟨d, ?_⟩
    dsimp [d]
    omega
  choose ds hds using hspatial
  have hsq : r ^ 2 ≤ dyadicScale n ^ 2 :=
    (sq_le_sq₀ hr (dyadicScale_pos n).le).mpr hside
  have htdist : |w.2 - z.2| ≤ dyadicScale (2 * n) := by
    rw [dyadicScale_two_mul]
    exact (abs_le.mpr (by constructor <;> linarith only [hbox.2.1, hbox.2.2])).trans hsq
  have hb := shiftedGridInterval_corner_near (dyadicScale_pos (2 * n))
    (shiftedTimePhase g) z.2 w.2 b hw.2 htdist
  let dt : Fin 3 := ⟨(b - (shiftedTimeCellSelector g n z.2 - 1)).toNat, by
    dsimp [shiftedTimeCellSelector]
    omega⟩
  have ht : b = shiftedTimeCellSelector g n z.2 - 1 + (dt : ℕ) := by
    dsimp [dt, shiftedTimeCellSelector]
    omega
  refine Finset.mem_image.mpr ⟨(ds, dt), Finset.mem_univ _, ?_⟩
  change (⟨n, _, _⟩ : ParabolicDyadicIndex) = ⟨n, a, b⟩
  congr 1
  · funext i
    exact (hds i).symm
  · exact ht.symm

end FluidSingularSets
