module

public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Sequences

/-!
# Simultaneous selection of infinitely many height ratios

This is the quantifier core of `lem:radial-product-selection` (manuscript §5,
`eq:rad-eq-js13`).  The height ratios form the compact cube `[1, 2]^ℕ`.  There
are countably many conditions.  Condition `k` is attached to one coordinate
`c k`; when every other coordinate is frozen, the heights violating it have
Lebesgue measure at most `ε k`.  The good set of each condition is closed in
the product topology.  If `∑ ε k < 1`, one sequence satisfies all conditions.

The order of quantifiers is `∃ σ, ∀ k`.  The proof is the one in the
manuscript: Fubini on the finite cube of the first coordinates together with a
union bound gives a point satisfying the conditions attached to those
coordinates; compactness of the cube and closedness of each good set pass to
the limit.  No measure on the infinite product is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Function MeasureTheory
open scoped ENNReal Topology

/-- The compact cube of admissible height ratios `σ n ∈ [1, 2]`. -/
def heightCube : Set (ℕ → ℝ) := Set.pi univ fun _ => Icc (1 : ℝ) 2

theorem mem_heightCube {σ : ℕ → ℝ} : σ ∈ heightCube ↔ ∀ n, σ n ∈ Icc (1 : ℝ) 2 :=
  ⟨fun h n => h n (mem_univ n), fun h n _ => h n⟩

theorem isCompact_heightCube : IsCompact heightCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_heightCube : IsClosed heightCube := isCompact_heightCube.isClosed

theorem update_mem_heightCube {σ : ℕ → ℝ} (hσ : σ ∈ heightCube) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 2) : update σ n t ∈ heightCube := by
  rw [mem_heightCube] at hσ ⊢
  intro m
  by_cases h : m = n
  · subst h
    simpa using ht
  · simpa [update_of_ne h] using hσ m

/-- Normalized Lebesgue measure on one height interval. -/
private def heightLaw : Measure ℝ := volume.restrict (Icc (1 : ℝ) 2)

private instance : IsProbabilityMeasure heightLaw :=
  ⟨by rw [heightLaw, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩

/-- The one-coordinate hypothesis, as an integral of the indicator of the bad
part of the cube.  The frozen point `x` is arbitrary. -/
private theorem lintegral_slice_le {B : Set (ℕ → ℝ)} (hB : MeasurableSet (heightCube ∩ B))
    (i : ℕ) {ε : ℝ≥0∞}
    (hslice : ∀ σ ∈ heightCube, volume {t | t ∈ Icc (1 : ℝ) 2 ∧ update σ i t ∈ B} ≤ ε)
    (x : ℕ → ℝ) :
    ∫⁻ t, (heightCube ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) (update x i t) ∂heightLaw ≤ ε := by
  have hS : MeasurableSet {t : ℝ | update x i t ∈ heightCube ∩ B} := measurable_update x hB
  have h1 : ∫⁻ t, (heightCube ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) (update x i t) ∂heightLaw =
      heightLaw {t : ℝ | update x i t ∈ heightCube ∩ B} := by
    rw [← lintegral_indicator_one hS]
    refine lintegral_congr fun t => ?_
    by_cases ht : update x i t ∈ heightCube ∩ B
    · have ht' : t ∈ {t : ℝ | update x i t ∈ heightCube ∩ B} := ht
      rw [indicator_of_mem ht, indicator_of_mem ht']
      rfl
    · have ht' : t ∉ {t : ℝ | update x i t ∈ heightCube ∩ B} := ht
      rw [indicator_of_notMem ht, indicator_of_notMem ht']
  rw [h1, heightLaw, Measure.restrict_apply hS]
  rcases ({t : ℝ | update x i t ∈ heightCube ∩ B} ∩ Icc (1 : ℝ) 2).eq_empty_or_nonempty with
    h | ⟨t₀, ht₀⟩
  · rw [h]
    simp
  · refine (measure_mono ?_).trans (hslice (update x i t₀) ht₀.1.1)
    intro t ht
    refine ⟨ht.2, ?_⟩
    rw [update_idem]
    exact ht.1.2

/-- Finite stage: the conditions attached to finitely many coordinates can be
satisfied simultaneously inside the cube. -/
theorem exists_mem_heightCube_good_on_finset {κ : Type*} [Countable κ]
    (c : κ → ℕ) (Bad : κ → Set (ℕ → ℝ)) (ε : κ → ℝ≥0∞)
    (hmeas : ∀ k, MeasurableSet (heightCube ∩ Bad k))
    (hslice : ∀ k, ∀ σ ∈ heightCube,
      volume {t | t ∈ Icc (1 : ℝ) 2 ∧ update σ (c k) t ∈ Bad k} ≤ ε k)
    (hsum : ∑' k, ε k < 1) (s : Finset ℕ) :
    ∃ σ ∈ heightCube, ∀ k, c k ∈ s → σ ∉ Bad k := by
  classical
  let x₀ : ℕ → ℝ := fun _ => 1
  let f : κ → (ℕ → ℝ) → ℝ≥0∞ := fun k => (heightCube ∩ Bad k).indicator fun _ => 1
  have hf : ∀ k, Measurable (f k) := fun k => measurable_const.indicator (hmeas k)
  let π : Measure (∀ _ : s, ℝ) := Measure.pi fun _ : s => heightLaw
  have hmarg : ∀ k, c k ∈ s → ∫⁻ y, f k (updateFinset x₀ s y) ∂π ≤ ε k := by
    intro k hk
    have h1 : (∫⋯∫⁻_s, f k ∂(fun _ : ℕ => heightLaw)) x₀ ≤ ε k := by
      rw [lmarginal_erase' (f k) (hf k) hk]
      calc (∫⋯∫⁻_(s.erase (c k)),
              (fun x => ∫⁻ t, f k (update x (c k) t) ∂heightLaw) ∂(fun _ : ℕ => heightLaw)) x₀
          ≤ (∫⋯∫⁻_(s.erase (c k)), (fun _ => ε k) ∂(fun _ : ℕ => heightLaw)) x₀ :=
            lmarginal_mono (fun x => lintegral_slice_le (hmeas k) (c k) (hslice k) x) x₀
        _ = ε k := by simp [lmarginal]
    exact h1
  have hπ : π = (Measure.pi fun _ : s => (volume : Measure ℝ)).restrict
      (Set.pi univ fun _ => Icc (1 : ℝ) 2) :=
    (Measure.restrict_pi_pi (fun _ : s => (volume : Measure ℝ)) fun _ => Icc (1 : ℝ) 2).symm
  have hae : ∀ᵐ y ∂π, ∀ i : s, y i ∈ Icc (1 : ℝ) 2 := by
    rw [hπ]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)] with y hy i
    exact hy i (mem_univ i)
  let G : (∀ _ : s, ℝ) → ℝ≥0∞ := fun y => ∑' k : {k // c k ∈ s}, f k (updateFinset x₀ s y)
  have hG : ∫⁻ y, G y ∂π < 1 := by
    calc ∫⁻ y, G y ∂π = ∑' k : {k // c k ∈ s}, ∫⁻ y, f k (updateFinset x₀ s y) ∂π :=
          lintegral_tsum fun k => ((hf k).comp measurable_updateFinset).aemeasurable
      _ ≤ ∑' k : {k // c k ∈ s}, ε k := ENNReal.tsum_le_tsum fun k => hmarg k k.2
      _ ≤ ∑' k, ε k := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective ε
      _ < 1 := hsum
  obtain ⟨y, hy, hGy⟩ : ∃ y, (∀ i : s, y i ∈ Icc (1 : ℝ) 2) ∧ G y < 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hone : (1 : ℝ≥0∞) ≤ ∫⁻ y, G y ∂π := by
      calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂π := by simp
        _ ≤ ∫⁻ y, G y ∂π := lintegral_mono_ae (hae.mono fun y hy => hcon y hy)
    exact (not_le.mpr hG) hone
  have hσ : updateFinset x₀ s y ∈ heightCube := by
    rw [mem_heightCube]
    intro n
    by_cases hn : n ∈ s
    · simpa [updateFinset_def, hn] using hy ⟨n, hn⟩
    · simp [updateFinset_def, hn, x₀]
  refine ⟨updateFinset x₀ s y, hσ, fun k hk hbad => ?_⟩
  have hmem : updateFinset x₀ s y ∈ heightCube ∩ Bad k := ⟨hσ, hbad⟩
  have h1 : f k (updateFinset x₀ s y) = 1 := indicator_of_mem hmem _
  have h2 : f k (updateFinset x₀ s y) ≤ G y :=
    ENNReal.le_tsum (f := fun k : {k // c k ∈ s} => f k (updateFinset x₀ s y)) (⟨k, hk⟩ : {k // c k ∈ s})
  rw [h1] at h2
  exact (not_le.mpr hGy) h2

/-- **Simultaneous selection.**  Countably many closed conditions on the cube
`[1, 2]^ℕ`, each attached to one coordinate and each excluding a set of
measure at most `ε k` in that coordinate, uniformly in all other coordinates,
have a common solution as soon as `∑ ε k < 1`. -/
theorem exists_simultaneous_selection {κ : Type*} [Countable κ]
    (c : κ → ℕ) (Bad : κ → Set (ℕ → ℝ)) (ε : κ → ℝ≥0∞)
    (hclosed : ∀ k, IsClosed (heightCube \ Bad k))
    (hslice : ∀ k, ∀ σ ∈ heightCube,
      volume {t | t ∈ Icc (1 : ℝ) 2 ∧ update σ (c k) t ∈ Bad k} ≤ ε k)
    (hsum : ∑' k, ε k < 1) :
    ∃ σ ∈ heightCube, ∀ k, σ ∉ Bad k := by
  have hmeas : ∀ k, MeasurableSet (heightCube ∩ Bad k) := by
    intro k
    rw [← sdiff_sdiff_right_self]
    exact isClosed_heightCube.measurableSet.diff (hclosed k).measurableSet
  choose τ hτcube hτgood using fun M : ℕ =>
    exists_mem_heightCube_good_on_finset c Bad ε hmeas hslice hsum (Finset.range M)
  obtain ⟨σ, hσ, φ, hφ, hlim⟩ := isCompact_heightCube.tendsto_subseq hτcube
  refine ⟨σ, hσ, fun k hk => ?_⟩
  have hev : ∀ᶠ m in atTop, (τ ∘ φ) m ∈ heightCube \ Bad k := by
    filter_upwards [eventually_gt_atTop (c k)] with m hm
    exact ⟨hτcube _, hτgood _ k (Finset.mem_range.mpr (hm.trans_le (hφ.id_le m)))⟩
  exact ((hclosed k).mem_of_tendsto hlim hev).2 hk

end ContinuousFlexibility.Radial
