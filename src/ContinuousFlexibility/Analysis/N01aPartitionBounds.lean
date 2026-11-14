module

public import ContinuousFlexibility.Analysis.N01aPartitionProperties
public import ContinuousFlexibility.Analysis.N01aPartitionDiameter
public import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Accumulating-profile bounds for the grouped partition

The coefficient sequence is enlarged by a factor of two. All physical
fields and every old cell's scale remain unchanged. This gives a new
accumulating profile with at most two enumerated cells per scale.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real

theorem n01aCoarseReference_accumulatingBounds (D : ReferenceData) (C : ℕ → ℝ)
    (hC : AccumulatingProfileBounds D C) (p : ℕ → ℝ)
    (hp : ∀ i, p i ∈ D.cells i)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) :
    AccumulatingProfileBounds (n01aCoarseReference D p hproper) (fun s => 2 * C s) := by
  rcases hC with ⟨hgeom, hpart, hpos, hne, hfinite, hlocal, hdist,
    hlower, hwjets, hinvjets, hwidth, habsorb, htrace⟩
  have hfull : AccumulatingProfileBounds D C :=
    ⟨hgeom, hpart, hpos, hne, hfinite, hlocal, hdist,
      hlower, hwjets, hinvjets, hwidth, habsorb, htrace⟩
  refine ⟨n01aCoarseReference_profileGeometry D p hproper hgeom,
    n01aCoarseReference_radialPartition D p hproper hpart,
    fun s => mul_pos (by norm_num) (hpos s),
    n01aCoarseReference_cell_nonempty D p hproper hne,
    n01aCellGroupIndex_proper D p hproper,
    n01aCoarseReference_locallyFiniteCells D p hproper hlocal,
    ?_, ?_, ?_, ?_,
    n01aCoarseReference_diameter D C hfull p hp hproper,
    habsorb, n01aCoarseReference_traceScaffold D p hproper htrace⟩
  · intro j r hr
    obtain ⟨i, hi, hri⟩ := (n01aCoarseReference_mem_cell D p hproper j r).mp hr
    rw [n01aCoarseReference_cellIndex D p hproper i j hi]
    have h := hdist i r hri
    have htwo : 0 < 2 * C 0 := mul_pos (by norm_num) (hpos 0)
    have hinv : (2 * C 0)⁻¹ ≤ (C 0)⁻¹ :=
      (inv_le_inv₀ htwo (hpos 0)).mpr (by linarith only [hpos 0])
    refine ⟨(mul_le_mul_of_nonneg_right hinv (exp_pos _).le).trans h.1, ?_⟩
    exact h.2.trans (mul_le_mul_of_nonneg_right (by linarith only [hpos 0])
      (exp_pos _).le)
  · intro j r hr
    obtain ⟨i, hi, hri⟩ := (n01aCoarseReference_mem_cell D p hproper j r).mp hr
    rw [n01aCoarseReference_cellIndex D p hproper i j hi]
    apply le_trans _ (hlower i r hri)
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg (hpos 0).le (sq_nonneg (D.cellIndex i : ℝ))]
  · intro j r hr s
    obtain ⟨i, hi, hri⟩ := (n01aCoarseReference_mem_cell D p hproper j r).mp hr
    rw [n01aCoarseReference_cellIndex D p hproper i j hi]
    apply (hwjets i r hri s).trans
    apply mul_le_mul (by linarith only [hpos s]) _ (exp_pos _).le
      (mul_nonneg (by norm_num) (hpos s).le)
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg (hpos s).le (sq_nonneg (D.cellIndex i : ℝ))]
  · intro j r hr s
    obtain ⟨i, hi, hri⟩ := (n01aCoarseReference_mem_cell D p hproper j r).mp hr
    rw [n01aCoarseReference_cellIndex D p hproper i j hi]
    have hE : 1 ≤ radialE (D.cellIndex i) :=
      one_le_exp_iff.mpr (Radial.radialQ_nonneg (D.cellIndex i))
    apply (hinvjets i r hri s).trans
    apply mul_le_mul (by linarith only [hpos s])
      (rpow_le_rpow_of_exponent_le hE (by linarith only [hpos s]))
      (rpow_nonneg (zero_le_one.trans hE) _)
      (mul_nonneg (by norm_num) (hpos s).le)

/-- Every accumulating profile has a finite-fiber coarsening whose scale
index grows at least linearly with the enumeration index. -/
theorem exists_n01a_grouped_profile {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ E : ReferenceData, ∃ σ : ℕ → ℕ,
      N01aReferenceCoarsening D E σ ∧ IsAccumulatingProfile E ∧
      Function.Surjective σ ∧ (∀ i, D.cells i ⊆ E.cells (σ i)) ∧
      ∀ j, j ≤ 2 * E.cellIndex j + 1 := by
  classical
  obtain ⟨C, hC⟩ := hD
  have hne : ∀ i, (D.cells i).Nonempty := hC.2.2.2.1
  have hp : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite := hC.2.2.2.2.1
  choose p hpoint using hne
  refine ⟨n01aCoarseReference D p hp, n01aCellGrouping D p hp,
    n01aCoarseReference_coarsening D p hp,
    ⟨fun s => 2 * C s, n01aCoarseReference_accumulatingBounds D C hC p hpoint hp⟩,
    n01aCellGrouping_surjective D p hp,
    n01aCoarseReference_cell_subset D p hp,
    n01aCellGroupIndex_lower D p hp⟩

end ContinuousFlexibility.Statements
