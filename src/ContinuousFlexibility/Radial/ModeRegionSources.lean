import ContinuousFlexibility.Radial.MatchingGraphRestrictions

/-!
# Actual Hilbert-space source restrictions

The two source maps are constructed from measurable indicators. Their
coefficients, scalar rows, complementary decomposition and support are
proved without assuming a matching realization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Restrict an actual modal Hilbert vector to a measurable region. -/
def modeRegionVector (D : ReferenceData) (J : Set ℝ) (hJ : MeasurableSet J)
    (f : RadialModeL2 D) : RadialModeL2 D :=
  (MemLp.indicator hJ (Lp.memLp f)).toLp (J.indicator (f : ℝ → ℝ))

theorem modeRegionVector_coe (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (f : RadialModeL2 D) :
    (modeRegionVector D J hJ f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      J.indicator (f : ℝ → ℝ) :=
  MemLp.coeFn_toLp _

theorem modeRegionVector_add (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (f g : RadialModeL2 D) :
    modeRegionVector D J hJ (f + g) =
      modeRegionVector D J hJ f + modeRegionVector D J hJ g := by
  classical
  apply Lp.ext
  filter_upwards [modeRegionVector_coe D J hJ (f + g),
    modeRegionVector_coe D J hJ f, modeRegionVector_coe D J hJ g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (modeRegionVector D J hJ f) (modeRegionVector D J hJ g)]
    with r hsum hf hg hfg hout
  by_cases hr : r ∈ J
  · simpa only [Set.indicator_of_mem hr, Pi.add_apply, hf, hg, hfg, hout] using hsum
  · simpa only [Set.indicator_of_notMem hr, Pi.add_apply, hf, hg, zero_add, hout]
      using hsum

theorem modeRegionVector_smul (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (c : ℝ) (f : RadialModeL2 D) :
    modeRegionVector D J hJ (c • f) = c • modeRegionVector D J hJ f := by
  classical
  apply Lp.ext
  filter_upwards [modeRegionVector_coe D J hJ (c • f),
    modeRegionVector_coe D J hJ f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (modeRegionVector D J hJ f)] with r hcf hf hsm hout
  by_cases hr : r ∈ J
  · simpa only [Set.indicator_of_mem hr, Pi.smul_apply, smul_eq_mul, hf, hsm, hout]
      using hcf
  · simpa only [Set.indicator_of_notMem hr, Pi.smul_apply, smul_eq_mul,
      hf, mul_zero, hout] using hcf

theorem modeRegionVector_norm_le (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (f : RadialModeL2 D) :
    ‖modeRegionVector D J hJ f‖ ≤ ‖f‖ := by
  classical
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [modeRegionVector_coe D J hJ f] with r hr
  by_cases hx : r ∈ J
  · simp only [hr, Set.indicator_of_mem hx, le_refl]
  · simp only [hr, Set.indicator_of_notMem hx, norm_zero, norm_nonneg]

/-- The restriction is a bounded linear operator with norm at most one. -/
def modeRegionProjection (D : ReferenceData) (J : Set ℝ) (hJ : MeasurableSet J) :
    RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  LinearMap.mkContinuous
    { toFun := modeRegionVector D J hJ
      map_add' := modeRegionVector_add D J hJ
      map_smul' := modeRegionVector_smul D J hJ }
    1 (by
      intro f
      change ‖modeRegionVector D J hJ f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using modeRegionVector_norm_le D J hJ f)

theorem modeRegionVector_idempotent (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (f : RadialModeL2 D) :
    modeRegionVector D J hJ (modeRegionVector D J hJ f) =
      modeRegionVector D J hJ f := by
  classical
  apply Lp.ext
  filter_upwards [modeRegionVector_coe D J hJ (modeRegionVector D J hJ f),
    modeRegionVector_coe D J hJ f] with r htwice honce
  by_cases hr : r ∈ J
  · simpa only [Set.indicator_of_mem hr] using htwice
  · rw [htwice, Set.indicator_of_notMem hr, honce, Set.indicator_of_notMem hr]

/-- The inner source retains the entire scalar source. -/
def modeInnerSource (D : ReferenceData) (l h : ℝ)
    (F : RadialModePair D) : RadialModePair D :=
  (modeRegionVector D (Ioo l h) measurableSet_Ioo F.1, F.2)

/-- The exterior source has zero scalar source. -/
def modeOuterSource (D : ReferenceData) (l h : ℝ)
    (F : RadialModePair D) : RadialModePair D :=
  (modeRegionVector D (Ioo l h)ᶜ measurableSet_Ioo.compl F.1, 0)

theorem modeRegionSources_spec (D : ReferenceData) (l h : ℝ)
    (F : RadialModePair D) :
    (modeInnerSource D l h F).2 = F.2 ∧
    (modeOuterSource D l h F).2 = 0 ∧
    ((modeInnerSource D l h F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo l h then F.1 r else 0) ∧
    ((modeOuterSource D l h F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo l h then 0 else F.1 r) := by
  classical
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change (modeRegionVector D (Ioo l h) measurableSet_Ioo F.1 : ℝ → ℝ) =ᵐ[
        radialHilbertMeasure D] _
    filter_upwards [modeRegionVector_coe D (Ioo l h) measurableSet_Ioo F.1] with r hr
    by_cases hx : r ∈ Ioo l h
    · simpa only [Set.indicator_of_mem hx, if_pos hx] using hr
    · simpa only [Set.indicator_of_notMem hx, if_neg hx] using hr
  · change (modeRegionVector D (Ioo l h)ᶜ measurableSet_Ioo.compl F.1 : ℝ → ℝ) =ᵐ[
        radialHilbertMeasure D] _
    filter_upwards [modeRegionVector_coe D (Ioo l h)ᶜ
      measurableSet_Ioo.compl F.1] with r hr
    by_cases hx : r ∈ Ioo l h
    · simpa only [Set.indicator_of_notMem (not_not.mpr hx), if_pos hx] using hr
    · simpa only [Set.indicator_of_mem hx, if_neg hx] using hr

theorem modeRegionSources_add (D : ReferenceData) (l h : ℝ)
    (F : RadialModePair D) :
    modeInnerSource D l h F + modeOuterSource D l h F = F := by
  have hs := modeRegionSources_spec D l h F
  apply Prod.ext
  · change (modeInnerSource D l h F).1 + (modeOuterSource D l h F).1 = F.1
    apply Lp.ext
    filter_upwards [hs.2.2.1, hs.2.2.2,
      Lp.coeFn_add (modeInnerSource D l h F).1 (modeOuterSource D l h F).1]
      with r hi ho hsum
    rw [hsum, Pi.add_apply, hi, ho]
    split_ifs <;> simp
  · exact add_zero F.2

theorem modeInnerSource_zero_outside (D : ReferenceData) (l h : ℝ)
    (F : RadialModePair D) :
    ((modeInnerSource D l h F).1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo l h)ᶜ] (fun _ => 0) := by
  filter_upwards [ae_restrict_of_ae (modeRegionSources_spec D l h F).2.2.1,
    ae_restrict_mem measurableSet_Ioo.compl] with r hr hout
  exact hr.trans (if_neg hout)

theorem modeOuterSource_zero_inside (D : ReferenceData) (l h : ℝ)
    (F : RadialModePair D) :
    ((modeOuterSource D l h F).1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo l h)] (fun _ => 0) := by
  filter_upwards [ae_restrict_of_ae (modeRegionSources_spec D l h F).2.2.2,
    ae_restrict_mem measurableSet_Ioo] with r hr hin
  exact hr.trans (if_pos hin)

/-- Keep the boundary values while extending an inner representative by zero. -/
def modeInnerExtension (l h : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  (Icc l h).indicator u

theorem modeInnerExtension_eqOn (l h : ℝ) (u : ℝ → ℝ) :
    EqOn (modeInnerExtension l h u) u (Icc l h) := by
  classical
  intro r hr
  exact Set.indicator_of_mem hr u

theorem modeInnerExtension_contDiffOn {l h : ℝ} {u : ℝ → ℝ} {n : ℕ∞ω}
    (hu : ContDiffOn ℝ n u (Icc l h)) :
    ContDiffOn ℝ n (modeInnerExtension l h u) (Icc l h) :=
  hu.congr (modeInnerExtension_eqOn l h u)

theorem modeInnerExtension_zero_outside {l h r : ℝ} {u : ℝ → ℝ}
    (hr : r < l ∨ h < r) : modeInnerExtension l h u r = 0 := by
  classical
  apply Set.indicator_of_notMem
  intro hx
  rcases hr with hr | hr
  · exact (not_le_of_gt hr) hx.1
  · exact (not_le_of_gt hr) hx.2

/-- Closed and open interval restrictions represent the same Hilbert vector;
the closed interval version preserves both traces pointwise. -/
theorem modeInnerSource_extension_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (l h : ℝ) (F : RadialModePair D)
    {u : ℝ → ℝ} (hu : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    ((modeInnerSource D l h F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      modeInnerExtension l h u := by
  classical
  filter_upwards [(modeRegionSources_spec D l h F).2.2.1, hu,
    matching_ae_ne hD l, matching_ae_ne hD h] with r hsrc hrep hl hh
  by_cases hi : r ∈ Ioo l h
  · rw [hsrc, if_pos hi, hrep]
    exact (modeInnerExtension_eqOn l h u (mem_Icc_of_Ioo hi)).symm
  · have hc : r ∉ Icc l h := by
      intro hc
      exact hi ⟨lt_of_le_of_ne hc.1 hl.symm, lt_of_le_of_ne hc.2 hh⟩
    rw [hsrc, if_neg hi]
    exact (Set.indicator_of_notMem hc u).symm

end ContinuousFlexibility.Radial
