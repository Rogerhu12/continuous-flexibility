import ContinuousFlexibility.Analysis.N07bHeightRadialMembers
import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# Changing the left cutoff inside the natural physical output class

The physical and reference cutoffs agree near both endpoints of the open
core. Their difference need not be compactly supported on the whole real
line. We use only its almost-everywhere support for the restricted physical
measure, and the finite set of cells meeting an interior compact interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff

/-- A correction supported in an interior compact radial set almost
everywhere for the physical measure has every natural output weight. -/
theorem n07b_outputCellSquare_summable_of_ae_core_compact
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {J : Set ℝ} (hJ : IsCompact J) (hJcore : J ⊆ radialCore D)
    {g : PolarPoint → ℝ} (hg : RadialCellIntegrable D g)
    (hzero : ∀ᵐ p ∂radialPhysicalMeasure D, p.1 ∉ J → g p = 0)
    (γ M : ℝ) : Summable (outputCellSquare D γ M g) := by
  obtain ⟨C, hgeom, hpart, _, _, _, hfinite, _⟩ := hD
  have hcells : Set.Finite {m | (D.cells m ∩ J).Nonempty} := hfinite J hJ hJcore
  apply summable_of_hasFiniteSupport
  apply hcells.subset
  intro m hm
  by_contra hmiss
  have hz :
      (fun p : PolarPoint => (D.localizer m p.1 * g p) ^ 2)
        =ᵐ[radialPhysicalMeasure D] (fun _ => 0) := by
    filter_upwards [hzero] with p hp
    by_cases hχ : D.localizer m p.1 = 0
    · simp only [hχ, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    · have hrm : p.1 ∈ D.cells m := hpart.2.2.1 m hχ
      have hpJ : p.1 ∉ J := fun hj => hmiss ⟨p.1, hrm, hj⟩
      change (D.localizer m p.1 * g p) ^ 2 = 0
      rw [hp hpJ, mul_zero, zero_pow (by decide : 2 ≠ 0)]
  apply hm
  change outputCellSquare D γ M g m = 0
  rw [outputCellSquare, r11b_referenceCellSquare_eq_integral hgeom.2.1.le hg m,
    integral_congr_ae hz, integral_zero, mul_zero, mul_zero]

/-- An interior correction preserves the realized left constant. Its values
outside the physical annulus are unrestricted. -/
theorem n07b_outputRealization_add_ae_core_compact
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {γ M a : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M a U)
    {J : Set ℝ} (hJ : IsCompact J) (hJcore : J ⊆ radialCore D)
    {g : PolarPoint → ℝ} (hg : RadialCellIntegrable D g)
    (hzero : ∀ᵐ p ∂radialPhysicalMeasure D, p.1 ∉ J → g p = 0)
    (hperiod : Function.Periodic g (0, Real.pi))
    (heven : ∀ r θ, g (r, -θ) = g (r, θ)) :
    OutputRealization D γ M a ((fun p => U.1 p + g p), U.2) := by
  have hs := n07b_outputCellSquare_summable_of_ae_core_compact hD hJ hJcore hg hzero γ M
  have hV : OutputRealization D γ M 0 (g, 0) := by
    refine ⟨?_, ?_, hperiod, heven⟩
    · simpa only [outputRemainder, zero_mul, sub_zero] using hg
    · simpa only [outputRemainder, zero_mul, sub_zero] using hs
  obtain ⟨C, hgeom, _⟩ := hD
  have hsum := OutputRealization.add hgeom.2.1.le hU hV
  have he : U + (g, 0) = ((fun p => U.1 p + g p), U.2) := by
    apply Prod.ext
    · funext p
      rfl
    · change U.2 + 0 = U.2
      exact add_zero _
  rw [add_zero, he] at hsum
  exact hsum

/-- Only support inside the open core is asserted. The reference cutoff's
values on the exterior half-lines do not enter this conclusion. -/
theorem n07b_cutoff_difference_core_support {D : ReferenceData}
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) (hborder : RadialTrueBorder D) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      ∀ r ∈ radialCore D, r ∉ J → χ r - D.chiLeft r = 0 := by
  obtain ⟨δ, hδ, _, hleft, hright⟩ := hχ.2.1
  obtain ⟨ε, hε, hDleft, hDright⟩ := hborder.2.2.2.2.2
  let d := min δ ε
  have hd : 0 < d := lt_min hδ hε
  have hdδ : d ≤ δ := min_le_left _ _
  have hdε : d ≤ ε := min_le_right _ _
  refine ⟨Icc (D.a + d) (D.b - d), isCompact_Icc, ?_, ?_⟩
  · intro r hr
    constructor <;> linarith only [hr.1, hr.2, hd]
  · intro r hr hnot
    by_cases hl : r < D.a + d
    · have h1 : χ r = 1 := hleft r (by linarith only [hl, hdδ])
      have h2 : D.chiLeft r = 1 :=
        hDleft r ⟨hr.1, by linarith only [hl, hdε]⟩
      rw [h1, h2, sub_self]
    · have hr' : D.b - d < r :=
        lt_of_not_ge (fun hh => hnot ⟨le_of_not_gt hl, hh⟩)
      have h1 : χ r = 0 := hright r (by linarith only [hr', hdδ])
      have h2 : D.chiLeft r = 0 :=
        hDright r ⟨by linarith only [hr', hdε], hr.2⟩
      rw [h1, h2, sub_self]

/-- A height plus the actual physical cutoff has the same free left
constant in the natural output class defined using the reference cutoff. -/
theorem n07b_heightMember_outputRealization_cutoff
    {D : ReferenceData} {T : MaterialData} {χ : ℝ → ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) (hχ : CutoffConditions D χ)
    {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β)
    {f : PolarPoint → ℝ} (hf : HeightMember D T β f) (M a μ : ℝ) :
    OutputRealization D γ M a ((fun p => f p + a * χ p.1), μ) := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := n07b_cutoff_difference_core_support hχ hborder
  have hdata := hD
  obtain ⟨C, _, hpart, _⟩ := hdata
  let g : PolarPoint → ℝ := fun p => a * (χ p.1 - D.chiLeft p.1)
  have hgcont : Continuous g :=
    continuous_const.mul
      ((hχ.1.continuous.comp continuous_fst).sub
        (hborder.2.2.2.2.1.continuous.comp continuous_fst))
  have hg : RadialCellIntegrable D g := by
    intro m
    exact r11b_continuous_memLp (((hpart.1 m).continuous.comp continuous_fst).mul hgcont)
  have hgz : ∀ᵐ p ∂radialPhysicalMeasure D, p.1 ∉ J → g p = 0 := by
    filter_upwards [ae_restrict_mem
      (show MeasurableSet (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) from
        measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    intro hpJ
    change a * (χ p.1 - D.chiLeft p.1) = 0
    rw [hzero p.1 hp.1 hpJ, mul_zero]
  have hgp : Function.Periodic g (0, Real.pi) := by
    intro p
    change a * (χ (p.1 + 0) - D.chiLeft (p.1 + 0)) =
      a * (χ p.1 - D.chiLeft p.1)
    rw [add_zero]
  have hge : ∀ r θ, g (r, -θ) = g (r, θ) := fun _ _ => rfl
  have hbase := n07b_heightMember_outputRealization hD hT hβ hγβ hf M a μ
  have hsum := n07b_outputRealization_add_ae_core_compact hD hbase
    hJ hJcore hg hgz hgp hge
  have he :
      (fun p : PolarPoint => (f p + a * D.chiLeft p.1) + a * (χ p.1 - D.chiLeft p.1)) =
        fun p => f p + a * χ p.1 := by
    funext p
    ring
  change OutputRealization D γ M a
    ((fun p => (f p + a * D.chiLeft p.1) + a * (χ p.1 - D.chiLeft p.1)), μ) at hsum
  rw [he] at hsum
  exact hsum

/-- In particular the physical HeightPair field retains its own left
constant when viewed in a strictly weaker natural graph. -/
theorem n07b_heightPair_outputRealization {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    {γ : ℝ} (hγ : γ < (3 / 4 : ℝ)) (M : ℝ) (u : HeightPair S) (μ : ℝ) :
    OutputRealization D γ M u.2 (heightPairField S u, μ) :=
  n07b_heightMember_outputRealization_cutoff hD hT hborder hS.2.2.1
    (by norm_num : (0 : ℝ) < 3 / 4) hγ
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u.1) M u.2 μ

end ContinuousFlexibility.Statements
