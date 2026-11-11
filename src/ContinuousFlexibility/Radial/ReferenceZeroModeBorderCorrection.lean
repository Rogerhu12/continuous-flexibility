import ContinuousFlexibility.Radial.ReferenceRadialCellBound
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The compact correction from the endpoint step to the actual border

The primitive is naturally normalized by a left half-interval step.
The frozen output norm uses the actual smooth chiLeft. Their difference
vanishes in both endpoint collars, hence meets only finitely many cells.
Its actual weighted radial L² norm is uniformly bounded for gamma in
[0,1] and every nonnegative output coefficient loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ENNReal

def referenceZeroModeBorderCorrection (D : ReferenceData) (r : ℝ) : ℝ :=
  (if r ≤ (D.a + D.b) / 2 then 1 else 0) - D.chiLeft r

theorem referenceZeroModeBorderCorrection_measurable {D : ReferenceData}
    (hB : RadialTrueBorder D) :
    Measurable (referenceZeroModeBorderCorrection D) := by
  unfold referenceZeroModeBorderCorrection
  exact (measurable_const.ite measurableSet_Iic measurable_const).sub
    hB.2.2.2.2.1.continuous.measurable

theorem referenceZeroModeBorderCorrection_compact_support {D : ReferenceData}
    (hab : D.a < D.b) (hB : RadialTrueBorder D) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∈ radialCore D, referenceZeroModeBorderCorrection D r ≠ 0 → r ∈ K := by
  obtain ⟨ε, hε, hleft, hright⟩ := hB.2.2.2.2.2
  let η : ℝ := min ε ((D.b - D.a) / 4)
  have hη : 0 < η := lt_min hε (by linarith)
  have hηε : η ≤ ε := min_le_left _ _
  have hηwidth : η ≤ (D.b - D.a) / 4 := min_le_right _ _
  have hlmid : D.a + η < (D.a + D.b) / 2 := by linarith
  have hmidr : (D.a + D.b) / 2 < D.b - η := by linarith
  refine ⟨Icc (D.a + η) (D.b - η), isCompact_Icc, ?_, ?_⟩
  · intro r hr
    constructor <;> linarith [hr.1, hr.2]
  · intro r hr hn
    constructor
    · by_contra hl
      have hrl : r < D.a + η := lt_of_not_ge hl
      have hm : r ≤ (D.a + D.b) / 2 := (hrl.trans hlmid).le
      have hχ : D.chiLeft r = 1 := hleft r ⟨hr.1, by linarith⟩
      exact hn (by simp only [referenceZeroModeBorderCorrection, if_pos hm, hχ, sub_self])
    · by_contra hh
      have hrr : D.b - η < r := lt_of_not_ge hh
      have hm : ¬r ≤ (D.a + D.b) / 2 := not_le.mpr (hmidr.trans hrr)
      have hχ : D.chiLeft r = 0 := hright r ⟨by linarith, hr.2⟩
      exact hn (by simp only [referenceZeroModeBorderCorrection, if_neg hm, hχ, sub_self])

theorem referenceZeroModeBorderCorrection_bounded {D : ReferenceData}
    (hB : RadialTrueBorder D) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ radialCore D,
      ‖referenceZeroModeBorderCorrection D r‖ ≤ B := by
  obtain ⟨B, hbound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hB.2.2.2.2.1.continuous.continuousOn : ContinuousOn D.chiLeft (Icc D.a D.b))
  refine ⟨1 + max B 0, by positivity, ?_⟩
  intro r hr
  have hstep : ‖(if r ≤ (D.a + D.b) / 2 then (1 : ℝ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  change ‖(if r ≤ (D.a + D.b) / 2 then (1 : ℝ) else 0) - D.chiLeft r‖ ≤ 1 + max B 0
  exact (norm_sub_le _ _).trans
    (add_le_add hstep ((hbound r ⟨hr.1.le, hr.2.le⟩).trans (le_max_left _ _)))

theorem referenceZeroModeBorderCorrection_uniform_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) :
    ∃ B : ℝ, 0 < B ∧ ∀ γ ∈ Icc (0 : ℝ) 1, ∀ M : ℝ, 0 ≤ M →
      MemLp (referenceZeroModeBorderCorrection D) 2
        (referenceRadialWeightedMeasure D γ (-M)) ∧
      (∫ r, referenceZeroModeBorderCorrection D r ^ 2
        ∂referenceRadialWeightedMeasure D γ (-M)) ≤ B := by
  classical
  obtain ⟨C, hgeom, hP, _, _, _, hfinite, _⟩ := hD
  obtain ⟨K, hK, hKcore, hsupport⟩ :=
    referenceZeroModeBorderCorrection_compact_support hgeom.2.1 hB
  obtain ⟨B₀, hB₀, hbound⟩ := referenceZeroModeBorderCorrection_bounded hB
  let hfin := hfinite K hK hKcore
  let s : Finset ℕ := hfin.toFinset
  let E : ℝ := (∑ m ∈ s, Real.exp (2 * radialS (D.cellIndex m))) + 1
  have hE : 0 < E := by
    have hs : 0 ≤ ∑ m ∈ s, Real.exp (2 * radialS (D.cellIndex m)) :=
      Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    dsimp only [E]
    linarith
  let A : ℝ := E * B₀ ^ 2
  have hA : 0 < A := mul_pos hE (sq_pos_of_pos hB₀)
  have hL : 0 < D.b - D.a := sub_pos.mpr hgeom.2.1
  refine ⟨(D.b - D.a) * A + 1, by positivity, ?_⟩
  intro γ hγ M hM
  have hcell (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) :
      Real.exp (2 * (-M) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        referenceZeroModeBorderCorrection D r ^ 2 ≤ A := by
    by_cases hz : referenceZeroModeBorderCorrection D r = 0
    · simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
      exact hA.le
    · have hrc := hP.2.2.2.1 m hr
      have hms : m ∈ s := hfin.mem_toFinset.mpr ⟨r, hr, hsupport r hrc hz⟩
      have hweight : Real.exp (2 * radialS (D.cellIndex m)) ≤ E := by
        have hs := Finset.single_le_sum
          (fun k (_ : k ∈ s) => (Real.exp_pos (2 * radialS (D.cellIndex k))).le) hms
        dsimp only [E]
        linarith
      have hexp :
          Real.exp (2 * (-M) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) ≤
          Real.exp (2 * radialS (D.cellIndex m)) := by
        apply Real.exp_le_exp.mpr
        have hq := mul_nonneg hM (Radial.radialQ_nonneg (D.cellIndex m))
        have hs := mul_nonneg (sub_nonneg.mpr hγ.2) (radialS_nonneg (D.cellIndex m))
        nlinarith only [hq, hs]
      have hsq : referenceZeroModeBorderCorrection D r ^ 2 ≤ B₀ ^ 2 := by
        have hh := (sq_le_sq₀ (norm_nonneg (referenceZeroModeBorderCorrection D r)) hB₀.le).mpr
          (hbound r hrc)
        simpa only [Real.norm_eq_abs, sq_abs] using hh
      exact (mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_right hweight (sq_nonneg B₀))
  obtain ⟨hmem, henergy⟩ := referenceRadial_memLp_of_cellwise_sq_bound hgeom.2.1 hP hA.le
    (referenceZeroModeBorderCorrection_measurable hB).aestronglyMeasurable hcell
  exact ⟨hmem, henergy.trans (by linarith)⟩

end ContinuousFlexibility.Statements
