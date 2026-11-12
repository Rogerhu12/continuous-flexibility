import ContinuousFlexibility.Analysis.N01aOpticalProfile
import ContinuousFlexibility.Analysis.MaterialSampleRadialPolynomial
import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
import ContinuousFlexibility.Analysis.SmoothDivisionBounds

/-!
# Material jets of the actual normalized optical root division

The reference optical radicand is smoothly extended without changing
its germ anywhere on the closed component. S05 divides that same
radicand, in either inward orientation. Only derivatives on the actual
component enter the bounds, so no derivatives of the auxiliary extension
and no arbitrary extension width enter the material constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- All ordinary radicand jets retain the actual host sample. -/
theorem n01aOpticalRadicand_component_material_jets
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ l h j,
      NegativeRadialComponent D l h → Ioo l h ⊆ D.cells j →
      ∀ r ∈ Icc l h, |iteratedDeriv n (n01aOpticalRadicand D.w) r| ≤
        K * T.E0 (T.sample j) ^ P := by
  obtain ⟨B, hB, hb⟩ := n01aOpticalRadicand_component_jets hD n
  obtain ⟨K, P, hK, hP, hpoly⟩ :=
    materialSample_radialE_power_bound hT hD (R := B) hB.le
  refine ⟨B * K, P, mul_pos hB hK, hP, ?_⟩
  intro l h j hcomp hhost r hr
  exact (hb l h j hcomp hhost r hr).trans
    ((mul_le_mul_of_nonneg_left (hpoly j) hB.le).trans_eq (by ring))

private theorem opticalRadicand_global_extension
    {D : ReferenceData} (hD : RadialProfileGeometry D) {l h : ℝ}
    (hcomp : NegativeRadialComponent D l h) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧
      ∀ r ∈ Icc l h, F =ᶠ[𝓝 r] n01aOpticalRadicand D.w := by
  let η : ℝ := min (l - D.a) (D.b - h) / 4
  have hη : 0 < η := div_pos
    (lt_min (sub_pos.mpr hcomp.1) (sub_pos.mpr hcomp.2.2.1)) (by norm_num)
  have hηL : 4 * η ≤ l - D.a := by
    dsimp only [η]
    linarith only [min_le_left (l - D.a) (D.b - h)]
  have hηR : 4 * η ≤ D.b - h := by
    dsimp only [η]
    linarith only [min_le_right (l - D.a) (D.b - h)]
  have hab : l - η ≤ h + η := by linarith only [hcomp.2.1, hη]
  let χ := circleFlowSmoothTimeClamp (l - η) (h + η) η hab hη
  have hχ : ContDiff ℝ ∞ χ := contDiff_circleFlowSmoothTimeClamp hab hη
  have hχmem (r : ℝ) : χ r ∈ radialCore D := by
    have hr := circleFlowSmoothTimeClamp_mem hab hη r
    change l - η - η < χ r ∧ χ r < h + η + η at hr
    constructor <;> linarith only [hr.1, hr.2, hηL, hηR, hη]
  let F : ℝ → ℝ := fun r => n01aOpticalRadicand D.w (χ r)
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro r
    have hq := contDiffAt_n01aOpticalRadicand hD.2.2.1.1
      (hD.1.trans (hχmem r).1).ne' (hD.2.2.2.2.1 _ (hχmem r)).ne'
    exact hq.comp r hχ.contDiffAt
  refine ⟨F, hF, ?_⟩
  intro r hr
  have hr' : r ∈ Ioo (l - η) (h + η) := by
    constructor <;> linarith only [hr.1, hr.2, hη]
  filter_upwards [isOpen_Ioo.mem_nhds hr'] with x hx
  change n01aOpticalRadicand D.w (χ x) = n01aOpticalRadicand D.w x
  exact congrArg (n01aOpticalRadicand D.w)
    (circleFlowSmoothTimeClamp_eq hab hη ⟨hx.1.le, hx.2.le⟩)

def inwardComponentPoint (l h : ℝ) (rightEnd : Bool) (t : ℝ) : ℝ :=
  if rightEnd then h - t else l + t

theorem inwardComponentPoint_mem {l h t : ℝ} (rightEnd : Bool)
    (ht : t ∈ Icc (0 : ℝ) (h - l)) :
    inwardComponentPoint l h rightEnd t ∈ Icc l h := by
  cases rightEnd <;> simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
    <;> constructor <;> linarith only [ht.1, ht.2]

private theorem abs_iteratedDeriv_inwardComponentPoint
    (F : ℝ → ℝ) (l h : ℝ) (rightEnd : Bool) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (fun x => F (inwardComponentPoint l h rightEnd x)) t| =
      |iteratedDeriv n F (inwardComponentPoint l h rightEnd t)| := by
  cases rightEnd with
  | false =>
    simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte,
      iteratedDeriv_comp_const_add]
  | true =>
    simp only [inwardComponentPoint, ↓reduceIte, iteratedDeriv_comp_const_sub,
      smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- S05's actual normalized root factor has all-order material bounds,
uniform in the component and its genuine host. The constants precede
both endpoint choices; the factor is chosen before requesting an order. -/
theorem exists_normalizedOpticalRootDivision_material_family
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ A P : ℕ → ℝ, (∀ n, 0 < A n) ∧ (∀ n, 0 ≤ P n) ∧
      ∀ l h : ℝ, ∀ j : ℕ, NegativeRadialComponent D l h →
      Ioo l h ⊆ D.cells j → ∀ rightEnd : Bool, ∃ g : ℝ → ℝ,
        ContDiff ℝ ∞ g ∧
        (∀ t ∈ Icc (0 : ℝ) (h - l),
          n01aOpticalRadicand D.w (inwardComponentPoint l h rightEnd t) = t * g t) ∧
        ∀ n t, t ∈ Icc (0 : ℝ) (h - l) →
          |iteratedDeriv n g t| ≤ A n * T.E0 (T.sample j) ^ P n := by
  classical
  choose A P hA hP hb using fun n =>
    n01aOpticalRadicand_component_material_jets hD hT (n + 1)
  refine ⟨A, P, hA, hP, ?_⟩
  intro l h j hcomp hhost rightEnd
  obtain ⟨F, hF, hFgerm⟩ := opticalRadicand_global_extension hD.choose_spec.1 hcomp
  let f : ℝ → ℝ := fun t => F (inwardComponentPoint l h rightEnd t)
  have hf : ContDiff ℝ ∞ f := by
    cases rightEnd with
    | false => exact hF.comp (contDiff_const.add contDiff_id)
    | true => exact hF.comp (contDiff_const.sub contDiff_id)
  have hfzero : f 0 = 0 := by
    cases rightEnd with
    | false =>
      change F (l + 0) = 0
      rw [add_zero, (hFgerm l ⟨le_rfl, hcomp.2.1.le⟩).self_of_nhds]
      exact n01aOpticalRadicand_zero hcomp.2.2.2.1
    | true =>
      change F (h - 0) = 0
      rw [sub_zero, (hFgerm h ⟨hcomp.2.1.le, le_rfl⟩).self_of_nhds]
      exact n01aOpticalRadicand_zero hcomp.2.2.2.2.1
  obtain ⟨g, hg, hg0, hfactor⟩ := exists_smooth_division_at_zero hf hfzero
  refine ⟨g, hg, ?_, ?_⟩
  · intro t ht
    exact ((hFgerm _ (inwardComponentPoint_mem rightEnd ht)).self_of_nhds).symm.trans
      (hfactor t)
  · intro n t ht
    have hE : 0 < T.E0 (T.sample j) :=
      (hT.2.1 _ (materialSample_mem_interval hD hT j)).2.2.1
    apply norm_iteratedDeriv_smoothDivisionFactor_le hf hg hfactor n
      (mul_nonneg (hA n).le (Real.rpow_nonneg hE.le _)) ht
    intro y hy
    have hymem := inwardComponentPoint_mem rightEnd hy
    calc
      |iteratedDeriv (n + 1) f y| =
          |iteratedDeriv (n + 1) F (inwardComponentPoint l h rightEnd y)| :=
        abs_iteratedDeriv_inwardComponentPoint F l h rightEnd (n + 1) y
      _ = |iteratedDeriv (n + 1) (n01aOpticalRadicand D.w)
          (inwardComponentPoint l h rightEnd y)| := by
        rw [(hFgerm _ hymem).iteratedDeriv_eq (n + 1)]
      _ ≤ A n * T.E0 (T.sample j) ^ P n := hb n l h j hcomp hhost _ hymem

end ContinuousFlexibility.Analysis
