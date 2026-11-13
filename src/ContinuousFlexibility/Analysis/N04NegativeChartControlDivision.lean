import ContinuousFlexibility.Analysis.N04RealizationLeadStart
import ContinuousFlexibility.Analysis.N01cComponentOpticalGeometry
import ContinuousFlexibility.Analysis.N01OpticalRootDivision
import ContinuousFlexibility.Analysis.SmoothDivisionBounds

/-!
# Dividing the actual optical control by its root coordinate

The actual control factor is globally smooth: its numerator vanishes
near the only apparent singularity at radius zero. Its strict component
support supplies the true zero at either turning point. S05 therefore
selects one smooth root division, with one extra radial derivative and
no inverse collar width. These are the affine state-dependent parts of
the full-half normalized optical square.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n04NegativeChart_controlOpticalFactor_support
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (m : ℕ) :
    Function.support (controlOpticalFactor C m) ⊆ Ioo (C.left m) (C.right m) := by
  intro r hr
  have hd : deriv (C.control m) r ≠ 0 := by
    change deriv (C.control m) r / r ≠ 0 at hr
    exact (div_ne_zero_iff.mp hr).1
  exact (hC.2.2.2.2.2.1 m).2.2
    (tsupport_deriv_subset (subset_tsupport (deriv (C.control m)) hd))

theorem n04NegativeChart_controlOpticalFactor_contDiff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    ContDiff ℝ ∞ (controlOpticalFactor C m) := by
  have hd : ContDiff ℝ ∞ (deriv (C.control m)) :=
    (contDiff_infty_iff_deriv.mp (hC.2.2.2.2.2.1 m).1).2
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    have hnot : (0 : ℝ) ∉ tsupport (deriv (C.control m)) := by
      intro h
      have hleft := ((hC.2.2.2.2.2.1 m).2.2 (tsupport_deriv_subset h)).1
      exact (not_lt_of_ge (hD.1.trans (hC.1 m).1).le) hleft
    have he : deriv (C.control m) =ᶠ[𝓝 (0 : ℝ)] (0 : ℝ → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have he' : controlOpticalFactor C m =ᶠ[𝓝 (0 : ℝ)] (0 : ℝ → ℝ) := by
      filter_upwards [he] with x hx
      change deriv (C.control m) x / x = 0
      rw [hx, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he'
  · exact hd.contDiffAt.div contDiffAt_id hr

/-- The two inward orientations preserve every absolute scalar jet. -/
theorem n04NegativeChart_abs_iteratedDeriv_inward
    (f : ℝ → ℝ) (l h : ℝ) (side : Bool) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (fun x => f (inwardComponentPoint l h side x)) t| =
      |iteratedDeriv n f (inwardComponentPoint l h side t)| := by
  cases side with
  | false =>
    simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte,
      iteratedDeriv_comp_const_add]
  | true =>
    simp only [inwardComponentPoint, ↓reduceIte, iteratedDeriv_comp_const_sub,
      smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- One smooth division of the actual control factor works at both ends
and at every order. Its zeroth value is also zero, since the original
control is supported strictly inside its component. -/
theorem negativeControlDivision_material_jets :
    ∃ g : ℕ → Bool → ℝ → ℝ,
      (∀ m side, ContDiff ℝ ∞ (g m side)) ∧
      (∀ m side, g m side 0 = 0) ∧
      (∀ m side t, controlOpticalFactor W.C m
        (inwardComponentPoint (W.C.left m) (W.C.right m) side t) = t * g m side t) ∧
      ∀ n : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m side t,
        t ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) →
          |iteratedDeriv n (g m side) t| ≤ B * W.T.E0 (W.T.sample (W.C.cell m)) ^ A := by
  classical
  have h01 := W.through03.1.1
  have hA : N01PartA W.D W.T W.S W.C :=
    ⟨h01.1, h01.2.2.1, h01.2.2.2.1, h01.2.2.2.2.1, h01.2.2.2.2.2.1⟩
  have hC : controlGeometryConditions W.D W.S W.C := hA.2.2.1
  have hD : RadialProfileGeometry W.D := hA.1.1.choose_spec.1
  let F (m : ℕ) (side : Bool) (t : ℝ) : ℝ :=
    controlOpticalFactor W.C m
      (inwardComponentPoint (W.C.left m) (W.C.right m) side t)
  have hF (m : ℕ) (side : Bool) : ContDiff ℝ ∞ (F m side) := by
    have hc := n04NegativeChart_controlOpticalFactor_contDiff hD hC m
    cases side
    · exact hc.comp (contDiff_const.add contDiff_id)
    · exact hc.comp (contDiff_const.sub contDiff_id)
  have hFs (m : ℕ) (side : Bool) :
      Function.support (F m side) ⊆ Ioo (0 : ℝ) (W.C.right m - W.C.left m) := by
    intro t ht
    have hr := n04NegativeChart_controlOpticalFactor_support hC m ht
    cases side <;> simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte] at hr
      <;> constructor <;> linarith only [hr.1, hr.2]
  have hzero (m : ℕ) (side : Bool) (n : ℕ) : iteratedDeriv n (F m side) 0 = 0 :=
    iteratedDeriv_zero_off_open_interval (hF m side) (hFs m side) n
      (fun h => lt_irrefl (0 : ℝ) h.1)
  have hdivision (m : ℕ) (side : Bool) : ∃ g : ℝ → ℝ,
      ContDiff ℝ ∞ g ∧ g 0 = 0 ∧ ∀ t, F m side t = t * g t := by
    obtain ⟨g, hg, hg0, hfactor⟩ := exists_smooth_division_at_zero
      (hF m side) (by simpa only [iteratedDeriv_zero] using hzero m side 0)
    refine ⟨g, hg, ?_, hfactor⟩
    rw [hg0]
    simpa only [iteratedDeriv_one] using hzero m side 1
  choose g hg hg0 hfactor using hdivision
  refine ⟨g, hg, hg0, hfactor, ?_⟩
  intro n
  obtain ⟨B, A, hB, hAp, hb⟩ := controlOpticalFactor_iteratedDeriv_sample_bound
    W.hT hA (fun r _ => W.floor r) (n + 1)
  have hglobal (m : ℕ) (r : ℝ) :
      |iteratedDeriv (n + 1) (controlOpticalFactor W.C m) r| ≤
        B * W.T.E0 (W.T.sample (W.C.cell m)) ^ A := by
    by_cases hr : r ∈ Ioo (W.C.left m) (W.C.right m)
    · exact hb m r hr
    · rw [iteratedDeriv_zero_off_open_interval
        (n04NegativeChart_controlOpticalFactor_contDiff hD hC m)
        (n04NegativeChart_controlOpticalFactor_support hC m) (n + 1) hr, abs_zero]
      exact mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (W.floor _)) _)
  refine ⟨B, A, hB, hAp, fun m side t ht => ?_⟩
  apply norm_iteratedDeriv_smoothDivisionFactor_le
    (hF m side) (hg m side) (hfactor m side) n
    (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (W.floor _)) _)) ht
  intro y _hy
  change |iteratedDeriv (n + 1) (fun x => controlOpticalFactor W.C m
    (inwardComponentPoint (W.C.left m) (W.C.right m) side x)) y| ≤ _
  rw [n04NegativeChart_abs_iteratedDeriv_inward]
  exact hglobal m _

end N04RealizationStart

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeControlDivision_material_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeControlDivision_material_jets
