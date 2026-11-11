import ContinuousFlexibility.Radial.InnerGapDirichlet

/-!
# Support and physical tests for the positive-gap inverse

The closed Dirichlet domain remains supported in its actual interval.
Restriction to the complement is a bounded L² map, so this support fact
passes from the test core to its closure. The form graph also exposes
the physical smooth tests and both energy coordinates for subsequent
weak conormal-flux and finite-piece gluing arguments.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

def innerGapOutsideRestriction (D : ReferenceData) (a b : ℝ) :
    RadialModeL2 D →L[ℝ] Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo a b)ᶜ) :=
  Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (by simpa only [one_smul] using
      (Measure.restrict_le_self : (radialHilbertMeasure D).restrict (Ioo a b)ᶜ ≤
        radialHilbertMeasure D))

theorem innerGapOutsideRestriction_ae (D : ReferenceData) (a b : ℝ) (u : RadialModeL2 D) :
    innerGapOutsideRestriction D a b u =ᵐ[(radialHilbertMeasure D).restrict (Ioo a b)ᶜ] u := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul
    (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (by simpa only [one_smul] using
      (Measure.restrict_le_self : (radialHilbertMeasure D).restrict (Ioo a b)ᶜ ≤
        radialHilbertMeasure D)) u

theorem innerGapOutsideRestriction_eq_zero_iff (D : ReferenceData) (a b : ℝ)
    (u : RadialModeL2 D) :
    innerGapOutsideRestriction D a b u = 0 ↔
      ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b → u r = 0 := by
  constructor
  · intro h
    have hz := Lp.eq_zero_iff_ae_eq_zero.mp h
    exact (ae_restrict_iff' measurableSet_Ioo.compl).mp
      ((innerGapOutsideRestriction_ae D a b u).symm.trans hz)
  · intro h
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    exact (innerGapOutsideRestriction_ae D a b u).trans
      ((ae_restrict_iff' measurableSet_Ioo.compl).mpr h)

theorem innerGapFormSpace_support (D : ReferenceData) (j a b : ℝ)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b → q.fst r = 0 := by
  let R := innerGapOutsideRestriction D a b
  have hf : Continuous (fun q : InnerGapEnergyTriple D => R q.fst) :=
    R.continuous.comp (WithLp.fstL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hclosed : IsClosed {q : InnerGapEnergyTriple D | R q.fst = 0} :=
    isClosed_eq hf continuous_const
  have hc : InnerGapEnergyCore D j a b ⊆ {q : InnerGapEnergyTriple D | R q.fst = 0} := by
    rintro p ⟨u, _, _, _, hu, _, _⟩
    apply (innerGapOutsideRestriction_eq_zero_iff D a b p.fst).mpr
    filter_upwards [hu] with r hr
    intro hout
    rw [hr, indicator_of_notMem hout]
  have hz : R q.fst = 0 :=
    (closure_minimal hc hclosed) ((mem_innerGapFormSpace D j a b q).mp hq)
  exact (innerGapOutsideRestriction_eq_zero_iff D a b q.fst).mp hz

theorem innerGapFormGraph_support {D : ReferenceData} {j a b : ℝ}
    {u f : RadialModeL2 D} (h : InnerGapFormGraph D j a b u f) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b → u r = 0 := by
  obtain ⟨q, hq, hvalue, _⟩ := (innerGapFormGraph_iff D j a b u f).mp h
  have hs := innerGapFormSpace_support D j a b q hq
  rwa [hvalue] at hs

theorem innerGapDirichletInverse_support (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) (f : RadialModeL2 D) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b →
      innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f r = 0 :=
  innerGapFormGraph_support
    (innerGapDirichletInverse_graph D hw hab ha hj hs hcore hpos hslope f)

/-- The same closed-domain witness supplies the weak equation against
every actual smooth compactly supported radial test. -/
theorem innerGapFormGraph_tests (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) {u f : RadialModeL2 D}
    (h : InnerGapFormGraph D j a b u f) :
    ∃ q : InnerGapEnergyTriple D, q ∈ innerGapFormSpace D j a b ∧ q.fst = u ∧
      ∀ φ : ℝ → ℝ, ∀ hφ : ContDiff ℝ ∞ φ,
        HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
        ⟪f, innerRadialIntervalToLp D hw.continuous ha hcore
          (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
          φ hφ.continuous.continuousOn⟫_ℝ =
          ⟪q.snd.fst, (innerGapEnergyPair D hw ha hcore hpos j φ hφ).fst⟫_ℝ +
            ⟪q.snd.snd, (innerGapEnergyPair D hw ha hcore hpos j φ hφ).snd⟫_ℝ := by
  obtain ⟨q, hq, hvalue, hform⟩ := (innerGapFormGraph_iff D j a b u f).mp h
  refine ⟨q, hq, hvalue, ?_⟩
  intro φ hφ hcφ hsφ
  let test : InnerGapEnergyTriple D := WithLp.toLp 2
    (innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) φ hφ.continuous.continuousOn,
      innerGapEnergyPair D hw ha hcore hpos j φ hφ)
  have ht : test ∈ innerGapFormSpace D j a b :=
    (mem_innerGapFormSpace D j a b test).mpr
      (subset_closure (innerGapEnergyTriple_mem_core D hw ha hcore hpos j φ hφ hcφ hsφ))
  have he := hform test ht
  simpa only [test, WithLp.toLp_fst, WithLp.toLp_snd, WithLp.prod_inner_apply,
    WithLp.ofLp_fst, WithLp.ofLp_snd] using he

end ContinuousFlexibility.Radial
