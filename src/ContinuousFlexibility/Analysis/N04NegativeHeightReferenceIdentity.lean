import ContinuousFlexibility.Analysis.N04NegativeHeightGaugeIdentity
import ContinuousFlexibility.Analysis.N04NegativeHeightReferenceData
import ContinuousFlexibility.Analysis.ActualReferenceNegativeRadialFields
import ContinuousFlexibility.Analysis.EffectiveRadialCoefficient

/-!
# Reference normalization of the negative-height factors

The retained reference chart preserves angle and is radial in its first
coordinate. Thus its nonsingular angular numerator is exactly one. The
actual density identity then normalizes the coefficient--Jacobian--height
product to one, using the same reference height as the current atoms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

private theorem height_referenceDensity_scalar {a J h : ℝ}
    (ha : 0 ≤ a) (hJ : 0 ≤ J) (hh : 0 < h)
    (he : h⁻¹ = Real.sqrt (a * J)) : a * J * h ^ 2 = 1 := by
  have hsq := congrArg (fun x : ℝ => x ^ 2) he
  rw [Real.sq_sqrt (mul_nonneg ha hJ)] at hsq
  rw [← hsq, ← mul_pow, inv_mul_cancel₀ hh.ne', one_pow]

private theorem height_referenceChartShape_of_eq
    {F H : PolarPoint → PolarPoint} (he : F = H) (p : PolarPoint)
    (hH : H p = ((H (p.1, 0)).1, p.2)) :
    F p = ((F (p.1, 0)).1, p.2) :=
  he.symm ▸ hH

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem negative_referenceChart_shape (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    (G.V η).chart (G.ref η) m (physicalUnitPoint (G.V η) m q) =
      (((G.V η).chart (G.ref η) m ((physicalUnitPoint (G.V η) m q).1, 0)).1, q.2) := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  have hr := n04Coordinates_actual_reference_negative_radial_fields
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ j.1 j.2
  have hp := G.heightRadial_physicalUnitPoint_mem η m j hi hq
  have he : (G.V η).chart (G.ref η) m =
      (G.W.A G.X.e₀).chart (G.W.C.referenceState, 0) (G.negativeIndex j) :=
    hf.2.2.2.2.2.2.2.1
  exact height_referenceChartShape_of_eq he (physicalUnitPoint (G.V η) m q)
    (hr.2.2.1 _ hp)

theorem negative_chartRadialRef_radial (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    G.atomRef η .chartRadial m q = G.atomRef η .chartRadial m (q.1, 0) := by
  have hfirst := congrArg Prod.fst (G.negative_referenceChart_shape η m hm q hq)
  exact congrArg
    (fun r : ℝ => (r - (G.V η).left m) / ((G.V η).right m - (G.V η).left m)) hfirst

theorem negative_chartAngleRef_zero (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    G.atomRef η .chartAngleDefect m q = 0 := by
  have h := congrArg (fun p : PolarPoint => p.2 - q.2)
    (G.negative_referenceChart_shape η m hm q hq)
  exact h.trans (sub_self q.2)

/-- Reference chart atoms have zero angular derivative at every point
of the open unit strip; their total extensions play no role. -/
theorem negative_chartRef_angularPartial_zero (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    angularPartial (G.atomRef η .chartRadial m) q = 0 ∧
      angularPartial (G.atomRef η .chartAngleDefect m) q = 0 := by
  constructor
  · exact angularPartial_eq_zero_of_constant_slice
      (r := q.1) (θ := q.2) (c := G.atomRef η .chartRadial m (q.1, 0))
      (fun θ => G.negative_chartRadialRef_radial η m hm (q.1, θ)
        ⟨hq.1, mem_univ _⟩)
  · exact angularPartial_eq_zero_of_constant_slice
      (r := q.1) (θ := q.2) (c := 0)
      (fun θ => G.negative_chartAngleRef_zero η m hm (q.1, θ)
        ⟨hq.1, mem_univ _⟩)

theorem negativeHeightAngularRef_one (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    G.negativeHeightAngularRef η m q = 1 := by
  have hd := G.negative_chartRef_angularPartial_zero η m hm q hq
  simp only [negativeHeightAngularRef, n04NegativeHeightUnitNumerator,
    hd.1, hd.2, add_zero, one_pow, mul_zero, zero_pow two_ne_zero, sub_zero]

theorem negativeHeightAngularFamily_zero :
    G.negativeHeightAngularFamily η 0 = G.negativeHeightAngularRef η :=
  congrArg₂
    (fun R A : ℕ → PolarPoint → ℝ => fun m =>
      n04NegativeHeightUnitNumerator ((G.V η).left m)
        ((G.V η).right m - (G.V η).left m) (R m) (A m))
    (G.height_atomFamily_zero η .chartRadial)
    (G.height_atomFamily_zero η .chartAngleDefect)

theorem negative_heightRef_pos (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    0 < G.atomRef η .height m q := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  have hr := n04Coordinates_actual_reference_negative_radial_fields
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ j.1 j.2
  have he : (G.V η).height (G.ref η) m =
      (G.W.A G.X.e₀).height (G.W.C.referenceState, 0) (G.negativeIndex j) :=
    hf.2.2.2.2.2.2.2.2.2.1
  exact (hr.2.2.2.2 _ (G.heightRadial_physicalUnitPoint_mem η m j hi hq)).trans_eq
    (congrFun he (physicalUnitPoint (G.V η) m q)).symm

/-- The second nonsingular factor is also normalized to one at the
reference state.  Its fixed height multiplier has its own reference jets. -/
theorem negativeHeight_referenceDensity (m : ℕ) (hm : G.Neg η m)
    (q : PolarPoint) (hq : q ∈ unitStrip) :
    G.physicalRadialRef η m q * G.atomRef η .jacobian m q *
      G.atomRef η .height m q ^ 2 = 1 := by
  have hz := G.height_zero_mem_sector η
  have hformula := G.negativeHeight_sqrt_formula η 0 hz m hm q hq
  have hN : G.negativeHeightAngularFamily η 0 m q = 1 :=
    (congrFun (congrFun (G.negativeHeightAngularFamily_zero η) m) q).trans
      (G.negativeHeightAngularRef_one η m hm q hq)
  have haeq : G.physicalRadialFamily η 0 m q = G.physicalRadialRef η m q :=
    congrFun (G.physicalRadialFamily_zero η m) q
  have hJeq : G.atomFamily η .jacobian 0 m q = G.atomRef η .jacobian m q :=
    congrFun (congrFun (G.height_atomFamily_zero η .jacobian) m) q
  have hheq : G.atomFamily η .heightInverse 0 m q = G.atomRef η .heightInverse m q :=
    congrFun (congrFun (G.height_atomFamily_zero η .heightInverse) m) q
  have hroot : G.atomRef η .heightInverse m q =
      Real.sqrt (G.physicalRadialRef η m q * G.atomRef η .jacobian m q) :=
    hheq.symm.trans (hformula.2.2.trans
      ((congrArg₂ (fun d n : ℝ => Real.sqrt (d / n))
        (congrArg₂ (fun x y : ℝ => x * y) haeq hJeq) hN).trans
          (congrArg Real.sqrt (div_one _))))
  have ha : 0 ≤ G.physicalRadialRef η m q :=
    (G.physicalRadial_pos η 0 hz m hm hq).le.trans_eq haeq
  have hJ : 0 ≤ G.atomRef η .jacobian m q := abs_nonneg _
  exact height_referenceDensity_scalar ha hJ (G.negative_heightRef_pos η m hm q hq) hroot

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeight_referenceDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeight_referenceDensity
