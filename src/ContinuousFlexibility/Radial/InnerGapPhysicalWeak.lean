import ContinuousFlexibility.Radial.InnerGapPotentialLift
import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph

/-!
# Positive-gap realization in the common physical weak graph

The potential class is the square of the actual square-root multiplier.
Thus the same arbitrary-source Dirichlet inverse satisfies the local
weak graph used for the finite chain, with one derivative for all tests.
The converse is included, so the graph also determines that inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerGapPotentialClass (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (u : RadialModeL2 D) :
    InnerRadialPotentialClass D j a b u
      (innerGapPotentialMultiplier D hw hpos j
        (innerGapPotentialMultiplier D hw hpos j u)) :=
  innerGapPotentialMultiplier_square_ae D hw hpos hslope j u

/-- The signed-potential relation uniquely determines the actual L²
potential coordinate on a positive piece. -/
theorem innerGapPotentialClass_eq (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (j : ℝ) {u v : RadialModeL2 D}
    (hv : InnerRadialPotentialClass D j a b u v) :
    v = innerGapPotentialMultiplier D hw hpos j
      (innerGapPotentialMultiplier D hw hpos j u) := by
  apply Lp.ext
  exact hv.trans (innerGapPotentialMultiplier_square_ae D hw hpos hslope j u).symm

/-- The coercive closed form is precisely the actual zero-endpoint
weak equation used on the pieces of the finite chain. -/
theorem innerGapFormGraph_iff_weakResidual (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (u f : RadialModeL2 D) :
    InnerGapFormGraph D j a b u f ↔
      ∃ d v : RadialModeL2 D, (u, d) ∈ innerRadialH1Zero D a b ∧
        InnerRadialPotentialClass D j a b u v ∧
        ∀ r ∈ innerRadialH1Zero D a b,
          innerRadialWeakResidual D (u, d) v f 0 0 r = 0 := by
  rw [innerGapFormGraph_iff_radialH1 D hw hpos j u f]
  constructor
  · rintro ⟨d, hd, hform⟩
    refine ⟨d, innerGapPotentialMultiplier D hw hpos j
      (innerGapPotentialMultiplier D hw hpos j u), hd,
      innerGapPotentialClass D hw hpos hslope j u, ?_⟩
    intro r hr
    have he := hform r hr
    rw [innerRadialWeakResidual_apply]
    rw [innerGapPotentialMultiplier_square_inner]
    simp only [zero_mul, add_zero]
    linarith
  · rintro ⟨d, v, hd, hv, hweak⟩
    refine ⟨d, hd, ?_⟩
    intro r hr
    have he := hweak r hr
    rw [innerRadialWeakResidual_apply] at he
    rw [innerGapPotentialClass_eq D hw hpos hslope j hv,
      innerGapPotentialMultiplier_square_inner] at he
    simp only [zero_mul, add_zero] at he
    linarith

/-- The same constructed inverse solves the physical piece equation
for every L² source, with no source regularity assumption. -/
theorem innerGapDirichletInverse_weakResidual (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j s : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (f : RadialModeL2 D) :
    ∃ d v : RadialModeL2 D,
      (innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f, d) ∈
        innerRadialH1Zero D a b ∧
      InnerRadialPotentialClass D j a b
        (innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f) v ∧
      ∀ r ∈ innerRadialH1Zero D a b,
        innerRadialWeakResidual D
          (innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f, d)
          v f 0 0 r = 0 :=
  (innerGapFormGraph_iff_weakResidual D hw hpos
    (fun r hr => hs.le.trans (hslope r hr)) j _ f).mp
      (innerGapDirichletInverse_graph D hw hab ha hj hs hcore hpos hslope f)

/-- Conversely every field in the same physical zero-endpoint weak
graph is the output of that very Dirichlet inverse. -/
theorem innerGapDirichletInverse_eq_of_weakResidual (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j s : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (u d v f : RadialModeL2 D)
    (hd : (u, d) ∈ innerRadialH1Zero D a b)
    (hv : InnerRadialPotentialClass D j a b u v)
    (he : ∀ r ∈ innerRadialH1Zero D a b,
      innerRadialWeakResidual D (u, d) v f 0 0 r = 0) :
    innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f = u :=
  (innerGapDirichletInverse_graph_iff D hw hab ha hj hs hcore hpos hslope u f).mp
    ((innerGapFormGraph_iff_weakResidual D hw hpos
      (fun r hr => hs.le.trans (hslope r hr)) j u f).mpr ⟨d, v, hd, hv, he⟩)

end ContinuousFlexibility.Radial
