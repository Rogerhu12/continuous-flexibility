import ContinuousFlexibility.Analysis.N04NegativeHeightDensityIdentity
import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialRegularity

/-!
# The nonsingular height numerator in normalized chart atoms

The physical unit map preserves the angular tangent vector.  Consequently
the angular numerator of the Airy density is a polynomial in the two
normalized forward-chart atoms and their first angular derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- The scalar formula used after recovering the radial coordinate and
the angular coordinate from the normalized forward-chart atoms. -/
def n04NegativeHeightUnitNumerator (l d : ℝ) (f g : PolarPoint → ℝ)
    (q : PolarPoint) : ℝ :=
  (1 + angularPartial g q) ^ 2 -
    (l + d * f q) * (d * angularPartial f q) ^ 2

theorem n04NegativeHeight_angularFactor_reconstructed
    {f g : PolarPoint → ℝ} {q : PolarPoint}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) (l d : ℝ) :
    n04NegativeHeightAngularFactor (fun y => (l + d * f y, y.2 + g y)) q =
      n04NegativeHeightUnitNumerator l d f g q := by
  have hd : HasFDerivAt (fun y : PolarPoint => (l + d * f y, y.2 + g y))
      ((d • fderiv ℝ f q).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ + fderiv ℝ g q)) q :=
    ((hf.hasFDerivAt.const_mul d).const_add l).prodMk
      (hasFDerivAt_snd.add hg.hasFDerivAt)
  simp only [n04NegativeHeightAngularFactor, n04NegativeHeightUnitNumerator,
    hd.fderiv, ContinuousLinearMap.prod_apply, add_apply, smul_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, angularPartial]

/-- A radial affine change of variables leaves the angular tangent
vector fixed, so no physical length enters this identity. -/
theorem n04NegativeHeight_angularFactor_affine
    {F : PolarPoint → PolarPoint} (l d : ℝ) (q : PolarPoint)
    (hF : DifferentiableAt ℝ F (l + d * q.1, q.2)) :
    n04NegativeHeightAngularFactor (fun y => F (l + d * y.1, y.2)) q =
      n04NegativeHeightAngularFactor F (l + d * q.1, q.2) := by
  have hP : HasFDerivAt (fun y : PolarPoint => (l + d * y.1, y.2))
      ((d • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
    ((hasFDerivAt_fst.const_mul d).const_add l).prodMk hasFDerivAt_snd
  have hd : HasFDerivAt (fun y : PolarPoint => F (l + d * y.1, y.2))
      ((fderiv ℝ F (l + d * q.1, q.2)).comp
        ((d • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          (ContinuousLinearMap.snd ℝ ℝ ℝ))) q :=
    hF.hasFDerivAt.comp q hP
  simp only [n04NegativeHeightAngularFactor, hd.fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero]

/-- The exact expression on the fixed physical unit strip.  The radial
constant is kept explicit, so the formula also applies before specializing
the canonical left endpoint to zero. -/
theorem n04NegativeHeight_angularFactor_eq_unitAtoms
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (q : PolarPoint)
    (hlen : K.right m - K.left m ≠ 0)
    (hF : DifferentiableAt ℝ (K.chart z m) (physicalUnitPoint K m q)) :
    n04NegativeHeightAngularFactor (K.chart z m) (physicalUnitPoint K m q) =
      n04NegativeHeightUnitNumerator (K.left m) (K.right m - K.left m)
        (atom D T S C L K z m .chartRadial)
        (atom D T S C L K z m .chartAngleDefect) q := by
  let f := atom D T S C L K z m .chartRadial
  let g := atom D T S C L K z m .chartAngleDefect
  have hP : DifferentiableAt ℝ (physicalUnitPoint K m) q := by
    exact ((differentiableAt_const (K.physicalLeft m)).add
      ((differentiableAt_const (K.physicalRight m - K.physicalLeft m)).mul
        differentiableAt_fst)).prodMk differentiableAt_snd
  have hcomp : DifferentiableAt ℝ
      (fun y => K.chart z m (physicalUnitPoint K m y)) q := hF.comp q hP
  have hf : DifferentiableAt ℝ f q := by
    change DifferentiableAt ℝ
      (fun y => ((K.chart z m (physicalUnitPoint K m y)).1 - K.left m) /
        (K.right m - K.left m)) q
    simpa only [div_eq_mul_inv] using
      (hcomp.fst.sub_const (K.left m)).mul_const ((K.right m - K.left m)⁻¹)
  have hg : DifferentiableAt ℝ g q := by
    change DifferentiableAt ℝ
      (fun y => (K.chart z m (physicalUnitPoint K m y)).2 - y.2) q
    exact hcomp.snd.sub differentiableAt_snd
  have he : (fun y => K.chart z m (physicalUnitPoint K m y)) =
      (fun y => (K.left m + (K.right m - K.left m) * f y, y.2 + g y)) := by
    funext y
    apply Prod.ext
    · dsimp only [f, atom]
      field_simp [hlen]
      <;> ring
    · dsimp only [g, atom, physicalUnitPoint]
      ring
  have ha := n04NegativeHeight_angularFactor_affine
    (F := K.chart z m) (K.physicalLeft m)
      (K.physicalRight m - K.physicalLeft m) q hF
  change n04NegativeHeightAngularFactor
    (fun y => K.chart z m (physicalUnitPoint K m y)) q = _ at ha
  rw [he] at ha
  exact ha.symm.trans (n04NegativeHeight_angularFactor_reconstructed hf hg
    (K.left m) (K.right m - K.left m))

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The nonsingular angular factor of the actual negative forward chart,
written entirely in the normalized chart atoms. -/
def negativeHeightAngularFamily (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    Parameter (G.S η) → ℕ → PolarPoint → ℝ := fun z m =>
  n04NegativeHeightUnitNumerator ((G.V η).left m) ((G.V η).right m - (G.V η).left m)
    (G.atomFamily η .chartRadial z m) (G.atomFamily η .chartAngleDefect z m)

/-- The same regularized expression formed from the reference atoms. -/
def negativeHeightAngularRef (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    ℕ → PolarPoint → ℝ := fun m =>
  n04NegativeHeightUnitNumerator ((G.V η).left m) ((G.V η).right m - (G.V η).left m)
    (G.atomRef η .chartRadial m) (G.atomRef η .chartAngleDefect m)

end N04RealizationGauge

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeHeight_angularFactor_eq_unitAtoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeHeight_angularFactor_eq_unitAtoms
