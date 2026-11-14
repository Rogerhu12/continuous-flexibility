import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# Polynomial tests with prescribed critical Hessians

These are actual globally smooth scalar functions. At the chosen point
their gradient is `(0, 1)` and their three Hessian entries are arbitrary.
They will force regularity of coefficient fields from equality of the
actual divergence operators, before any coefficient product rule is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def operatorJetProbe (p : PolarPoint) (a b c : ℝ) (q : PolarPoint) : ℝ :=
  q.2 + (a / 2) * (q.1 - p.1) ^ 2 +
    b * ((q.1 - p.1) * (q.2 - p.2)) + (c / 2) * (q.2 - p.2) ^ 2

def operatorJetProbeRadial (p : PolarPoint) (a b : ℝ) (q : PolarPoint) : ℝ :=
  a * (q.1 - p.1) + b * (q.2 - p.2)

def operatorJetProbeAngular (p : PolarPoint) (b c : ℝ) (q : PolarPoint) : ℝ :=
  1 + b * (q.1 - p.1) + c * (q.2 - p.2)

theorem contDiff_operatorJetProbe (p : PolarPoint) (a b c : ℝ) :
    ContDiff ℝ ∞ (operatorJetProbe p a b c) := by
  exact ((contDiff_snd.add
    (contDiff_const.mul ((contDiff_fst.sub contDiff_const).pow 2))).add
      (contDiff_const.mul
        ((contDiff_fst.sub contDiff_const).mul (contDiff_snd.sub contDiff_const)))).add
    (contDiff_const.mul ((contDiff_snd.sub contDiff_const).pow 2))

/-- The actual gradient of the polynomial test, as two explicit functions. -/
theorem operatorJetProbe_partials (p q : PolarPoint) (a b c : ℝ) :
    radialPartial (operatorJetProbe p a b c) q = operatorJetProbeRadial p a b q ∧
      angularPartial (operatorJetProbe p a b c) q = operatorJetProbeAngular p b c q := by
  have hx : HasFDerivAt (fun z : PolarPoint => z.1 - p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) q := hasFDerivAt_fst.sub_const p.1
  have hy : HasFDerivAt (fun z : PolarPoint => z.2 - p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) q := hasFDerivAt_snd.sub_const p.2
  have hd := (((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).add
    ((hx.pow 2).const_mul (a / 2))).add ((hx.mul hy).const_mul b)).add
      ((hy.pow 2).const_mul (c / 2))
  have he : (((Prod.snd : PolarPoint → ℝ) +
      (fun y : PolarPoint => a / 2 * (y.1 - p.1) ^ 2)) +
      (fun y : PolarPoint => b *
        (((fun z : PolarPoint => z.1 - p.1) * (fun z : PolarPoint => z.2 - p.2)) y))) +
      (fun y : PolarPoint => c / 2 * (y.2 - p.2) ^ 2) = operatorJetProbe p a b c := by
    funext y
    simp only [Pi.add_apply, Pi.mul_apply, operatorJetProbe]
  rw [he] at hd
  constructor
  · change fderiv ℝ (operatorJetProbe p a b c) q (1, 0) = _
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      operatorJetProbeRadial]
    norm_num
    <;> ring
  · change fderiv ℝ (operatorJetProbe p a b c) q (0, 1) = _
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      operatorJetProbeAngular]
    norm_num
    <;> ring

theorem hasFDerivAt_operatorJetProbeRadial (p q : PolarPoint) (a b : ℝ) :
    HasFDerivAt (operatorJetProbeRadial p a b)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ +
        b • ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
  exact ((hasFDerivAt_fst.sub_const p.1).const_mul a).add
    ((hasFDerivAt_snd.sub_const p.2).const_mul b)

theorem hasFDerivAt_operatorJetProbeAngular (p q : PolarPoint) (b c : ℝ) :
    HasFDerivAt (operatorJetProbeAngular p b c)
      (b • ContinuousLinearMap.fst ℝ ℝ ℝ +
        c • ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
  exact (((hasFDerivAt_fst.sub_const p.1).const_mul b).const_add 1).add
    ((hasFDerivAt_snd.sub_const p.2).const_mul c)

theorem operatorJetProbeRadial_partials (p q : PolarPoint) (a b : ℝ) :
    radialPartial (operatorJetProbeRadial p a b) q = a ∧
      angularPartial (operatorJetProbeRadial p a b) q = b := by
  simp only [radialPartial, angularPartial,
    (hasFDerivAt_operatorJetProbeRadial p q a b).fderiv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    mul_one, mul_zero, add_zero, zero_add, and_self]

theorem operatorJetProbeAngular_partials (p q : PolarPoint) (b c : ℝ) :
    radialPartial (operatorJetProbeAngular p b c) q = b ∧
      angularPartial (operatorJetProbeAngular p b c) q = c := by
  simp only [radialPartial, angularPartial,
    (hasFDerivAt_operatorJetProbeAngular p q b c).fderiv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    mul_one, mul_zero, add_zero, zero_add, and_self]

/-- At the center, equality of actual operators sees the freely prescribed
three Hessian entries. This formula is only used for regular coefficients. -/
theorem divergenceOperator_operatorJetProbe
    {B : SymmetricCoefficients} {p : PolarPoint}
    (ha : DifferentiableAt ℝ B.a p) (hb : DifferentiableAt ℝ B.b p)
    (hc : DifferentiableAt ℝ B.c p) (a b c : ℝ) :
    divergenceOperator B (operatorJetProbe p a b c) p =
      radialPartial B.b p + angularPartial B.c p +
        B.a p * a + 2 * B.b p * b + B.c p * c := by
  have hr : radialPartial (operatorJetProbe p a b c) = operatorJetProbeRadial p a b :=
    funext fun q => (operatorJetProbe_partials p q a b c).1
  have ht : angularPartial (operatorJetProbe p a b c) = operatorJetProbeAngular p b c :=
    funext fun q => (operatorJetProbe_partials p q a b c).2
  have hrd := (hasFDerivAt_operatorJetProbeRadial p p a b).differentiableAt
  have htd := (hasFDerivAt_operatorJetProbeAngular p p b c).differentiableAt
  have har : DifferentiableAt ℝ (fun y => B.a y * operatorJetProbeRadial p a b y) p :=
    ha.mul hrd
  have hbr : DifferentiableAt ℝ (fun y => B.b y * operatorJetProbeRadial p a b y) p :=
    hb.mul hrd
  have hbt : DifferentiableAt ℝ (fun y => B.b y * operatorJetProbeAngular p b c y) p :=
    hb.mul htd
  have hct : DifferentiableAt ℝ (fun y => B.c y * operatorJetProbeAngular p b c y) p :=
    hc.mul htd
  rw [divergenceOperator, hr, ht,
    radialPartial_add har hbt, angularPartial_add hbr hct,
    radialPartial_mul ha hrd, radialPartial_mul hb htd,
    angularPartial_mul hb hrd, angularPartial_mul hc htd,
    (operatorJetProbeRadial_partials p p a b).1,
    (operatorJetProbeRadial_partials p p a b).2,
    (operatorJetProbeAngular_partials p p b c).1,
    (operatorJetProbeAngular_partials p p b c).2]
  simp only [operatorJetProbeRadial, operatorJetProbeAngular,
    sub_self, mul_zero, zero_add, add_zero, mul_one]
  ring

end ContinuousFlexibility.Analysis
