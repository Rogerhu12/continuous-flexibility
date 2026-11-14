module

public import ContinuousFlexibility.Analysis.N07bCanonicalSourceRecursion
public import ContinuousFlexibility.Analysis.N07bMaterialCoordinateMeasure
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Actual material-coordinate calculus for angular source coefficients

One application of the actual inverse angular derivative to a weighted
material jet produces three terms. Their coefficients depend on the
material data, chart, weight, and preceding coefficient, but never on the
function whose material jets are being expanded. The same formula holds
for an arbitrary finite sum, providing the exact calculus step needed to
iterate the finite source expansion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The inverse angular operator is evaluation of the actual differential
on the actual inverse angular vector. -/
theorem n07b_inverseAngle_eq_fderiv (Ψ : PolarPoint → PolarPoint)
    (F : PolarPoint → ℝ) (x : PolarPoint) :
    n07bInverseAngleDerivative Ψ F x =
      fderiv ℝ F x (n07bInverseAngleVector Ψ x) :=
  (polarCLM_apply_decompose (fderiv ℝ F x) (n07bInverseAngleVector Ψ x)).symm

theorem n07b_inverseAngle_mul (Ψ : PolarPoint → PolarPoint)
    {F G : PolarPoint → ℝ} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    n07bInverseAngleDerivative Ψ (fun y => F y * G y) x =
      n07bInverseAngleDerivative Ψ F x * G x +
        F x * n07bInverseAngleDerivative Ψ G x := by
  unfold n07bInverseAngleDerivative
  rw [radialPartial_mul hF hG, angularPartial_mul hF hG]
  ring

theorem n07b_inverseAngle_finset_sum {ι : Type*}
    (Ψ : PolarPoint → PolarPoint) (s : Finset ι) {F : ι → PolarPoint → ℝ}
    {x : PolarPoint} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) :
    n07bInverseAngleDerivative Ψ (fun y => ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, n07bInverseAngleDerivative Ψ (F i) x := by
  classical
  rw [n07b_inverseAngle_eq_fderiv, fderiv_fun_sum hF]
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i _ => (n07b_inverseAngle_eq_fderiv Ψ (F i) x).symm)

/-- The coefficient of the unchanged material jet. -/
def n07bMaterialCoeffStay (T : MaterialData) (β : ℝ)
    (Ψ : PolarPoint → PolarPoint) (c : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  T.H x.1 ^ (-β) * n07bInverseAngleDerivative Ψ (fun y => T.H y.1 ^ β * c y) x

/-- The coefficient of the next material radial jet. -/
def n07bMaterialCoeffRadial (T : MaterialData)
    (Ψ : PolarPoint → PolarPoint) (c : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  ((n07bInverseAngleVector Ψ x).1 / T.ell x.1) * c x

/-- The coefficient of the next angular jet. -/
def n07bMaterialCoeffAngular
    (Ψ : PolarPoint → PolarPoint) (c : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (n07bInverseAngleVector Ψ x).2 * c x

variable {D : ReferenceData} {T : MaterialData}

/-- The physical material weight is smooth at every actual annular point. -/
theorem n07b_contDiffAt_physicalMaterialWeight (hT : IsMaterialData D T)
    {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) (β : ℝ) :
    ContDiffAt ℝ ∞ (fun y : PolarPoint => T.H y.1 ^ β) x := by
  have hH : ContDiffAt ℝ ∞ T.H x.1 :=
    (hT.1 T.H (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hx)
  exact (hH.comp x contDiffAt_fst).rpow_const_of_ne (hT.2.1 x.1 hx).2.1.ne'

/-- The three new coefficients are locally smooth whenever the preceding
coefficient and actual chart are smooth and the actual Jacobian is nonzero. -/
theorem n07b_contDiffAt_materialChainCoefficients (hT : IsMaterialData D T)
    {Ψ : PolarPoint → PolarPoint} {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (β : ℝ)
    (hΨ : ContDiffAt ℝ ∞ Ψ x) (hJ : planeJacobian Ψ x ≠ 0)
    (hc : ContDiffAt ℝ ∞ c x) :
    ContDiffAt ℝ ∞ (n07bMaterialCoeffStay T β Ψ c) x ∧
      ContDiffAt ℝ ∞ (n07bMaterialCoeffRadial T Ψ c) x ∧
      ContDiffAt ℝ ∞ (n07bMaterialCoeffAngular Ψ c) x := by
  have hweight := n07b_contDiffAt_physicalMaterialWeight hT hx β
  have hinvweight := n07b_contDiffAt_physicalMaterialWeight hT hx (-β)
  have hV := n07b_contDiffAt_inverseAngleVector hΨ hJ
  have hell : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.ell y.1) x :=
    ((hT.1 T.ell (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hx)).comp x contDiffAt_fst
  refine ⟨?_, ?_, ?_⟩
  · exact hinvweight.mul (n07b_contDiffAt_inverseAngleDerivative hΨ hJ (hweight.mul hc))
  · exact (hV.fst.div hell (hT.2.1 x.1 hx).1.ne').mul hc
  · exact hV.snd.mul hc

/-- The material coordinate has the actual radial derivative `1 / ell`.
Consequently the inverse angular direction has the displayed action on
any differentiable material-coordinate scalar. -/
theorem n07b_inverseAngle_material_comp (hT : IsMaterialData D T)
    (Ψ : PolarPoint → PolarPoint) {u : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b)
    (hu : DifferentiableAt ℝ u (n07bMaterialChart T x)) :
    n07bInverseAngleDerivative Ψ (u ∘ n07bMaterialChart T) x =
      (n07bInverseAngleVector Ψ x).1 / T.ell x.1 *
          radialPartial u (n07bMaterialChart T x) +
        (n07bInverseAngleVector Ψ x).2 * angularPartial u (n07bMaterialChart T x) := by
  have hcoord := n07bMaterialChart_hasFDerivAt hT hx
  rw [n07b_inverseAngle_eq_fderiv, (hu.hasFDerivAt.comp x hcoord).fderiv,
    ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [polarCLM_apply_decompose]
  change ((1 / T.ell x.1) * (n07bInverseAngleVector Ψ x).1) *
      radialPartial u (n07bMaterialChart T x) +
      (n07bInverseAngleVector Ψ x).2 * angularPartial u (n07bMaterialChart T x) = _
  simp only [div_eq_mul_inv, one_mul]
  ring

/-- Applying the actual direction to a material mixed jet increases its
total order by one and introduces precisely the two coordinate factors. -/
theorem n07b_inverseAngle_materialJet (hT : IsMaterialData D T)
    (Ψ : PolarPoint → PolarPoint) {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (a b : ℕ) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) :
    n07bInverseAngleDerivative Ψ
        (fun y => mixedDerivative a b u (n07bMaterialChart T y)) x =
      (n07bInverseAngleVector Ψ x).1 / T.ell x.1 *
          mixedDerivative (a + 1) b u (n07bMaterialChart T x) +
        (n07bInverseAngleVector Ψ x).2 *
          mixedDerivative a (b + 1) u (n07bMaterialChart T x) := by
  change n07bInverseAngleDerivative Ψ (mixedDerivative a b u ∘ n07bMaterialChart T) x = _
  rw [n07b_inverseAngle_material_comp hT Ψ hx
    ((contDiff_mixedDerivative hu a b).differentiable (by simp) _),
    radialPartial_mixedDerivative hu a b, angularPartial_mixedDerivative hu a b]

/-- Exact differentiation of one weighted material jet. The three
coefficient functions in the conclusion contain no occurrence of `u`. -/
theorem n07b_inverseAngle_weighted_materialJet (hT : IsMaterialData D T)
    (Ψ : PolarPoint → PolarPoint) (β : ℝ) {c u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (a b : ℕ) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (hc : ContDiffAt ℝ ∞ c x) :
    n07bInverseAngleDerivative Ψ
        (fun y => T.H y.1 ^ β * c y * mixedDerivative a b u (n07bMaterialChart T y)) x =
      T.H x.1 ^ β *
        (n07bMaterialCoeffStay T β Ψ c x * mixedDerivative a b u (n07bMaterialChart T x) +
          n07bMaterialCoeffRadial T Ψ c x *
            mixedDerivative (a + 1) b u (n07bMaterialChart T x) +
          n07bMaterialCoeffAngular Ψ c x *
            mixedDerivative a (b + 1) u (n07bMaterialChart T x)) := by
  have hw : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.H y.1 ^ β * c y) x :=
    (n07b_contDiffAt_physicalMaterialWeight hT hx β).mul hc
  have hj : ContDiffAt ℝ ∞
      (fun y => mixedDerivative a b u (n07bMaterialChart T y)) x :=
    (contDiff_mixedDerivative hu a b).contDiffAt.comp x (n07b_contDiffAt_materialChart hT hx)
  have hcancel : T.H x.1 ^ β * T.H x.1 ^ (-β) = 1 := by
    rw [← Real.rpow_add (hT.2.1 x.1 hx).2.1, add_neg_cancel, Real.rpow_zero]
  rw [n07b_inverseAngle_mul Ψ (hw.differentiableAt (by simp))
    (hj.differentiableAt (by simp)), n07b_inverseAngle_materialJet hT Ψ hu a b hx]
  dsimp only [n07bMaterialCoeffStay, n07bMaterialCoeffRadial, n07bMaterialCoeffAngular]
  calc
    _ = (T.H x.1 ^ β * T.H x.1 ^ (-β)) *
          n07bInverseAngleDerivative Ψ (fun y => T.H y.1 ^ β * c y) x *
            mixedDerivative a b u (n07bMaterialChart T x) +
        (T.H x.1 ^ β * c x) *
          ((n07bInverseAngleVector Ψ x).1 / T.ell x.1 *
              mixedDerivative (a + 1) b u (n07bMaterialChart T x) +
            (n07bInverseAngleVector Ψ x).2 *
              mixedDerivative a (b + 1) u (n07bMaterialChart T x)) := by
      rw [hcancel, one_mul]
    _ = _ := by ring

/-- The same exact rule for an arbitrary finite material expansion. No
coefficient is selected after seeing the function `u`. -/
theorem n07b_inverseAngle_weighted_material_sum {ι : Type*}
    (hT : IsMaterialData D T) (Ψ : PolarPoint → PolarPoint) (β : ℝ)
    (s : Finset ι) (a b : ι → ℕ) (c : ι → PolarPoint → ℝ)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (hc : ∀ i ∈ s, ContDiffAt ℝ ∞ (c i) x) :
    n07bInverseAngleDerivative Ψ
        (fun y => T.H y.1 ^ β * ∑ i ∈ s,
          c i y * mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) x =
      T.H x.1 ^ β * ∑ i ∈ s,
        (n07bMaterialCoeffStay T β Ψ (c i) x *
            mixedDerivative (a i) (b i) u (n07bMaterialChart T x) +
          n07bMaterialCoeffRadial T Ψ (c i) x *
            mixedDerivative (a i + 1) (b i) u (n07bMaterialChart T x) +
          n07bMaterialCoeffAngular Ψ (c i) x *
            mixedDerivative (a i) (b i + 1) u (n07bMaterialChart T x)) := by
  classical
  have hcoord := n07b_contDiffAt_materialChart hT hx
  have hweight := n07b_contDiffAt_physicalMaterialWeight hT hx β
  have hterm (i : ι) (hi : i ∈ s) : DifferentiableAt ℝ
      (fun y => T.H y.1 ^ β * c i y *
        mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) x :=
    ((hweight.mul (hc i hi)).mul
      ((contDiff_mixedDerivative hu (a i) (b i)).contDiffAt.comp x hcoord)).differentiableAt
        (by simp)
  have heq : (fun y : PolarPoint => T.H y.1 ^ β * ∑ i ∈ s,
      c i y * mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) =
      (fun y => ∑ i ∈ s, T.H y.1 ^ β * c i y *
        mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) := by
    funext y
    simp only [Finset.mul_sum, mul_assoc]
  rw [heq, n07b_inverseAngle_finset_sum Ψ s hterm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi =>
    n07b_inverseAngle_weighted_materialJet hT Ψ β hu (a i) (b i) hx (hc i hi))

/-- The actual material pullback recovers the physical source, without
requiring any regularity of that source for this algebraic identity. -/
theorem n07b_materialPullback_restore (hT : IsMaterialData D T)
    (β : ℝ) (f : PolarPoint → ℝ) {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) :
    T.H x.1 ^ β * materialPullback T β f (n07bMaterialChart T x) = f x := by
  have hinv : T.radius (T.rho x.1) = x.1 := hT.2.2.2.2.2.2.2.2.1 x.1 hx
  change T.H x.1 ^ β *
    (T.H (T.radius (T.rho x.1)) ^ (-β) * f (T.radius (T.rho x.1), x.2)) = f x
  rw [hinv, ← mul_assoc, ← Real.rpow_add (hT.2.1 x.1 hx).2.1,
    add_neg_cancel, Real.rpow_zero, one_mul]

/-- The initial actual source expression has exactly the prescribed
source-independent coefficient `h / |J|` in material coordinates. -/
theorem n07b_physicalSourceJet_zero_material (hT : IsMaterialData D T)
    {S : PhysicalSpacesData} (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (f : PolarPoint → ℝ) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) :
    n07bPhysicalSourceJet K z m f 0 x =
      T.H x.1 ^ β * (K.height z m x / |planeJacobian (K.chart z m) x|) *
        mixedDerivative 0 0 (materialPullback T β f) (n07bMaterialChart T x) := by
  simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]
  calc
    _ = (K.height z m x / |planeJacobian (K.chart z m) x|) * f x := by
      dsimp only [n07bPhysicalSourceJet]
      ring
    _ = (K.height z m x / |planeJacobian (K.chart z m) x|) *
        (T.H x.1 ^ β * materialPullback T β f (n07bMaterialChart T x)) :=
      congrArg (fun v : ℝ => (K.height z m x / |planeJacobian (K.chart z m) x|) * v)
        (n07b_materialPullback_restore hT β f hx).symm
    _ = _ := by ring

end ContinuousFlexibility.Analysis
