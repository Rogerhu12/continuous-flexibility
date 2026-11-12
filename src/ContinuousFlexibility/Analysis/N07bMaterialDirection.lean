import ContinuousFlexibility.Analysis.N07bInverseDirection
import ContinuousFlexibility.Analysis.N07bMaterialAngularChain

/-!
# Weighted material calculus for arbitrary geometric directions

Each actual directional derivative of a weighted material jet has three
terms. Their coefficients depend only on the geometric vector field and
the previous coefficient. The same identity therefore handles the two
reference directions and every subsequent current angular derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

def n07bDirectionCoeffStay (T : MaterialData) (β : ℝ)
    (X : PolarPoint → PolarPoint) (c : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  T.H x.1 ^ (-β) * n07bDirectionalDerivative X (fun y => T.H y.1 ^ β * c y) x

def n07bDirectionCoeffRadial (T : MaterialData)
    (X : PolarPoint → PolarPoint) (c : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  ((X x).1 / T.ell x.1) * c x

def n07bDirectionCoeffAngular
    (X : PolarPoint → PolarPoint) (c : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (X x).2 * c x

variable {D : ReferenceData} {T : MaterialData}

theorem n07b_contDiffAt_directionChainCoefficients (hT : IsMaterialData D T)
    {X : PolarPoint → PolarPoint} {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (β : ℝ)
    (hX : ContDiffAt ℝ ∞ X x) (hc : ContDiffAt ℝ ∞ c x) :
    ContDiffAt ℝ ∞ (n07bDirectionCoeffStay T β X c) x ∧
      ContDiffAt ℝ ∞ (n07bDirectionCoeffRadial T X c) x ∧
      ContDiffAt ℝ ∞ (n07bDirectionCoeffAngular X c) x := by
  have hweight := n07b_contDiffAt_physicalMaterialWeight hT hx β
  have hinvweight := n07b_contDiffAt_physicalMaterialWeight hT hx (-β)
  have hell : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.ell y.1) x :=
    ((hT.1 T.ell (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hx)).comp x contDiffAt_fst
  refine ⟨?_, ?_, ?_⟩
  · exact hinvweight.mul (n07b_contDiffAt_directionalDerivative hX (hweight.mul hc))
  · exact (hX.fst.div hell (hT.2.1 x.1 hx).1.ne').mul hc
  · exact hX.snd.mul hc

/-- The material-coordinate derivative follows from its actual rho derivative. -/
theorem n07b_directional_material_comp (hT : IsMaterialData D T)
    (X : PolarPoint → PolarPoint) {u : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b)
    (hu : DifferentiableAt ℝ u (n07bMaterialChart T x)) :
    n07bDirectionalDerivative X (u ∘ n07bMaterialChart T) x =
      (X x).1 / T.ell x.1 *
          radialPartial u (n07bMaterialChart T x) +
        (X x).2 * angularPartial u (n07bMaterialChart T x) := by
  have hcoord := n07bMaterialChart_hasFDerivAt hT hx
  rw [n07bDirectionalDerivative_eq_fderiv, (hu.hasFDerivAt.comp x hcoord).fderiv,
    ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [polarCLM_apply_decompose]
  change ((1 / T.ell x.1) * (X x).1) *
      radialPartial u (n07bMaterialChart T x) +
      (X x).2 * angularPartial u (n07bMaterialChart T x) = _
  simp only [div_eq_mul_inv, one_mul]
  ring

/-- Applying the actual direction to a material mixed jet increases its
total order by one and introduces precisely the two coordinate factors. -/
theorem n07b_directional_materialJet (hT : IsMaterialData D T)
    (X : PolarPoint → PolarPoint) {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (a b : ℕ) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) :
    n07bDirectionalDerivative X
        (fun y => mixedDerivative a b u (n07bMaterialChart T y)) x =
      (X x).1 / T.ell x.1 *
          mixedDerivative (a + 1) b u (n07bMaterialChart T x) +
        (X x).2 *
          mixedDerivative a (b + 1) u (n07bMaterialChart T x) := by
  change n07bDirectionalDerivative X (mixedDerivative a b u ∘ n07bMaterialChart T) x = _
  rw [n07b_directional_material_comp hT X hx
    ((contDiff_mixedDerivative hu a b).differentiable (by simp) _),
    radialPartial_mixedDerivative hu a b, angularPartial_mixedDerivative hu a b]

/-- Exact differentiation of one weighted material jet. The three
coefficient functions in the conclusion contain no occurrence of `u`. -/
theorem n07b_directional_weighted_materialJet (hT : IsMaterialData D T)
    (X : PolarPoint → PolarPoint) (β : ℝ) {c u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (a b : ℕ) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (hc : ContDiffAt ℝ ∞ c x) :
    n07bDirectionalDerivative X
        (fun y => T.H y.1 ^ β * c y * mixedDerivative a b u (n07bMaterialChart T y)) x =
      T.H x.1 ^ β *
        (n07bDirectionCoeffStay T β X c x * mixedDerivative a b u (n07bMaterialChart T x) +
          n07bDirectionCoeffRadial T X c x *
            mixedDerivative (a + 1) b u (n07bMaterialChart T x) +
          n07bDirectionCoeffAngular X c x *
            mixedDerivative a (b + 1) u (n07bMaterialChart T x)) := by
  have hw : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.H y.1 ^ β * c y) x :=
    (n07b_contDiffAt_physicalMaterialWeight hT hx β).mul hc
  have hj : ContDiffAt ℝ ∞
      (fun y => mixedDerivative a b u (n07bMaterialChart T y)) x :=
    (contDiff_mixedDerivative hu a b).contDiffAt.comp x (n07b_contDiffAt_materialChart hT hx)
  have hcancel : T.H x.1 ^ β * T.H x.1 ^ (-β) = 1 := by
    rw [← Real.rpow_add (hT.2.1 x.1 hx).2.1, add_neg_cancel, Real.rpow_zero]
  rw [n07bDirectionalDerivative_mul X (hw.differentiableAt (by simp))
    (hj.differentiableAt (by simp)), n07b_directional_materialJet hT X hu a b hx]
  dsimp only [n07bDirectionCoeffStay, n07bDirectionCoeffRadial, n07bDirectionCoeffAngular]
  calc
    _ = (T.H x.1 ^ β * T.H x.1 ^ (-β)) *
          n07bDirectionalDerivative X (fun y => T.H y.1 ^ β * c y) x *
            mixedDerivative a b u (n07bMaterialChart T x) +
        (T.H x.1 ^ β * c x) *
          ((X x).1 / T.ell x.1 *
              mixedDerivative (a + 1) b u (n07bMaterialChart T x) +
            (X x).2 *
              mixedDerivative a (b + 1) u (n07bMaterialChart T x)) := by
      rw [hcancel, one_mul]
    _ = _ := by ring

/-- The same exact rule for an arbitrary finite material expansion. No
coefficient is selected after seeing the function `u`. -/
theorem n07b_directional_weighted_material_sum {ι : Type*}
    (hT : IsMaterialData D T) (X : PolarPoint → PolarPoint) (β : ℝ)
    (s : Finset ι) (a b : ι → ℕ) (c : ι → PolarPoint → ℝ)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (hc : ∀ i ∈ s, ContDiffAt ℝ ∞ (c i) x) :
    n07bDirectionalDerivative X
        (fun y => T.H y.1 ^ β * ∑ i ∈ s,
          c i y * mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) x =
      T.H x.1 ^ β * ∑ i ∈ s,
        (n07bDirectionCoeffStay T β X (c i) x *
            mixedDerivative (a i) (b i) u (n07bMaterialChart T x) +
          n07bDirectionCoeffRadial T X (c i) x *
            mixedDerivative (a i + 1) (b i) u (n07bMaterialChart T x) +
          n07bDirectionCoeffAngular X (c i) x *
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
  rw [heq, n07bDirectionalDerivative_finset_sum X s hterm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi =>
    n07b_directional_weighted_materialJet hT X β hu (a i) (b i) hx (hc i hi))

end ContinuousFlexibility.Analysis
