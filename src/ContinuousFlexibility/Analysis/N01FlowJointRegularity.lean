import ContinuousFlexibility.Analysis.N01FlowAngularVariation
import ContinuousFlexibility.Analysis.ReturnCorrectionPatching
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Joint differentiability of the actual N01 flow

The angular variational equation supplies the continuous angular
derivative. The original ODE supplies the radial derivative. The actual
characteristic speed is jointly continuous, including its radial square
root, so the partial-derivative criterion gives a joint strict derivative
at every interior radius. This removes the extra joint-regularity premise
from the corrected-flow equation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n01FlowJointRegularityRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

section ActualFlow

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hS hT hz hsector

theorem N01Properties.minusCharacteristicSpeed_continuousAt
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContinuousAt (minusCharacteristicSpeed (originalCoefficients D S C z)) p := by
  obtain ⟨hA, hB⟩ := hN01.characteristic_factors_contDiffAt hS hT hz hsector hp
  have hk : ContinuousAt (fun q : PolarPoint =>
      characteristicRadialRoot D S C z q.1) p :=
    (hN01.characteristicRadialRoot_continuousAt hS hT (z := z) hp.1).comp continuousAt_fst
  apply (hA.continuousAt.sub (hk.mul hB.continuousAt)).congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
  exact hN01.minusCharacteristicSpeed_eq_separated hS hT hz hsector hq

theorem N01Properties.minusFlow_hasStrictFDerivAt
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    HasStrictFDerivAt (fun q : PolarPoint => C.minusFlow z m q.1 q.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (minusCharacteristicSpeed (originalCoefficients D S C z)
          (p.1, C.minusFlow z m p.1 p.2))).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (C.minusFlow z m p.1) p.2))) p := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hopen : Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩
  have hclosed : Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
    mem_of_superset hopen (fun q hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩)
  have hΦ : ContinuousAt (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p :=
    (hN01.minusFlow_continuousOn hz m).continuousAt hclosed
  have hJ : ContinuousAt (fun q : PolarPoint => deriv (C.minusFlow z m q.1) q.2) p :=
    (hN01.minusFlow_angular_deriv_continuousOn hS hT hz hsector m).continuousAt hclosed
  have hv : ContinuousAt (fun q : PolarPoint =>
      minusCharacteristicSpeed (originalCoefficients D S C z)
        (q.1, C.minusFlow z m q.1 q.2)) p :=
    (hN01.minusCharacteristicSpeed_continuousAt hS hT hz hsector
      (p := (p.1, C.minusFlow z m p.1 p.2))
      ⟨⟨(hcontrol.1 m).1.trans hp.1, hp.2.trans (hcontrol.1 m).2.2⟩,
        mem_univ _⟩).comp (f := fun r : PolarPoint => (r.1, C.minusFlow z m r.1 r.2))
        (continuousAt_fst.prodMk hΦ)
  have hlin : Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c) := by
    have heq : (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c) =
        (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ : ℝ → (ℝ →L[ℝ] ℝ)) := by
      funext c
      exact (ContinuousLinearMap.toSpanSingletonLIE_apply ℝ ℝ c).symm
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous
  have hpartial := hasStrictFDerivAt_uncurry_coprod
    (f := C.minusFlow z m)
    (f₁ := fun r θ => ContinuousLinearMap.toSpanSingleton ℝ
      (minusCharacteristicSpeed (originalCoefficients D S C z) (r, C.minusFlow z m r θ)))
    (f₂ := fun r θ => ContinuousLinearMap.toSpanSingleton ℝ (deriv (C.minusFlow z m r) θ))
    (by
      filter_upwards [hopen] with q hq
      simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using
        ((hflow z hz m q.2).2.2.1 q.1 hq.1).hasFDerivAt)
    (by
      filter_upwards [hopen] with q hq
      simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using
        ((N01Properties.minusFlow_differentiable S C z m hN01 hz
          ⟨hq.1.1.le, hq.1.2.le⟩) q.2).hasDerivAt.hasFDerivAt)
    (by simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using hlin.continuousAt.comp hv)
    (by simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using hlin.continuousAt.comp hJ)
  simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
        Function.hasUncurryInduction, id_eq, Function.comp_def] using hpartial

theorem N01Properties.returnCorrectedMinusFlow_hasDerivAt_of_physical
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (r θ : ℝ)
    (hr : r ∈ Ioo (C.left m) (C.right m))
    (hχ : DifferentiableAt ℝ (χ m) r) (hχrange : χ m r ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => returnCorrectedMinusFlow S C χ z m s θ)
      (returnCorrectedMinusSpeed D S C χ z m
        (r, returnCorrectedMinusFlow S C χ z m r θ)) r := by
  apply hN01.returnCorrectedMinusFlow_hasDerivAt χ hz hsector m r θ hr hχ hχrange
  exact (hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m _ hr).hasFDerivAt.differentiableAt

omit hS hT hsector in
theorem N01Properties.returnCorrectedMinusFlow_continuousOn_of_physical
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (θ : ℝ) (hχ : Continuous (χ m)) :
    ContinuousOn (fun r => returnCorrectedMinusFlow S C χ z m r θ)
      (Icc (C.left m) (C.right m)) := by
  have hJ : Continuous (fun r => returnInterpolation (χ m r)
      (returnCorrectionInitialMap S C z m) θ) :=
    continuous_const.add (hχ.mul continuous_const)
  exact (hN01.minusFlow_continuousOn hz m).comp
    (continuous_id.prodMk hJ).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)

/-- Every flow assertion of N03 for the actual corrected coefficient
candidate, with the remaining speed-gap estimate displayed explicitly. -/
theorem N01Properties.returnCorrectedFlow_properties_of_physical
    (χ : ℕ → ℝ → ℝ) (m : ℕ)
    (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (hχleft : χ m (C.left m) = 0) (hχright : χ m (C.right m) = 1)
    (hgap : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      returnCorrectedMinusSpeed D S C χ z m (r, θ) ≤
        -returnCorrectedMinusSpeed D S C χ z m (r, -θ))
    (θ : ℝ) :
    returnCorrectedMinusFlow S C χ z m (C.left m) θ = θ ∧
    ContinuousOn (fun r => returnCorrectedMinusFlow S C χ z m r θ)
      (Icc (C.left m) (C.right m)) ∧
    (∀ r ∈ Ioo (C.left m) (C.right m), HasDerivAt
      (fun s => returnCorrectedMinusFlow S C χ z m s θ)
      (minusCharacteristicSpeed (returnCorrectedCoefficients D S C χ z)
        (r, returnCorrectedMinusFlow S C χ z m r θ)) r) ∧
    rightChartCandidate S C z m (returnCorrectedMinusFlow S C χ z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m (-returnCorrectedMinusFlow S C χ z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have he := hN01.returnCorrectedMinusFlow_endpoints χ hz hsector m hχleft hχright θ
  refine ⟨he.1,
    hN01.returnCorrectedMinusFlow_continuousOn_of_physical hz χ m θ hχ.continuous,
    ?_, he.2.1, he.2.2⟩
  intro r hr
  have hp : (r, returnCorrectedMinusFlow S C χ z m r θ) ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have ha := (hN01.characteristic_coefficient_regular hS hT hz hsector hp).1
  rw [returnCorrectedCoefficients_minusCharacteristicSpeed hcontrol.2.2.1 χ z m _ hr
    ha (hgap r hr _)]
  exact hN01.returnCorrectedMinusFlow_hasDerivAt_of_physical hS hT hz hsector χ m r θ hr
    (hχ.differentiable (by simp) r) (hχrange r ⟨hr.1.le, hr.2.le⟩)

end ActualFlow

end ContinuousFlexibility.Statements
