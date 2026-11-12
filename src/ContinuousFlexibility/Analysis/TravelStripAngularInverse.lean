import ContinuousFlexibility.Analysis.PlanarInverseRegularity
import ContinuousFlexibility.Analysis.ParameterizedCircleInverse
import ContinuousFlexibility.Scalar.HeightDerivatives
import Mathlib.Topology.Order.Basic

/-!
# The actual angular inverse on a parameter strip

Strict monotonicity and surjectivity construct the inverse of every
angular slice. Joint continuity, including radial endpoints, follows
by trapping the inverse between two fixed angular values. On an open
parameter set, the actual planar inverse function theorem gives joint
smoothness of the same choice.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Joint continuity of actual scalar inverses on an arbitrary parameter
domain. No regularity of the inverse is part of the hypotheses. -/
theorem continuousOn_parameterizedCircleInverse_of_strictMono
    {P : Type*} [TopologicalSpace P] {I : Set P} {F : P × ℝ → ℝ}
    (hF : ContinuousOn F (I ×ˢ univ))
    (hMono : ∀ p ∈ I, StrictMono (fun θ : ℝ => F (p, θ)))
    (hSurj : ∀ p ∈ I, Function.Surjective (fun θ : ℝ => F (p, θ))) :
    ContinuousOn (parameterizedCircleInverse F) (I ×ˢ univ) := by
  have hRight (q : P × ℝ) (hq : q.1 ∈ I) :
      F (q.1, parameterizedCircleInverse F q) = q.2 :=
    Function.rightInverse_invFun (hSurj q.1 hq) q.2
  have hFixed (θ : ℝ) :
      ContinuousOn (fun q : P × ℝ => F (q.1, θ)) (I ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk continuous_const).continuousOn
      (fun q hq => ⟨hq.1, mem_univ _⟩)
  intro q hq
  apply tendsto_order.mpr
  constructor
  · intro θ hθ
    have hlt : F (q.1, θ) < q.2 := by
      rw [← hRight q hq.1]
      exact hMono q.1 hq.1 hθ
    have he : ∀ᶠ z in 𝓝[I ×ˢ univ] q, F (z.1, θ) < z.2 :=
      Filter.Tendsto.eventually_lt (hFixed θ q hq)
        continuous_snd.continuousWithinAt hlt
    filter_upwards [self_mem_nhdsWithin, he] with z hz hzt
    by_contra hnot
    have hh : F (z.1, parameterizedCircleInverse F z) ≤ F (z.1, θ) :=
      (hMono z.1 hz.1).monotone (le_of_not_gt hnot)
    rw [hRight z hz.1] at hh
    exact (not_le_of_gt hzt) hh
  · intro θ hθ
    have hlt : q.2 < F (q.1, θ) := by
      rw [← hRight q hq.1]
      exact hMono q.1 hq.1 hθ
    have he : ∀ᶠ z in 𝓝[I ×ˢ univ] q, z.2 < F (z.1, θ) :=
      Filter.Tendsto.eventually_lt continuous_snd.continuousWithinAt
        (hFixed θ q hq) hlt
    filter_upwards [self_mem_nhdsWithin, he] with z hz hzt
    by_contra hnot
    have hh : F (z.1, θ) ≤ F (z.1, parameterizedCircleInverse F z) :=
      (hMono z.1 hz.1).monotone (le_of_not_gt hnot)
    rw [hRight z hz.1] at hh
    exact (not_le_of_gt hzt) hh

/-- The triangular map (r,θ) ↦ (r,F(r,θ)) has exactly the actual
angular derivative as its coordinate Jacobian. -/
theorem planeJacobian_preserve_first
    {F : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) :
    planeJacobian (fun q : PolarPoint => (q.1, F q)) p =
      angularPartial F p := by
  have hx : HasFDerivAt (fun q : PolarPoint => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hh := hx.prodMk hF.hasFDerivAt
  unfold planeJacobian angularPartial
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    one_mul, mul_zero, sub_zero]

/-- Smoothness of the actual angular inverse follows from a genuine
triangular planar inverse, throughout the open radial parameter set. -/
theorem contDiffOn_parameterizedCircleInverse_of_strictMono
    {I : Set ℝ} {F : PolarPoint → ℝ}
    (hI : IsOpen I) (hF : ContDiffOn ℝ ∞ F (I ×ˢ univ))
    (hPositive : ∀ p ∈ I ×ˢ univ, 0 < angularPartial F p)
    (hMono : ∀ r ∈ I, StrictMono (fun θ : ℝ => F (r, θ)))
    (hSurj : ∀ r ∈ I, Function.Surjective (fun θ : ℝ => F (r, θ))) :
    ContDiffOn ℝ ∞ (parameterizedCircleInverse F) (I ×ˢ univ) := by
  let H : PolarPoint → PolarPoint := fun p => (p.1, F p)
  let A : PolarPoint → PolarPoint := fun p => (p.1, parameterizedCircleInverse F p)
  have hOpen : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hH : ContDiffOn ℝ ∞ H (I ×ˢ univ) := contDiff_fst.contDiffOn.prodMk hF
  have hJ : ∀ p ∈ I ×ˢ univ, planeJacobian H p ≠ 0 := by
    intro p hp
    change planeJacobian (fun q : PolarPoint => (q.1, F q)) p ≠ 0
    rw [planeJacobian_preserve_first
      ((hF.contDiffAt (hOpen.mem_nhds hp)).differentiableAt (by simp))]
    exact (hPositive p hp).ne'
  have hInj : InjOn H (I ×ˢ univ) := by
    rintro ⟨r, θ⟩ hp ⟨s, η⟩ hq he
    have hrs : r = s := congrArg Prod.fst he
    subst s
    apply Prod.ext
    · rfl
    · exact (hMono r hp.1).injective (congrArg Prod.snd he)
  have hMaps : MapsTo A (I ×ˢ univ) (I ×ˢ univ) :=
    fun p hp => ⟨hp.1, mem_univ _⟩
  have hRight : RightInvOn A H (I ×ˢ univ) := by
    intro p hp
    apply Prod.ext
    · rfl
    · exact Function.rightInverse_invFun (hSurj p.1 hp.1) p.2
  exact (contDiffOn_planar_rightInverse_of_injOn hOpen hOpen hH hJ hInj hMaps hRight).snd

end ContinuousFlexibility.Analysis
