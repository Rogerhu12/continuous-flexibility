module

public import ContinuousFlexibility.Analysis.N06PositiveDividedRegularity
public import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity

/-!
# Symmetries of the genuine forward principal density

The full derivative of a reflected chart is obtained by differentiating
its actual local equivariance. Periodicity and reflection of the density
then follow from the physical coefficient symmetries. Both statements
concern forward derivatives at interior physical points.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual derivative of a reflected chart has the four required
coordinate signs. This is one calculation for the two coordinate directions. -/
theorem n06_fderiv_chart_reflection {F : PolarPoint → PolarPoint} {l r : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hsym : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), F (p.1, -p.2) = ((F p).1, -(F p).2))
    {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    fderiv ℝ F (p.1, -p.2) (1, 0) =
        ((fderiv ℝ F p (1, 0)).1, -(fderiv ℝ F p (1, 0)).2) ∧
      fderiv ℝ F (p.1, -p.2) (0, 1) =
        (-(fderiv ℝ F p (0, 1)).1, (fderiv ℝ F p (0, 1)).2) := by
  let R : PolarPoint →L[ℝ] PolarPoint :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hRp (q : PolarPoint) : R q = (q.1, -q.2) := rfl
  have hp' : (p.1, -p.2) ∈ Ioo l r ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  have hFp := (hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hFr := (hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp')).differentiableAt (by simp)
  have heq : (fun q => F (R q)) =ᶠ[𝓝 p] (fun q => R (F q)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hsym q hq
  have hleft := hFr.hasFDerivAt.comp p R.hasFDerivAt
  have hright := R.hasFDerivAt.comp p hFp.hasFDerivAt
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  have h₁ := congrArg (fun M : PolarPoint →L[ℝ] PolarPoint => M (1, 0)) hd
  have h₂ := congrArg (fun M : PolarPoint →L[ℝ] PolarPoint => M (0, 1)) hd
  simp only [ContinuousLinearMap.comp_apply, hRp, neg_zero] at h₁ h₂
  refine ⟨h₁, ?_⟩
  have hneg : ((0 : ℝ), -(1 : ℝ)) = -((0 : ℝ), (1 : ℝ)) := by ext <;> norm_num
  rw [hneg, map_neg] at h₂
  have hn := congrArg Neg.neg h₂
  simpa only [neg_neg, Prod.neg_mk] using hn

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A genuine angular lift and periodic physical coefficients give a
periodic principal density at the physical point. -/
theorem n06_coordinatePrincipalDensity_periodicOn
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {H : PolarPoint → ℝ}
    {l r τ : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hlift : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), F (p + (0, τ)) = F p + (0, τ))
    {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ))
    (ha : A.a (p + (0, τ)) = A.a p) (hb : A.b (p + (0, τ)) = A.b p)
    (hc : A.c (p + (0, τ)) = A.c p) (hh : H (p + (0, τ)) = H p) :
    (coordinatePrincipalDensity A F H).a (p + (0, τ)) = (coordinatePrincipalDensity A F H).a p ∧
      (coordinatePrincipalDensity A F H).b (p + (0, τ)) = (coordinatePrincipalDensity A F H).b p ∧
      (coordinatePrincipalDensity A F H).c (p + (0, τ)) = (coordinatePrincipalDensity A F H).c p := by
  have hd := n06_fderiv_chart_lift hF hlift hp
  have hj := n06_planeJacobian_chart_lift hF hlift hp
  simp only [coordinatePrincipalDensity, coefficientQuadratic, hh, hj, hd, ha, hb, hc,
    and_self]

/-- Reflection of the true forward chart yields the even/odd/even
principal-density signs, including the mixed coefficient. -/
theorem n06_coordinatePrincipalDensity_reflectionOn
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {H : PolarPoint → ℝ}
    {l r : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hsym : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), F (p.1, -p.2) = ((F p).1, -(F p).2))
    {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ))
    (ha : A.a (p.1, -p.2) = A.a p) (hb : A.b (p.1, -p.2) = -A.b p)
    (hc : A.c (p.1, -p.2) = A.c p) (hh : H (p.1, -p.2) = H p)
    (hj : planeJacobian F (p.1, -p.2) = planeJacobian F p) :
    (coordinatePrincipalDensity A F H).a (p.1, -p.2) = (coordinatePrincipalDensity A F H).a p ∧
      (coordinatePrincipalDensity A F H).b (p.1, -p.2) = -(coordinatePrincipalDensity A F H).b p ∧
      (coordinatePrincipalDensity A F H).c (p.1, -p.2) = (coordinatePrincipalDensity A F H).c p := by
  have hd := n06_fderiv_chart_reflection hF hsym hp
  simp only [coordinatePrincipalDensity, coefficientQuadratic, hh, hj, hd.1, hd.2, ha, hb, hc]
  constructor
  · ring
  constructor <;> ring

end ContinuousFlexibility.Analysis
