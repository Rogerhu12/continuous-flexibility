module

public import ContinuousFlexibility.Analysis.ParameterizedCircleInverse
public import ContinuousFlexibility.Analysis.CircleInverseExistence
public import ContinuousFlexibility.Analysis.TravelStripGlobalInverse
public import ContinuousFlexibility.Analysis.CylinderSobolev

/-!
# Genuine positive cylinder coordinates from two scalar interpolations

First fix the angle φ. A positive radial coordinate Y is then constructed
at fixed η=φ(r,θ). The actual Jacobian is Y_r·φ_θ. The two scalar inverse
functions give an explicit global inverse, whose joint smoothness follows
from the already proved parameterized implicit-function theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual inverse of the radial function at fixed angular parameter. -/
def positiveFiberRadialInverse (Y : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  Function.invFun (fun r => Y (r, p.2)) p.1

theorem positiveFiberRadialInverse_properties
    {Y : PolarPoint → ℝ} (hY : ContDiff ℝ ∞ Y) {B : ℝ} (hB : 0 < B)
    (hLower : ∀ r η, B ≤ deriv (fun t => Y (t, η)) r) :
    ContDiff ℝ ∞ (positiveFiberRadialInverse Y) ∧
      (∀ p : PolarPoint, Y (positiveFiberRadialInverse Y p, p.2) = p.1) ∧
      (∀ p : PolarPoint, positiveFiberRadialInverse Y (Y p, p.2) = p.1) := by
  have hbij (η : ℝ) : Function.Bijective (fun r => Y (r, η)) :=
    bijective_of_deriv_lower_bound hB (fun r => hLower r η)
  have hright (p : PolarPoint) :
      Y (positiveFiberRadialInverse Y p, p.2) = p.1 :=
    Function.rightInverse_invFun (hbij p.2).2 p.1
  have hleft (p : PolarPoint) :
      positiveFiberRadialInverse Y (Y p, p.2) = p.1 :=
    Function.leftInverse_invFun (hbij p.2).1 p.1
  have hswap : ContDiff ℝ ∞ (fun p : PolarPoint => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hInv : ContDiff ℝ ∞
      (fun p : PolarPoint => positiveFiberRadialInverse Y (p.2, p.1)) :=
    contDiff_parameterized_scalar_rightInverse
      (F := fun p : PolarPoint => Y (p.2, p.1))
      (hY.comp hswap)
      (fun p => hB.trans_le (hLower p.2 p.1))
      (fun p => hright (p.2, p.1))
  exact ⟨hInv.comp hswap, hright, hleft⟩

def positiveFiberChart (φ Y : PolarPoint → ℝ) (p : PolarPoint) : PolarPoint :=
  (Y (p.1, φ p), φ p)

def positiveFiberChartInverse (φ Y : PolarPoint → ℝ) (p : PolarPoint) : PolarPoint :=
  (positiveFiberRadialInverse Y p,
    parameterizedCircleInverse φ (positiveFiberRadialInverse Y p, p.2))

/-- The triangular change of angle removes the troublesome cross term
from the positivity test. This identity uses actual Fréchet derivatives. -/
theorem planeJacobian_positiveFiberChart
    {φ Y : PolarPoint → ℝ} {p : PolarPoint}
    (hφ : DifferentiableAt ℝ φ p)
    (hY : DifferentiableAt ℝ Y (p.1, φ p)) :
    planeJacobian (positiveFiberChart φ Y) p =
      radialPartial Y (p.1, φ p) * angularPartial φ p := by
  let H : PolarPoint → PolarPoint := fun q => (q.1, φ q)
  let K : PolarPoint → PolarPoint := fun q => (Y q, q.2)
  have hH : DifferentiableAt ℝ H p := differentiableAt_fst.prodMk hφ
  have hK : DifferentiableAt ℝ K (H p) := hY.prodMk differentiableAt_snd
  have he : positiveFiberChart φ Y = K ∘ H := by
    funext q
    rfl
  rw [he, planeJacobian_comp hH hK,
    planeJacobian_preserve_second hY, planeJacobian_preserve_first hφ]

/-- Both input derivative bounds are obtained from the explicit scalar
interpolations. They give a genuine global chart and actual smooth inverse;
no Jacobian or inverse regularity of the resulting chart is assumed. -/
theorem positiveFiberChart_geometry
    {φ Y : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) (hY : ContDiff ℝ ∞ Y)
    {κ B T : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hT : T ≠ 0)
    (hφLower : ∀ r θ, κ ≤ deriv (fun η => φ (r, η)) θ)
    (hYLower : ∀ r η, B ≤ deriv (fun t => Y (t, η)) r)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T) :
    ContDiff ℝ ∞ (positiveFiberChart φ Y) ∧
      ContDiff ℝ ∞ (positiveFiberChartInverse φ Y) ∧
      Function.LeftInverse (positiveFiberChartInverse φ Y) (positiveFiberChart φ Y) ∧
      Function.RightInverse (positiveFiberChartInverse φ Y) (positiveFiberChart φ Y) ∧
      (∀ p : PolarPoint, B * κ ≤ planeJacobian (positiveFiberChart φ Y) p) := by
  have hp : ∀ p : PolarPoint, 0 < deriv (fun η => φ (p.1, η)) p.2 :=
    fun p => hκ.trans_le (hφLower p.1 p.2)
  have hA := contDiff_parameterizedCircleInverse hT hφ hp hperiod
  have hAR := parameterizedCircleInverse_right_inverse hT hφ hperiod
  have hAL := parameterizedCircleInverse_left_inverse hp
  obtain ⟨hR, hRR, hRL⟩ := positiveFiberRadialInverse_properties hY hB hYLower
  have hChart : ContDiff ℝ ∞ (positiveFiberChart φ Y) :=
    (hY.comp (contDiff_fst.prodMk hφ)).prodMk hφ
  have hInv : ContDiff ℝ ∞ (positiveFiberChartInverse φ Y) :=
    hR.prodMk (hA.comp (hR.prodMk contDiff_snd))
  refine ⟨hChart, hInv, ?_, ?_, ?_⟩
  · intro p
    have hrad : positiveFiberRadialInverse Y (positiveFiberChart φ Y p) = p.1 :=
      hRL (p.1, φ p)
    apply Prod.ext
    · exact hrad
    · change parameterizedCircleInverse φ
        (positiveFiberRadialInverse Y (positiveFiberChart φ Y p), φ p) = p.2
      rw [hrad]
      exact hAL p
  · intro p
    have hang : φ (positiveFiberChartInverse φ Y p) = p.2 :=
      hAR (positiveFiberRadialInverse Y p, p.2)
    apply Prod.ext
    · change Y (positiveFiberRadialInverse Y p,
        φ (positiveFiberChartInverse φ Y p)) = p.1
      rw [hang]
      exact hRR p
    · exact hang
  · intro p
    rw [planeJacobian_positiveFiberChart
      (hφ.differentiable (by simp) p) (hY.differentiable (by simp) _)]
    have hrad : B ≤ radialPartial Y (p.1, φ p) := by
      have hh := hYLower p.1 (φ p)
      rw [deriv_cylinder_radial_slice (hY.differentiable (by simp)) p.1 (φ p)] at hh
      exact hh
    have hang : κ ≤ angularPartial φ p := by
      have hh := hφLower p.1 p.2
      rw [deriv_cylinder_angular_slice (hφ.differentiable (by simp)) p.1 p.2] at hh
      exact hh
    exact mul_le_mul hrad hang hκ.le ((hB.trans_le hrad).le)

/-- Prescribed radial endpoint values give the exact open-strip image.
The inverse used for surjectivity is the actual smooth inverse above. -/
theorem positiveFiberChart_bijOn_openStrip
    {φ Y : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) (hY : ContDiff ℝ ∞ Y)
    {κ B T l r α β : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hT : T ≠ 0)
    (hφLower : ∀ x θ, κ ≤ deriv (fun η => φ (x, η)) θ)
    (hYLower : ∀ x η, B ≤ deriv (fun t => Y (t, η)) x)
    (hperiod : ∀ x θ, φ (x, θ + T) = φ (x, θ) + T)
    (hleft : ∀ η, Y (l, η) = α) (hright : ∀ η, Y (r, η) = β) :
    BijOn (positiveFiberChart φ Y) (Ioo l r ×ˢ (univ : Set ℝ))
      (Ioo α β ×ˢ (univ : Set ℝ)) := by
  obtain ⟨_, _, hInvL, hInvR, _⟩ :=
    positiveFiberChart_geometry hφ hY hκ hB hT hφLower hYLower hperiod
  have hmono (η : ℝ) : StrictMono (fun x => Y (x, η)) :=
    strictMono_of_deriv_pos (fun x => hB.trans_le (hYLower x η))
  have hmaps : MapsTo (positiveFiberChart φ Y)
      (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo α β ×ˢ (univ : Set ℝ)) := by
    intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · change α < Y (p.1, φ p)
      rw [← hleft (φ p)]
      exact hmono (φ p) hp.1.1
    · change Y (p.1, φ p) < β
      rw [← hright (φ p)]
      exact hmono (φ p) hp.1.2
  refine ⟨hmaps, hInvL.injective.injOn, ?_⟩
  intro q hq
  refine ⟨positiveFiberChartInverse φ Y q, ?_, hInvR q⟩
  have hR := (positiveFiberRadialInverse_properties hY hB hYLower).2.1 q
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · change l < positiveFiberRadialInverse Y q
    apply lt_of_not_ge
    intro hle
    have hh := (hmono q.2).monotone hle
    rw [hR, hleft q.2] at hh
    exact (not_le_of_gt hq.1.1) hh
  · change positiveFiberRadialInverse Y q < r
    apply lt_of_not_ge
    intro hle
    have hh := (hmono q.2).monotone hle
    rw [hR, hright q.2] at hh
    exact (not_le_of_gt hq.1.2) hh

end ContinuousFlexibility.Analysis

