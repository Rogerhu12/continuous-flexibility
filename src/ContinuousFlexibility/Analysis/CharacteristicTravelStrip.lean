module

public import ContinuousFlexibility.Analysis.TravelStripGlobalInverse
public import ContinuousFlexibility.Analysis.CharacteristicPrincipalDensity
public import Mathlib.Tactic.Ring

/-!
# The global strip of two genuine characteristic first integrals

The transport equations give the travel chart's actual Jacobian. Positive
angular derivatives give its positive angular coordinate, and the actual
endpoint normalization gives constant travel-time boundaries. The global
inverse is consequently constructed by the full-strip theorem, rather than
postulated among the characteristic data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual characteristic equations and endpoint normalizations imply
the full-strip bijection. This does not identify any radial half-cut. -/
theorem characteristicTravelChart_bijOn
    {U V d v : PolarPoint → ℝ} {hL hR : ℝ → ℝ} {a b W P : ℝ}
    (hab : a < b) (hP : P ≠ 0)
    (hUc : ContinuousOn U (Icc a b ×ˢ univ))
    (hVc : ContinuousOn V (Icc a b ×ˢ univ))
    (hUs : ContDiffOn ℝ ∞ U (Ioo a b ×ˢ univ))
    (hVs : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ univ))
    (hUr : ∀ p ∈ Ioo a b ×ˢ univ,
      radialPartial U p = -(d p + v p) * angularPartial U p)
    (hVr : ∀ p ∈ Ioo a b ×ˢ univ,
      radialPartial V p = -(d p - v p) * angularPartial V p)
    (hv : ∀ p ∈ Ioo a b ×ˢ univ, 0 < v p)
    (hUθ : ∀ p ∈ Ioo a b ×ˢ univ, 0 < angularPartial U p)
    (hVθ : ∀ p ∈ Ioo a b ×ˢ univ, 0 < angularPartial V p)
    (hUp : ∀ r ∈ Icc a b, ∀ θ : ℝ, U (r, θ + P) = U (r, θ) + P)
    (hVp : ∀ r ∈ Icc a b, ∀ θ : ℝ, V (r, θ + P) = V (r, θ) + P)
    (hLm : StrictMono hL) (hRm : StrictMono hR)
    (hUL : ∀ θ : ℝ, U (a, θ) = hL θ)
    (hVL : ∀ θ : ℝ, V (a, θ) = hL θ)
    (hUR : ∀ θ : ℝ, U (b, θ) = hR θ - W)
    (hVR : ∀ θ : ℝ, V (b, θ) = hR θ + W) :
    BijOn (characteristicTravelChart U V)
      (Ioo a b ×ˢ univ) (Ioo 0 W ×ˢ univ) := by
  have hC : ContinuousOn (characteristicTravelChart U V) (Icc a b ×ˢ univ) :=
    (continuousOn_const.mul (hVc.sub hUc)).prodMk
      (continuousOn_const.mul (hUc.add hVc))
  have hS : ContDiffOn ℝ ∞ (characteristicTravelChart U V) (Ioo a b ×ˢ univ) :=
    (contDiffOn_const.mul (hVs.sub hUs)).prodMk
      (contDiffOn_const.mul (hUs.add hVs))
  have hOpen : IsOpen (Ioo a b ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hUd (p : PolarPoint) (hp : p ∈ Ioo a b ×ˢ univ) :
      DifferentiableAt ℝ U p :=
    (hUs.contDiffAt (hOpen.mem_nhds hp)).differentiableAt (by simp)
  have hVd (p : PolarPoint) (hp : p ∈ Ioo a b ×ˢ univ) :
      DifferentiableAt ℝ V p :=
    (hVs.contDiffAt (hOpen.mem_nhds hp)).differentiableAt (by simp)
  apply travelStrip_bijOn hab hP hC hS
  · intro p hp
    have hd : HasFDerivAt (fun q => (characteristicTravelChart U V q).2)
        ((1 / 2 : ℝ) • (fderiv ℝ U p + fderiv ℝ V p)) p :=
      ((hUd p hp).hasFDerivAt.fun_add (hVd p hp).hasFDerivAt).const_mul (1 / 2 : ℝ)
    unfold angularPartial
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    exact mul_pos (by norm_num) (add_pos (hUθ p hp) (hVθ p hp))
  · intro p hp
    exact planeJacobian_characteristicTravelChart_pos
      (hUd p hp) (hVd p hp) (hUr p hp) (hVr p hp)
      (hv p hp) (hUθ p hp) (hVθ p hp)
  · intro r hr θ
    simp only [characteristicTravelChart, hUp r hr θ, hVp r hr θ]
    ring
  · have he : (fun θ : ℝ => (characteristicTravelChart U V (a, θ)).2) = hL := by
      funext θ
      simp only [characteristicTravelChart, hUL θ, hVL θ]
      ring
    rw [he]
    exact hLm
  · have he : (fun θ : ℝ => (characteristicTravelChart U V (b, θ)).2) = hR := by
      funext θ
      simp only [characteristicTravelChart, hUR θ, hVR θ]
      ring
    rw [he]
    exact hRm
  · intro θ
    simp only [characteristicTravelChart, hUL θ, hVL θ]
    ring
  · intro θ
    simp only [characteristicTravelChart, hUR θ, hVR θ]
    ring

end ContinuousFlexibility.Analysis
