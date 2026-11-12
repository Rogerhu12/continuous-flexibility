import ContinuousFlexibility.Analysis.TravelStripGlobalInverse

/-!
# Injectivity on a genuine two-sided cylindrical collar

Positive angular derivatives invert every angular slice. The actual
Jacobian quotient then makes radial travel at fixed output angle strictly
increasing. This proves injectivity without constant outer-boundary values.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Interior angular positivity gives strict monotonicity of every
complete lifted angular slice of an open strip. -/
theorem n04b_strictMono_openStrip_angle
    {F : PolarPoint → PolarPoint} {I : Set ℝ}
    (hI : IsOpen I) (hF : ContDiffOn ℝ ∞ F (I ×ˢ univ))
    (hAngle : ∀ p ∈ I ×ˢ univ, 0 < angularPartial (fun q => (F q).2) p)
    {r : ℝ} (hr : r ∈ I) :
    StrictMono (fun θ : ℝ => (F (r, θ)).2) := by
  apply strictMono_of_deriv_pos
  intro θ
  have hp : (r, θ) ∈ I ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ _⟩
  have hDiff := (hF.contDiffAt ((hI.prod isOpen_univ).mem_nhds hp)).differentiableAt
    (by simp)
  have hd := hDiff.hasFDerivAt.snd
  have hc := hd.comp_hasDerivAt θ
    ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  have he : (fun q : PolarPoint => (F q).2) ∘ (fun η : ℝ => (r, η)) =
      (fun η : ℝ => (F (r, η)).2) := rfl
  rw [he] at hc
  have hvalue : deriv (fun η : ℝ => (F (r, η)).2) θ =
      angularPartial (fun q => (F q).2) (r, θ) := by
    rw [hc.deriv]
    unfold angularPartial
    rw [hd.fderiv]
  rw [hvalue]
  exact hAngle (r, θ) hp

/-- Strict angular and normalized radial monotonicity determine both
coordinates of a point from its actual image. -/
theorem n04b_injOn_of_angleNormalizedTravel
    {F : PolarPoint → PolarPoint} {I : Set ℝ}
    (hAngle : ∀ r ∈ I, StrictMono (fun θ : ℝ => (F (r, θ)).2))
    (hRadial : ∀ η : ℝ,
      StrictMonoOn (fun r : ℝ => angleNormalizedTravel F (r, η)) I) :
    InjOn F (I ×ˢ (univ : Set ℝ)) := by
  have hRecover (p : PolarPoint) (hp : p.1 ∈ I) :
      angleNormalizedTravel F (p.1, (F p).2) = (F p).1 := by
    have hi : parameterizedCircleInverse (fun q => (F q).2) (p.1, (F p).2) = p.2 :=
      Function.leftInverse_invFun (hAngle p.1 hp).injective p.2
    simp only [angleNormalizedTravel, hi, Prod.eta]
  rintro ⟨r, θ⟩ hp ⟨s, η⟩ hq he
  have hφ : (F (r, θ)).2 = (F (s, η)).2 := congrArg Prod.snd he
  have hσ : (F (r, θ)).1 = (F (s, η)).1 := congrArg Prod.fst he
  have heTravel :
      angleNormalizedTravel F (r, (F (r, θ)).2) =
        angleNormalizedTravel F (s, (F (r, θ)).2) := by
    calc
      _ = (F (r, θ)).1 := hRecover (r, θ) hp.1
      _ = (F (s, η)).1 := hσ
      _ = angleNormalizedTravel F (s, (F (s, η)).2) :=
        (hRecover (s, η) hq.1).symm
      _ = _ := congrArg (fun v => angleNormalizedTravel F (s, v)) hφ.symm
  have hrs : r = s := (hRadial (F (r, θ)).2).injOn hp.1 hq.1 heTravel
  subst s
  exact Prod.ext rfl ((hAngle r hp.1).injective hφ)

/-- Differential positivity on a full collar gives injectivity on one
smaller full collar, uniformly over the lifted angular coordinate. -/
theorem n04b_injOn_cylindrical_collar
    {F : PolarPoint → PolarPoint} {δ P : ℝ} (hδ : 0 < δ) (hP : P ≠ 0)
    (hF : ContDiffOn ℝ ∞ F (Ioo (-δ) δ ×ˢ (univ : Set ℝ)))
    (hAngle : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ),
      0 < angularPartial (fun q => (F q).2) p)
    (hJ : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), 0 < planeJacobian F p)
    (hPeriod : ∀ r ∈ Ioo (-δ) δ, ∀ θ : ℝ,
      (F (r, θ + P)).2 = (F (r, θ)).2 + P) :
    InjOn F (Ioo (-δ / 2) (δ / 2) ×ˢ (univ : Set ℝ)) := by
  have hsub : Icc (-δ / 2) (δ / 2) ⊆ Ioo (-δ) δ := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have hsub₂ : Icc (-δ / 2) (δ / 2) ×ˢ (univ : Set ℝ) ⊆
      Ioo (-δ) δ ×ˢ (univ : Set ℝ) := prod_mono hsub Subset.rfl
  have hclosed := hF.continuousOn.mono hsub₂
  have hsmall : Ioo (-δ / 2) (δ / 2) ×ˢ (univ : Set ℝ) ⊆
      Ioo (-δ) δ ×ˢ (univ : Set ℝ) :=
    (prod_mono Ioo_subset_Icc_self Subset.rfl).trans hsub₂
  have hMono (r : ℝ) (hr : r ∈ Icc (-δ / 2) (δ / 2)) :
      StrictMono (fun θ : ℝ => (F (r, θ)).2) :=
    n04b_strictMono_openStrip_angle isOpen_Ioo hF hAngle (hsub hr)
  have hSurj (r : ℝ) (hr : r ∈ Icc (-δ / 2) (δ / 2)) :
      Function.Surjective (fun θ : ℝ => (F (r, θ)).2) :=
    surjective_of_continuous_periodic_lift hP
      (hclosed.snd.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => ⟨hr, mem_univ θ⟩))
      (hPeriod r (hsub hr))
  have hinj : InjOn F (Icc (-δ / 2) (δ / 2) ×ˢ (univ : Set ℝ)) :=
    n04b_injOn_of_angleNormalizedTravel hMono
      (strictMonoOn_angleNormalizedTravel hclosed (hF.mono hsmall)
        (fun p hp => hAngle p (hsmall hp))
        (fun p hp => hJ p (hsmall hp)) hMono hSurj)
  exact hinj.mono (prod_mono Ioo_subset_Icc_self Subset.rfl)

end ContinuousFlexibility.Analysis
