module

public import ContinuousFlexibility.Analysis.N04bCollarInjectivity
public import ContinuousFlexibility.Analysis.N04bPlanarInverseGerm
public import ContinuousFlexibility.Analysis.PeriodicGermCollar

/-!
# An actual smooth inverse on a uniform target cylinder

The image of the injective source collar is open and contains the whole
zero-radius axis. Angular equivariance makes membership in that image
periodic. Compactness of one angular period supplies a genuine target
collar, on which the actual invFunOn is smooth and has full inverse germs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The image of a cylindrical source inherits the actual lifted period. -/
theorem n04b_image_strip_periodic
    {F : PolarPoint → PolarPoint} {a b P : ℝ}
    (hPeriod : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      F (r, θ + P) = F (r, θ) + (0, P))
    (r θ : ℝ) :
    (r, θ + P) ∈ F '' (Ioo a b ×ˢ (univ : Set ℝ)) ↔
      (r, θ) ∈ F '' (Ioo a b ×ˢ (univ : Set ℝ)) := by
  constructor
  · rintro ⟨p, hp, he⟩
    refine ⟨(p.1, p.2 - P), ⟨hp.1, mem_univ _⟩, ?_⟩
    have hstep : F p = F (p.1, p.2 - P) + (0, P) := by
      simpa only [sub_add_cancel, Prod.eta] using hPeriod p.1 hp.1 (p.2 - P)
    apply add_right_cancel
    calc
      F (p.1, p.2 - P) + (0, P) = F p := hstep.symm
      _ = (r, θ) + (0, P) := by
        simpa only [Prod.mk_add_mk, add_zero] using he
  · rintro ⟨p, hp, he⟩
    refine ⟨(p.1, p.2 + P), ⟨hp.1, mem_univ _⟩, ?_⟩
    calc
      F (p.1, p.2 + P) = F p + (0, P) := by
        simpa only [Prod.eta] using hPeriod p.1 hp.1 p.2
      _ = (r, θ + P) := by rw [he]; simp

/-- The chosen inverse is an actual smooth map on a full two-sided target
strip. In particular every boundary point has the exact full-neighborhood
inverse germ required by the canonical contract. -/
theorem n04b_exists_cylindrical_collar_inverse
    {F : PolarPoint → PolarPoint} {δ P : ℝ} (hδ : 0 < δ) (hP : P ≠ 0)
    (hF : ContDiffOn ℝ ∞ F (Ioo (-δ) δ ×ˢ (univ : Set ℝ)))
    (hAngle : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ),
      0 < angularPartial (fun q => (F q).2) p)
    (hJ : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), 0 < planeJacobian F p)
    (hPeriod : ∀ r ∈ Ioo (-δ) δ, ∀ θ : ℝ,
      F (r, θ + P) = F (r, θ) + (0, P))
    (hAxis : ∀ θ : ℝ, (F (0, θ)).1 = 0) :
    ∃ η : ℝ, 0 < η ∧
      let S := Ioo (-δ / 2) (δ / 2) ×ˢ (univ : Set ℝ)
      let T := Ioo (-η) η ×ˢ (univ : Set ℝ)
      let G := Function.invFunOn F S
      MapsTo G T S ∧ LeftInvOn G F S ∧ RightInvOn G F T ∧
        ContDiffOn ℝ ∞ G T ∧
        ∀ θ : ℝ, CanonicalBoundaryInverseGerm F G (0, θ) := by
  let S : Set PolarPoint := Ioo (-δ / 2) (δ / 2) ×ˢ (univ : Set ℝ)
  let G : PolarPoint → PolarPoint := Function.invFunOn F S
  have hRadSub : Ioo (-δ / 2) (δ / 2) ⊆ Ioo (-δ) δ := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have hSub : S ⊆ Ioo (-δ) δ ×ˢ (univ : Set ℝ) :=
    prod_mono hRadSub Subset.rfl
  have hS : IsOpen S := isOpen_Ioo.prod isOpen_univ
  have hsmall := hF.mono hSub
  have hJsmall : ∀ p ∈ S, planeJacobian F p ≠ 0 :=
    fun p hp => (hJ p (hSub hp)).ne'
  have hInj : InjOn F S := n04b_injOn_cylindrical_collar hδ hP hF hAngle hJ
    (fun r hr θ => by simpa using congrArg Prod.snd (hPeriod r hr θ))
  have hOpen : IsOpen (F '' S) :=
    n04b_isOpen_image_of_planeJacobian_ne_zero hS hsmall hJsmall
  have hZero (θ : ℝ) : (0, θ) ∈ S :=
    ⟨⟨by linarith, half_pos hδ⟩, mem_univ _⟩
  have hSurj : Function.Surjective (fun θ : ℝ => (F (0, θ)).2) :=
    surjective_of_continuous_periodic_lift hP
      (hF.continuousOn.snd.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => hSub (hZero θ)))
      (fun θ => by simpa using congrArg Prod.snd (hPeriod 0 (hSub (hZero θ)).1 θ))
  have hLocal (θ : ℝ) : ∀ᶠ q in 𝓝 (0, θ), q ∈ F '' S := by
    obtain ⟨φ, hφ⟩ := hSurj θ
    exact hOpen.mem_nhds ⟨(0, φ), hZero φ, Prod.ext (hAxis φ) hφ⟩
  obtain ⟨η, hη, hImage⟩ := exists_uniform_periodic_collar_of_local
    (Q := fun q => q ∈ F '' S) hP
    (n04b_image_strip_periodic (fun r hr θ => hPeriod r (hRadSub hr) θ)) hLocal
  let T : Set PolarPoint := Ioo (-η) η ×ˢ (univ : Set ℝ)
  have hT : IsOpen T := isOpen_Ioo.prod isOpen_univ
  have hTarget : T ⊆ F '' S := by
    intro q hq
    exact hImage q.1 q.2 (abs_lt.mpr hq.1)
  have hOnto : SurjOn F S (F '' S) := fun _ hy => hy
  have hMaps : MapsTo G T S := fun q hq => hOnto.mapsTo_invFunOn (hTarget hq)
  have hRight : RightInvOn G F T := by
    intro q hq
    exact hOnto.rightInvOn_invFunOn (hTarget hq)
  refine ⟨η, hη, hMaps, hInj.leftInvOn_invFunOn, hRight,
    contDiffOn_planar_rightInverse_of_injOn hS hT hsmall hJsmall hInj hMaps hRight, ?_⟩
  intro θ
  have hFzero : F (0, θ) ∈ T := by
    refine ⟨?_, mem_univ _⟩
    rw [hAxis θ]
    exact ⟨by linarith, hη⟩
  exact n04b_boundaryInverseGerm_of_rightInverse hS hT
    (hsmall.contDiffAt (hS.mem_nhds (hZero θ))) (hJsmall _ (hZero θ))
    hInj hMaps hRight (hZero θ) hFzero

end ContinuousFlexibility.Analysis
