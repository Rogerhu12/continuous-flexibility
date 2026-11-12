import ContinuousFlexibility.Analysis.N04bMovingDomains
import ContinuousFlexibility.Analysis.ParameterizedCircleInverse

/-!
# The actual inverse on a closed travel strip

The two boundary circle lifts and the interior bijection have disjoint
images. They therefore determine a bijection on the entire closed strip.
The chosen inverse on that closed strip agrees with every actual interior
inverse, and its endpoint-circle images are proved from the forward map.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

private theorem n04b_bijOn_union_disjoint
    {α β : Type*} {f : α → β} {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂)
    (hd : Disjoint t₁ t₂) :
    BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) := by
  apply h₁.union h₂
  rintro x (hx | hx) y (hy | hy) he
  · exact h₁.injOn hx hy he
  · exfalso
    exact Set.disjoint_left.mp hd (h₁.mapsTo hx) (he.symm ▸ h₂.mapsTo hy)
  · exfalso
    exact Set.disjoint_left.mp hd (h₁.mapsTo hy) (he ▸ h₂.mapsTo hx)
  · exact h₂.injOn hx hy he

theorem n04b_bijOn_radial_line
    {F : PolarPoint → PolarPoint} {h : ℝ → ℝ} {a c : ℝ}
    (hF : ∀ θ, F (a, θ) = (c, h θ)) (hh : Function.Bijective h) :
    BijOn F (({a} : Set ℝ) ×ˢ univ) (({c} : Set ℝ) ×ˢ univ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r, θ⟩ ⟨hr, _⟩
    have he : r = a := hr
    subst r
    rw [hF]
    exact ⟨rfl, mem_univ _⟩
  · rintro ⟨r, θ⟩ ⟨hr, _⟩ ⟨s, φ⟩ ⟨hs, _⟩ he
    have hr' : r = a := hr
    have hs' : s = a := hs
    subst r
    subst s
    rw [hF, hF] at he
    exact Prod.ext rfl (hh.1 (congrArg Prod.snd he))
  · rintro ⟨r, θ⟩ ⟨hr, _⟩
    have he : r = c := hr
    subst r
    obtain ⟨φ, hφ⟩ := hh.2 θ
    refine ⟨(a, φ), ⟨rfl, mem_univ _⟩, ?_⟩
    rw [hF, hφ]

private theorem n04b_closedStrip_eq_three_strata
    {a b : ℝ} (hab : a < b) :
    Icc a b ×ˢ (univ : Set ℝ) =
      ((({a} : Set ℝ) ×ˢ univ) ∪ (Ioo a b ×ˢ univ)) ∪
        (({b} : Set ℝ) ×ˢ univ) := by
  ext p
  simp only [mem_prod, mem_Icc, mem_Ioo, mem_univ, and_true,
    mem_union, mem_singleton_iff]
  constructor
  · intro hp
    rcases eq_or_lt_of_le hp.1 with ha | ha
    · exact Or.inl (Or.inl ha.symm)
    · rcases eq_or_lt_of_le hp.2 with hb | hb
      · exact Or.inr hb
      · exact Or.inl (Or.inr ⟨ha, hb⟩)
  · rintro ((ha | ⟨ha, hb⟩) | hb) <;> constructor <;> linarith

/-- An actual interior travel bijection and two actual boundary-circle
bijections determine the closed travel bijection. -/
theorem n04b_closedTravelStrip_bijOn
    {F : PolarPoint → PolarPoint} {hL hR : ℝ → ℝ} {a b T : ℝ}
    (hab : a < b) (hT : 0 < T)
    (hInterior : BijOn F (Ioo a b ×ˢ univ) (Ioo (0 : ℝ) T ×ˢ univ))
    (hLeft : ∀ θ, F (a, θ) = (0, hL θ))
    (hRight : ∀ θ, F (b, θ) = (T, hR θ))
    (hLbij : Function.Bijective hL) (hRbij : Function.Bijective hR) :
    BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ) := by
  have h0 : Disjoint ((({0} : Set ℝ) ×ˢ (univ : Set ℝ)))
      (Ioo (0 : ℝ) T ×ˢ univ) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have he : p.1 = 0 := hp.1
    linarith [hq.1.1]
  have h1 : Disjoint
      (((({0} : Set ℝ) ×ˢ (univ : Set ℝ))) ∪ (Ioo (0 : ℝ) T ×ˢ univ))
      ((({T} : Set ℝ) ×ˢ (univ : Set ℝ))) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have he : p.1 = T := hq.1
    rcases hp with hp | hp
    · have he0 : p.1 = 0 := hp.1
      linarith
    · linarith [hp.1.2]
  rw [n04b_closedStrip_eq_three_strata hab,
    n04b_closedStrip_eq_three_strata hT]
  exact n04b_bijOn_union_disjoint
    (n04b_bijOn_union_disjoint (n04b_bijOn_radial_line hLeft hLbij) hInterior h0)
    (n04b_bijOn_radial_line hRight hRbij) h1

/-- Positive derivatives and the genuine lifted period supply the
boundary bijections used in the preceding theorem. -/
theorem n04b_closedTravelStrip_bijOn_of_circle_lifts
    {F : PolarPoint → PolarPoint} {hL hR : ℝ → ℝ} {a b T P : ℝ}
    (hab : a < b) (hT : 0 < T) (hP : P ≠ 0)
    (hInterior : BijOn F (Ioo a b ×ˢ univ) (Ioo (0 : ℝ) T ×ˢ univ))
    (hLeft : ∀ θ, F (a, θ) = (0, hL θ))
    (hRight : ∀ θ, F (b, θ) = (T, hR θ))
    (hLc : Continuous hL) (hRc : Continuous hR)
    (hLd : ∀ θ, 0 < deriv hL θ) (hRd : ∀ θ, 0 < deriv hR θ)
    (hLp : ∀ θ, hL (θ + P) = hL θ + P)
    (hRp : ∀ θ, hR (θ + P) = hR θ + P) :
    BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ) :=
  n04b_closedTravelStrip_bijOn hab hT hInterior hLeft hRight
    ⟨(strictMono_of_deriv_pos hLd).injective,
      surjective_of_continuous_periodic_lift hP hLc hLp⟩
    ⟨(strictMono_of_deriv_pos hRd).injective,
      surjective_of_continuous_periodic_lift hP hRc hRp⟩

/-- The inverse chosen on the closed strip agrees with an already
constructed inverse on the open strip. -/
theorem n04b_closedTravelInverse_eq_interior
    {F X : PolarPoint → PolarPoint} {a b T : ℝ}
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hX : MapsTo X (Ioo (0 : ℝ) T ×ˢ univ) (Ioo a b ×ˢ univ))
    (hFX : RightInvOn X F (Ioo (0 : ℝ) T ×ˢ univ)) :
    EqOn (Function.invFunOn F (Icc a b ×ˢ univ)) X
      (Ioo (0 : ℝ) T ×ˢ univ) := by
  intro q hq
  have hqc : q ∈ Icc (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
    ⟨⟨hq.1.1.le, hq.1.2.le⟩, mem_univ _⟩
  have hXq := hX hq
  apply hClosed.injOn (hClosed.surjOn.mapsTo_invFunOn hqc)
    ⟨⟨hXq.1.1.le, hXq.1.2.le⟩, mem_univ _⟩
  exact (hClosed.surjOn.rightInvOn_invFunOn hqc).trans (hFX hq).symm

/-- The closed inverse maps each actual endpoint circle onto the physical
endpoint circle, including every real angular lift. -/
theorem n04b_closedTravelInverse_image_endpoint
    {F : PolarPoint → PolarPoint} {h : ℝ → ℝ} {a b T r s : ℝ}
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hr : r ∈ Icc a b)
    (hEndpoint : ∀ θ, F (r, θ) = (s, h θ))
    (hh : Function.Bijective h) :
    Function.invFunOn F (Icc a b ×ˢ univ) '' (({s} : Set ℝ) ×ˢ univ) =
      ({r} : Set ℝ) ×ˢ univ := by
  rw [← (n04b_bijOn_radial_line hEndpoint hh).image_eq]
  apply hClosed.injOn.leftInvOn_invFunOn.image_image'
  intro p hp
  have he : p.1 = r := hp.1
  exact ⟨he.symm ▸ hr, mem_univ _⟩

end ContinuousFlexibility.Analysis
