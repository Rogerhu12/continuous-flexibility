import ContinuousFlexibility.Scalar.Coordinates
import Mathlib.Data.Set.Function
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Linarith

/-!
# Actual physical domains cut by a travel coordinate

A travel subdomain is the intersection of the genuine physical domain with
the preimage of a canonical travel interval. Restriction of an actual
bijection gives its actual chart, and continuity on the physical open set
gives openness. One Boolean interval describes the two middle halves.

The middle cut is parametrized by the actual inverse on the full travel
strip. Its level lies in the canonical interior, so no unspecified boundary
value of `invFunOn` is used. These results do not assume a radial graph for
the physical cut and do not assert a characteristic normal form.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

variable {X : Type*}

/-- Restrict a genuine physical domain by an interval of its travel chart. -/
def n04bTravelDomain (Ω : Set X) (Γ : X → PolarPoint) (I : Set ℝ) : Set X :=
  Ω ∩ Γ ⁻¹' (I ×ˢ (univ : Set ℝ))

@[simp]
theorem mem_n04bTravelDomain {Ω : Set X} {Γ : X → PolarPoint}
    {I : Set ℝ} {x : X} :
    x ∈ n04bTravelDomain Ω Γ I ↔ x ∈ Ω ∧ (Γ x).1 ∈ I := by
  simp only [n04bTravelDomain, mem_inter_iff, mem_preimage, mem_prod,
    mem_univ, and_true]

/-- The restricted chart is a genuine bijection onto the chosen substrip. -/
theorem n04b_bijOn_travelDomain {Ω : Set X} {Γ : X → PolarPoint}
    {T : ℝ} {I : Set ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hI : I ⊆ Ioo (0 : ℝ) T) :
    BijOn Γ (n04bTravelDomain Ω Γ I) (I ×ˢ (univ : Set ℝ)) := by
  exact hΓ.subset_right (Set.prod_mono hI (Subset.rfl))

/-- In particular the image is the whole target substrip, not a subset. -/
theorem n04b_image_travelDomain {Ω : Set X} {Γ : X → PolarPoint}
    {T : ℝ} {I : Set ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hI : I ⊆ Ioo (0 : ℝ) T) :
    Γ '' n04bTravelDomain Ω Γ I = I ×ˢ (univ : Set ℝ) :=
  (n04b_bijOn_travelDomain hΓ hI).image_eq

/-- Continuity only on the actual open physical domain is sufficient. -/
theorem n04b_isOpen_travelDomain [TopologicalSpace X]
    {Ω : Set X} {Γ : X → PolarPoint} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hΓ : ContinuousOn Γ Ω) (hI : IsOpen I) :
    IsOpen (n04bTravelDomain Ω Γ I) :=
  hΓ.isOpen_inter_preimage hΩ (hI.prod isOpen_univ)

/-- The actual level set inside the physical domain. -/
def n04bTravelCut (Ω : Set X) (Γ : X → PolarPoint) (t : ℝ) : Set X :=
  n04bTravelDomain Ω Γ {t}

@[simp]
theorem mem_n04bTravelCut {Ω : Set X} {Γ : X → PolarPoint}
    {t : ℝ} {x : X} :
    x ∈ n04bTravelCut Ω Γ t ↔ x ∈ Ω ∧ (Γ x).1 = t := by
  simp only [n04bTravelCut, mem_n04bTravelDomain, mem_singleton_iff]

/-- One general split proves both disjointness and coverage away from the
actual level set. The physical set need not be a radial strip. -/
theorem n04b_travelDomains_split {Ω : Set X} {Γ : X → PolarPoint}
    {a c b : ℝ}
    (hΓ : MapsTo Γ Ω (Ioo a b ×ˢ (univ : Set ℝ))) :
    Disjoint (n04bTravelDomain Ω Γ (Ioo a c))
      (n04bTravelDomain Ω Γ (Ioo c b)) ∧
    n04bTravelDomain Ω Γ (Ioo a c) ∪
      n04bTravelDomain Ω Γ (Ioo c b) = Ω \ n04bTravelCut Ω Γ c := by
  refine ⟨Set.disjoint_left.mpr ?_, ?_⟩
  · intro x hx hy
    have hleft := (mem_n04bTravelDomain.mp hx).2.2
    have hright := (mem_n04bTravelDomain.mp hy).2.1
    exact (not_lt_of_ge hright.le) hleft
  · ext x
    constructor
    · rintro (hx | hx)
      · have h := mem_n04bTravelDomain.mp hx
        refine ⟨h.1, ?_⟩
        intro hcut
        exact (ne_of_lt h.2.2) (mem_n04bTravelCut.mp hcut).2
      · have h := mem_n04bTravelDomain.mp hx
        refine ⟨h.1, ?_⟩
        intro hcut
        exact (ne_of_gt h.2.1) (mem_n04bTravelCut.mp hcut).2
    · intro hx
      have hfull := hΓ hx.1
      have hne : (Γ x).1 ≠ c := by
        intro he
        exact hx.2 (mem_n04bTravelCut.mpr ⟨hx.1, he⟩)
      rcases lt_or_gt_of_ne hne with hl | hr
      · exact Or.inl (mem_n04bTravelDomain.mpr ⟨hx.1, hfull.1.1, hl⟩)
      · exact Or.inr (mem_n04bTravelDomain.mpr ⟨hx.1, hr, hfull.1.2⟩)

/-- `false` is the left travel half and `true` is the right travel half. -/
def n04bTravelHalfInterval (T : ℝ) : Bool → Set ℝ
  | false => Ioo 0 (T / 2)
  | true => Ioo (T / 2) T

/-- The physical half is represented by the same generic travel domain. -/
def n04bTravelHalfDomain (Ω : Set X) (Γ : X → PolarPoint)
    (T : ℝ) (side : Bool) : Set X :=
  n04bTravelDomain Ω Γ (n04bTravelHalfInterval T side)

theorem n04b_travelHalfInterval_subset {T : ℝ} (hT : 0 < T) (side : Bool) :
    n04bTravelHalfInterval T side ⊆ Ioo (0 : ℝ) T := by
  intro r hr
  cases side with
  | false =>
    simp only [n04bTravelHalfInterval] at hr
    exact ⟨hr.1, by linarith [hr.2]⟩
  | true =>
    simp only [n04bTravelHalfInterval] at hr
    exact ⟨by linarith [hr.1], hr.2⟩

/-- Both middle restrictions are actual bijections to their travel halves. -/
theorem n04b_bijOn_travelHalf {Ω : Set X} {Γ : X → PolarPoint}
    {T : ℝ} (hT : 0 < T)
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ))) (side : Bool) :
    BijOn Γ (n04bTravelHalfDomain Ω Γ T side)
      (n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ)) :=
  n04b_bijOn_travelDomain hΓ (n04b_travelHalfInterval_subset hT side)

theorem n04b_image_travelHalf {Ω : Set X} {Γ : X → PolarPoint}
    {T : ℝ} (hT : 0 < T)
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ))) (side : Bool) :
    Γ '' n04bTravelHalfDomain Ω Γ T side =
      n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ) :=
  (n04b_bijOn_travelHalf hT hΓ side).image_eq

theorem n04b_isOpen_travelHalf [TopologicalSpace X]
    {Ω : Set X} {Γ : X → PolarPoint} {T : ℝ}
    (hΩ : IsOpen Ω) (hΓ : ContinuousOn Γ Ω) (side : Bool) :
    IsOpen (n04bTravelHalfDomain Ω Γ T side) := by
  apply n04b_isOpen_travelDomain hΩ hΓ
  cases side <;> exact isOpen_Ioo

/-- The two physical halves omit exactly the genuine middle level. -/
theorem n04b_travelHalves_split {Ω : Set X} {Γ : X → PolarPoint} {T : ℝ}
    (hΓ : MapsTo Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ))) :
    Disjoint (n04bTravelHalfDomain Ω Γ T false)
      (n04bTravelHalfDomain Ω Γ T true) ∧
    n04bTravelHalfDomain Ω Γ T false ∪ n04bTravelHalfDomain Ω Γ T true =
      Ω \ n04bTravelCut Ω Γ (T / 2) := by
  simpa only [n04bTravelHalfDomain, n04bTravelHalfInterval] using
    (n04b_travelDomains_split (a := 0) (c := T / 2) (b := T) hΓ)

/-- The actual inverse on the full open travel strip parametrizes a cut. -/
def n04bTravelCutPoint [Nonempty X] (Ω : Set X) (Γ : X → PolarPoint)
    (t θ : ℝ) : X :=
  Function.invFunOn Γ Ω (t, θ)

/-- All inverse evaluations here lie in the canonical interior. -/
theorem n04b_travelCutPoint_spec [Nonempty X]
    {Ω : Set X} {Γ : X → PolarPoint} {T t : ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (ht : t ∈ Ioo (0 : ℝ) T) (θ : ℝ) :
    n04bTravelCutPoint Ω Γ t θ ∈ Ω ∧
      Γ (n04bTravelCutPoint Ω Γ t θ) = (t, θ) := by
  have hp : (t, θ) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
    ⟨ht, mem_univ _⟩
  exact ⟨hΓ.surjOn.mapsTo_invFunOn hp, hΓ.surjOn.rightInvOn_invFunOn hp⟩

/-- Any specified genuine inverse gives exactly the same cut points. -/
theorem n04b_travelCutPoint_eq_of_inverse [Nonempty X]
    {Ω : Set X} {Γ : X → PolarPoint} {G : PolarPoint → X} {T t : ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hFG : ∀ p ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), Γ (G p) = p)
    (ht : t ∈ Ioo (0 : ℝ) T) (θ : ℝ) :
    n04bTravelCutPoint Ω Γ t θ = G (t, θ) := by
  have hp : (t, θ) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
    ⟨ht, mem_univ _⟩
  have hcut := n04b_travelCutPoint_spec hΓ ht θ
  exact hΓ.injOn hcut.1 (hG hp) (hcut.2.trans (hFG _ hp).symm)

/-- The cut parametrization is injective as a lift, not just modulo a period. -/
theorem n04b_travelCutPoint_injective [Nonempty X]
    {Ω : Set X} {Γ : X → PolarPoint} {T t : ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (ht : t ∈ Ioo (0 : ℝ) T) :
    Function.Injective (n04bTravelCutPoint Ω Γ t) := by
  intro θ ψ he
  have hθ := (n04b_travelCutPoint_spec hΓ ht θ).2
  have hψ := (n04b_travelCutPoint_spec hΓ ht ψ).2
  have hpair : (t, θ) = (t, ψ) :=
    hθ.symm.trans ((congrArg Γ he).trans hψ)
  exact congrArg Prod.snd hpair

/-- The parametrized curve is precisely the actual physical level set. -/
theorem n04b_range_travelCutPoint [Nonempty X]
    {Ω : Set X} {Γ : X → PolarPoint} {T t : ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (ht : t ∈ Ioo (0 : ℝ) T) :
    Set.range (n04bTravelCutPoint Ω Γ t) = n04bTravelCut Ω Γ t := by
  apply Set.Subset.antisymm
  · rintro x ⟨θ, rfl⟩
    have h := n04b_travelCutPoint_spec hΓ ht θ
    exact mem_n04bTravelCut.mpr ⟨h.1, congrArg Prod.fst h.2⟩
  · intro x hx
    have h := mem_n04bTravelCut.mp hx
    refine ⟨(Γ x).2, ?_⟩
    have hcut := n04b_travelCutPoint_spec hΓ ht (Γ x).2
    have hpair : (t, (Γ x).2) = Γ x := Prod.ext h.2.symm rfl
    exact hΓ.injOn hcut.1 h.1 (hcut.2.trans hpair)

/-- The actual middle inverse curve is exactly what the two halves omit. -/
theorem n04b_travelHalves_union_rangeCutPoint [Nonempty X]
    {Ω : Set X} {Γ : X → PolarPoint} {T : ℝ} (hT : 0 < T)
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ))) :
    n04bTravelHalfDomain Ω Γ T false ∪ n04bTravelHalfDomain Ω Γ T true =
      Ω \ Set.range (n04bTravelCutPoint Ω Γ (T / 2)) := by
  have hmid : T / 2 ∈ Ioo (0 : ℝ) T := ⟨by linarith, by linarith⟩
  rw [n04b_range_travelCutPoint hΓ hmid]
  exact (n04b_travelHalves_split hΓ.mapsTo).2


/-- Actual forward/inverse identities give the bijection used by the
travel-domain restriction lemmas. -/
theorem n04b_bijOn_of_travel_inverse
    {Ω : Set X} {Γ : X → PolarPoint} {G : PolarPoint → X} {T : ℝ}
    (hΓ : MapsTo Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hGF : ∀ x ∈ Ω, G (Γ x) = x)
    (hFG : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), Γ (G q) = q) :
    BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) := by
  refine ⟨hΓ, ?_, ?_⟩
  · intro x hx y hy he
    exact (hGF x hx).symm.trans ((congrArg G he).trans (hGF y hy))
  · intro q hq
    exact ⟨G q, hG hq, hFG q hq⟩

/-- Each middle half contains an actual inverse image of an interior
travel point. A single statement handles both sides. -/
theorem n04b_travelHalfDomain_nonempty
    {Ω : Set X} {Γ : X → PolarPoint} {T : ℝ}
    (hT : 0 < T)
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ))) (side : Bool) :
    (n04bTravelHalfDomain Ω Γ T side).Nonempty := by
  have hI : (n04bTravelHalfInterval T side).Nonempty := by
    cases side with
    | false => exact ⟨T / 4, by constructor <;> linarith⟩
    | true => exact ⟨3 * T / 4, by constructor <;> linarith⟩
  obtain ⟨t, ht⟩ := hI
  have hp : (t, (0 : ℝ)) ∈ n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ) :=
    ⟨ht, mem_univ _⟩
  obtain ⟨x, hx, _⟩ := (n04b_bijOn_travelHalf hT hΓ side).surjOn hp
  exact ⟨x, hx⟩

/-- The specified actual inverse restricts to either moving half-domain. -/
theorem n04b_inverse_mapsTo_travelHalf
    {Ω : Set X} {Γ : X → PolarPoint} {G : PolarPoint → X} {T : ℝ}
    (hT : 0 < T)
    (hG : MapsTo G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hFG : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), Γ (G q) = q)
    (side : Bool) :
    MapsTo G (n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ))
      (n04bTravelHalfDomain Ω Γ T side) := by
  intro q hq
  have hq' : q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
    ⟨n04b_travelHalfInterval_subset hT side hq.1, mem_univ _⟩
  apply mem_n04bTravelDomain.mpr
  refine ⟨hG hq', ?_⟩
  simpa only [hFG q hq'] using hq.1

/-- The two actual halves together with the specified inverse trace cover
the original physical domain. The inverse is evaluated only at interior
middle-travel points. -/
theorem n04b_travelHalves_decomposition_of_inverse
    {Ω : Set X} {Γ : X → PolarPoint} {G : PolarPoint → X} {T : ℝ}
    (hT : 0 < T)
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hFG : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), Γ (G q) = q) :
    (n04bTravelHalfDomain Ω Γ T false ∪ n04bTravelHalfDomain Ω Γ T true) ∪
      Set.range (fun θ : ℝ => G (T / 2, θ)) = Ω := by
  letI : Nonempty X := ⟨G (T / 2, 0)⟩
  have hmid : T / 2 ∈ Ioo (0 : ℝ) T := ⟨half_pos hT, half_lt_self hT⟩
  have hcut : n04bTravelCutPoint Ω Γ (T / 2) =
      (fun θ : ℝ => G (T / 2, θ)) :=
    funext (n04b_travelCutPoint_eq_of_inverse hΓ hG hFG hmid)
  have hcover := n04b_travelHalves_union_rangeCutPoint hT hΓ
  rw [hcut] at hcover
  rw [hcover]
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | ⟨θ, rfl⟩
    · exact hx.1
    · exact hG ⟨hmid, mem_univ θ⟩
  · intro x hx
    by_cases hcut : x ∈ Set.range (fun θ : ℝ => G (T / 2, θ))
    · exact Or.inr hcut
    · exact Or.inl ⟨hx, hcut⟩

/-- A symmetry preserving the physical domain and the first travel
coordinate preserves every travel subdomain, hence either half. -/
theorem n04b_travelDomain_invariant
    {Ω : Set X} {Γ : X → PolarPoint} {R : X → X} {I : Set ℝ}
    (hΩ : ∀ x, R x ∈ Ω ↔ x ∈ Ω)
    (hΓ : ∀ x ∈ Ω, (Γ (R x)).1 = (Γ x).1) :
    ∀ x, R x ∈ n04bTravelDomain Ω Γ I ↔ x ∈ n04bTravelDomain Ω Γ I := by
  intro x
  simp only [mem_n04bTravelDomain]
  constructor
  · rintro ⟨hRx, hI⟩
    have hx := (hΩ x).mp hRx
    refine ⟨hx, ?_⟩
    simpa only [hΓ x hx] using hI
  · rintro ⟨hx, hI⟩
    refine ⟨(hΩ x).mpr hx, ?_⟩
    simpa only [hΓ x hx] using hI

/-- Taking period = π supplies the angular periodicity in the shared
canonical-domain contract. -/
theorem n04b_travelHalfDomain_periodic
    {Ω : Set PolarPoint} {Γ : PolarPoint → PolarPoint} {T : ℝ}
    (period : ℝ)
    (hΩ : ∀ p, p + (0, period) ∈ Ω ↔ p ∈ Ω)
    (hΓ : ∀ p ∈ Ω, Γ (p + (0, period)) = Γ p + (0, period))
    (side : Bool) :
    ∀ p, p + (0, period) ∈ n04bTravelHalfDomain Ω Γ T side ↔
      p ∈ n04bTravelHalfDomain Ω Γ T side := by
  unfold n04bTravelHalfDomain
  apply n04b_travelDomain_invariant hΩ
  intro p hp
  simpa using congrArg Prod.fst (hΓ p hp)

/-- Reflection equivariance preserves either moving half by the same
radial-coordinate invariance argument. -/
theorem n04b_travelHalfDomain_reflection
    {Ω : Set PolarPoint} {Γ : PolarPoint → PolarPoint} {T : ℝ}
    (hΩ : ∀ p, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω)
    (hΓ : ∀ p ∈ Ω, Γ (p.1, -p.2) = ((Γ p).1, -(Γ p).2))
    (side : Bool) :
    ∀ p, (p.1, -p.2) ∈ n04bTravelHalfDomain Ω Γ T side ↔
      p ∈ n04bTravelHalfDomain Ω Γ T side := by
  unfold n04bTravelHalfDomain
  apply n04b_travelDomain_invariant hΩ
  intro p hp
  simpa using congrArg Prod.fst (hΓ p hp)

end ContinuousFlexibility.Analysis
