module

public import ContinuousFlexibility.Analysis.N04RealizationUniformAffine

/-!
# Abstract transport of a retained uniform family

The full affine pullback, neighborhood choice, and existential witness
assembly are performed over abstract graded spaces. The concrete
geometry enters only through the supplied decoder predicates and the
already proved neighborhood restriction operation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

/-- Preserve the supplied family, its affine map, and its decoded
property while making one common neighborhood choice. -/
theorem n04Realization_uniformAffine_family
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (r : ℕ → Seminorm ℝ Z)
    (c : Y) (L : X →L[ℝ] Y) (hL : ∀ n x, q n (L x) ≤ p n x)
    (V : ℕ → ℝ → Set X) (base : ℕ) (ε : ℝ)
    (P : Set Y → (Y → Z) → Prop) (Q : ℕ → ℝ → (X → Z) → Prop)
    (hrestrict : ∀ (W : Set X) (f : X → Z) (b ell : ℕ),
      IsOpen W → (0 : X) ∈ W → FixedNeighborhoodSmoothTame p r W b ell f →
      ∃ b' : ℕ, ∃ η : ℝ, base ≤ b' ∧ 0 < η ∧ η ≤ ε ∧ V b' η ⊆ W ∧
        FixedNeighborhoodSmoothTame p r (V b' η) b' ell f)
    (htransport : ∀ (U : Set Y) (N : Y → Z), P U N →
      ∀ (b : ℕ) (η : ℝ), base ≤ b → 0 < η → η ≤ ε →
        V b η ⊆ (fun x => c + L x) ⁻¹' U →
        Q b η (fun x => N (c + L x)))
    (hseed : ∃ U : Set Y, IsOpen U ∧ c ∈ U ∧
      ∃ b ell : ℕ, ∃ N : Y → Z,
        FixedNeighborhoodSmoothTame q r U b ell N ∧ P U N) :
    ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ N : X → Z, FixedNeighborhoodSmoothTame p r (V b η) b ell N ∧ Q b η N := by
  obtain ⟨U, hU, hc, b₀, ell, N, hN, hP⟩ := hseed
  have hA : Continuous (fun x => c + L x) := continuous_const.add L.continuous
  have hzero : (0 : X) ∈ (fun x => c + L x) ⁻¹' U := by
    rw [Set.mem_preimage, ContinuousLinearMap.map_zero, add_zero]
    exact hc
  have hpull : FixedNeighborhoodSmoothTame p r
      ((fun x => c + L x) ⁻¹' U) b₀ ell (fun x => N (c + L x)) :=
    n04Realization_fixedNeighborhood_affine hN c L hL
  obtain ⟨b, η, hb, hη, hηε, hmap, htower⟩ :=
    hrestrict ((fun x => c + L x) ⁻¹' U) (fun x => N (c + L x)) b₀ ell
      (hU.preimage hA) hzero hpull
  exact ⟨b, ell, η, hb, hη, hηε, fun x => N (c + L x), htower,
    htransport U N hP b η hb hη hηε hmap⟩

end ContinuousFlexibility.Analysis
