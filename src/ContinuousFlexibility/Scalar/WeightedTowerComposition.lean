module

public import ContinuousFlexibility.Scalar.WeightedTowerCompositionBounds
public import ContinuousFlexibility.Analysis.TameComposition

/-!
# Fixed-loss composition on the original open domain

The derivative family is the main library's actual ordered-partition
composition tower.  A uniform bound on one fixed source seminorm suffices
to add the two losses, without any dependence of the base or loss on the
directional derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis
open scoped BigOperators

section ProjectiveComposition

variable {E F G : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)]
  [∀ n, CompleteSpace (G n)]
  {e : ∀ n, E (n + 1) →L[ℝ] E n}
  {f : ∀ n, F (n + 1) →L[ℝ] F n}
  {g : ∀ n, G (n + 1) →L[ℝ] G n}
  {u : ProjectiveLimit E e → ProjectiveLimit F f}
  {v : ProjectiveLimit F f → ProjectiveLimit G g}
  {U : Set (ProjectiveLimit E e)} {V : Set (ProjectiveLimit F f)}
  {p : ℕ → Seminorm ℝ (ProjectiveLimit E e)}
  {q : ℕ → Seminorm ℝ (ProjectiveLimit F f)}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit G g)}
  {b c ell m : ℕ}

/-- The genuine partition tower of a composition, on the same source open
set as the original inner tower. -/
def smoothDirectionsUniformComp
    (J : SmoothDirections U u) (K : SmoothDirections V v) (hmap : MapsTo u U V) :
    SmoothDirections U (v ∘ u) :=
  smoothDirectionsOfJets J.open_domain (projectiveCompositionJets u J.D K.D)
    (HasProjectiveJetsOn.comp J.open_domain K.open_domain
      J.hasProjectiveJetsOn K.hasProjectiveJetsOn hmap)

theorem smoothDirectionsUniformComp_D
    (J : SmoothDirections U u) (K : SmoothDirections V v) (hmap : MapsTo u U V)
    (k : ℕ) (x : ProjectiveLimit E e) (w : Fin k → ProjectiveLimit E e) :
    (smoothDirectionsUniformComp J K hmap).D k x w =
      projectiveCompositionJets u J.D K.D k x w := rfl

/-- Uniform towers compose with the sum of their fixed losses.  The source
base is enlarged once to control every low inner block. -/
theorem UniformScalarTowerEstimate.comp
    {J : SmoothDirections U u} {K : SmoothDirections V v}
    (hJ : UniformScalarTowerEstimate p q U b ell u J)
    (hK : UniformScalarTowerEstimate q r V c m v K)
    (hp : Monotone p) (hq : Monotone q) (hmap : MapsTo u U V)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ U, p (max b c + ell) x ≤ R) :
    UniformScalarTowerEstimate p r U (max b c + ell) (ell + m)
      (v ∘ u) (smoothDirectionsUniformComp J K hmap) := by
  intro k s hs
  obtain ⟨C, hC, hCx⟩ :=
    uniformScalarCompositionJets_bound hp hq J K hJ hK hmap hR hxR k s hs
  refine ⟨C, hC, fun x hx w => ?_⟩
  rw [smoothDirectionsUniformComp_D]
  exact hCx x hx w

/-- Fixed-neighborhood smooth tameness is closed under genuine composition
when the required single low source seminorm is bounded on that neighborhood. -/
theorem FixedNeighborhoodSmoothTame.comp
    (hu : FixedNeighborhoodSmoothTame p q U b ell u)
    (hv : FixedNeighborhoodSmoothTame q r V c m v)
    (hp : Monotone p) (hq : Monotone q) (hmap : MapsTo u U V)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ U, p (max b c + ell) x ≤ R) :
    FixedNeighborhoodSmoothTame p r U (max b c + ell) (ell + m) (v ∘ u) := by
  obtain ⟨J, hJ⟩ := hu.2
  obtain ⟨K, hK⟩ := hv.2
  exact fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsUniformComp J K hmap)
    (hJ.comp hK hp hq hmap hR hxR)

end ProjectiveComposition

end ContinuousFlexibility.Statements
