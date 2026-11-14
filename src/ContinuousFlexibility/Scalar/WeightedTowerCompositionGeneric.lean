module

public import ContinuousFlexibility.Scalar.WeightedTowerCompositionBounds
public import ContinuousFlexibility.Scalar.WeightedGenericJetComposition

/-!
# Uniform composition for nested scalar state domains

The source may be any topological real module and the intermediate space any
locally convex real module.  This includes finite products of the actual
weighted height model and scalar parameters, with their original topologies.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
  {fbond : ∀ n, F (n + 1) →L[ℝ] F n}
  {u : X → Y} {v : Y → ProjectiveLimit F fbond}
  {U : Set X} {V : Set Y}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit F fbond)}
  {b c ell m : ℕ}

def smoothDirectionsUniformCompGeneric
    (J : SmoothDirections U u) (K : SmoothDirections V v) (hmap : MapsTo u U V) :
    SmoothDirections U (v ∘ u) :=
  smoothDirectionsOfJets J.open_domain (projectiveCompositionJets u J.D K.D)
    (HasProjectiveJetsOn.comp_generic J.open_domain K.open_domain
      J.hasProjectiveJetsOn K.hasProjectiveJetsOn hmap)

theorem smoothDirectionsUniformCompGeneric_D
    (J : SmoothDirections U u) (K : SmoothDirections V v) (hmap : MapsTo u U V)
    (k : ℕ) (x : X) (w : Fin k → X) :
    (smoothDirectionsUniformCompGeneric J K hmap).D k x w =
      projectiveCompositionJets u J.D K.D k x w := rfl

/-- Uniform actual towers compose on the same open source domain, with one
fixed enlarged base and the sum of the two fixed losses. -/
theorem UniformScalarTowerEstimate.comp_generic
    {J : SmoothDirections U u} {K : SmoothDirections V v}
    (hJ : UniformScalarTowerEstimate p q U b ell u J)
    (hK : UniformScalarTowerEstimate q r V c m v K)
    (hp : Monotone p) (hq : Monotone q) (hmap : MapsTo u U V)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ U, p (max b c + ell) x ≤ R) :
    UniformScalarTowerEstimate p r U (max b c + ell) (ell + m)
      (v ∘ u) (smoothDirectionsUniformCompGeneric J K hmap) := by
  intro k s hs
  obtain ⟨C, hC, hCx⟩ :=
    uniformScalarCompositionJets_bound hp hq J K hJ hK hmap hR hxR k s hs
  refine ⟨C, hC, fun x hx w => ?_⟩
  rw [smoothDirectionsUniformCompGeneric_D]
  exact hCx x hx w

theorem FixedNeighborhoodSmoothTame.comp_generic
    (hu : FixedNeighborhoodSmoothTame p q U b ell u)
    (hv : FixedNeighborhoodSmoothTame q r V c m v)
    (hp : Monotone p) (hq : Monotone q) (hmap : MapsTo u U V)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ U, p (max b c + ell) x ≤ R) :
    FixedNeighborhoodSmoothTame p r U (max b c + ell) (ell + m) (v ∘ u) := by
  obtain ⟨J, hJ⟩ := hu.2
  obtain ⟨K, hK⟩ := hv.2
  exact fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsUniformCompGeneric J K hmap)
    (hJ.comp_generic hK hp hq hmap hR hxR)

end ContinuousFlexibility.Statements
