import ContinuousFlexibility.Contracts.SphereClosedBending

/-!
# Solution: a smooth periodic isometric bending of an embedded sphere

The definitions below are copied verbatim from the independent Challenge
(`src/Challenge/FlexibleSphereChallenge.lean`); this module does not import it.

`closedBending_of_statements` transports the project's own target structure
`ContinuousFlexibility.Statements.ClosedBending` to the Challenge structure, and
`exists_closedBending_of_core` is the proved geometric half of the theorem: it reduces
the Challenge to `Nonempty ContinuousFlexibility.FlatAnnularCore`.
-/

noncomputable section

namespace FlexibleSphere

open Set MeasureTheory Bundle
open scoped ContDiff Manifold Topology ENNReal NNReal

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

instance finrankE3 : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

/-- The existing standard unit sphere, with mathlib's existing smooth structure. -/
abbrev S2 := {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

abbrev E2 := EuclideanSpace ℝ (Fin 2)

abbrev SphereTangent (x : S2) := TangentSpace (𝓡 2) x

/-- A genuine smooth positive-definite Riemannian metric on the tangent bundle. -/
abbrev SmoothSphereMetric :=
  Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ E2 (fun x : S2 => SphereTangent x)

/-- The actual manifold derivative, with the canonical target identification for E3. -/
def sphereDifferential (f : S2 → E3) (x : S2) : SphereTangent x →L[ℝ] E3 :=
  (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
    (mfderiv (𝓡 2) 𝓘(ℝ, E3) f x)

def phaseMap (F : S2 × ℝ → E3) (t : ℝ) : S2 → E3 := fun x => F (x, t)

/-- Actual normalized Hausdorff area on an embedded surface image. -/
def imageAreaMeasure (f : S2 → E3) : Measure E3 :=
  (Measure.euclideanHausdorffMeasure 2).restrict (Set.range f)

def imageArea (f : S2 → E3) : ℝ≥0∞ :=
  (Measure.euclideanHausdorffMeasure 2 : Measure E3) (Set.range f)

def outsideRegion (Ω : Set E3) : Set E3 := (closure Ω)ᶜ

/-- The normal's negative ray enters the real inside; its positive ray leaves
the entire closed inside. This is an actual outward condition. -/
def PointsOutward (Ω : Set E3) (p n : E3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, s ∈ Ioo 0 ε →
    p - s • n ∈ Ω ∧ p + s • n ∈ outsideRegion Ω

def UnitSurfaceNormal (f n : S2 → E3) : Prop :=
  ∀ x : S2, ‖n x‖ = 1 ∧
    ∀ v : SphereTangent x, inner ℝ (sphereDifferential f x v) (n x) = 0

/-- Real closed disks, including nonempty interiors and the required nesting.
The complementary cap is the complement of the graph disk's interior. -/
structure DiskRegions where
  graphDisk : Set S2
  innerDisk : Set S2
  cap : Set S2
  graph_closed : IsClosed graphDisk
  inner_closed : IsClosed innerDisk
  cap_closed : IsClosed cap
  graph_disk : Nonempty ({u : E2 // ‖u‖ ≤ 1} ≃ₜ graphDisk)
  inner_disk : Nonempty ({u : E2 // ‖u‖ ≤ 1} ≃ₜ innerDisk)
  cap_disk : Nonempty ({u : E2 // ‖u‖ ≤ 1} ≃ₜ cap)
  graph_interior : (interior graphDisk).Nonempty
  inner_interior : (interior innerDisk).Nonempty
  cap_interior : (interior cap).Nonempty
  graph_regular : closure (interior graphDisk) = graphDisk
  inner_regular : closure (interior innerDisk) = innerDisk
  cap_regular : closure (interior cap) = cap
  nested : innerDisk ⊆ interior graphDisk
  complement : cap = (interior graphDisk)ᶜ

structure FixedDiskRegions (F : S2 × ℝ → E3) extends DiskRegions where
  fixed_inner : ∀ t x, x ∈ innerDisk → F (x, t) = F (x, 0)
  fixed_cap : ∀ t x, x ∈ cap → F (x, t) = F (x, 0)

/-- A genuine tangent-space shape operator. Its value is identified by
`df ∘ S = -dn`; its symmetry is measured in the actual induced first form. -/
structure ShapeGeometry (f n : S2 → E3) where
  shape (x : S2) : SphereTangent x →L[ℝ] SphereTangent x
  smooth_shape : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E2 →L[ℝ] E2)) ∞
    (fun x => TotalSpace.mk' (E2 →L[ℝ] E2) x (shape x))
  weingarten : ∀ x (v : SphereTangent x),
    sphereDifferential f x (shape x v) = -sphereDifferential n x v
  self_adjoint : ∀ x (v w : SphereTangent x),
    inner ℝ (sphereDifferential f x (shape x v)) (sphereDifferential f x w) =
      inner ℝ (sphereDifferential f x v) (sphereDifferential f x (shape x w))
  smooth_mean : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
    (fun x => LinearMap.trace ℝ (SphereTangent x) (shape x).toLinearMap / 2)
  smooth_gaussian : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
    (fun x => LinearMap.det (shape x).toLinearMap)

def ShapeGeometry.mean {f n : S2 → E3} (G : ShapeGeometry f n) (x : S2) : ℝ :=
  LinearMap.trace ℝ (SphereTangent x) (G.shape x).toLinearMap / 2

def ShapeGeometry.gaussian {f n : S2 → E3} (G : ShapeGeometry f n) (x : S2) : ℝ :=
  LinearMap.det (G.shape x).toLinearMap

/-- Actual bounded inside regions and the actual outward unit normal for the
same family. Connectedness of both inside and unbounded outside identifies the
bounded component bounded by the image. -/
structure EnclosedRegionFamily (F : S2 × ℝ → E3) where
  region : ℝ → Set E3
  region_open : ∀ t, IsOpen (region t)
  region_bounded : ∀ t, Bornology.IsBounded (region t)
  region_connected : ∀ t, IsConnected (region t)
  frontier_eq : ∀ t, frontier (region t) = Set.range (phaseMap F t)
  exterior_connected : ∀ t, IsConnected (outsideRegion (region t))
  exterior_unbounded : ∀ t, ¬ Bornology.IsBounded (outsideRegion (region t))
  normal : S2 × ℝ → E3
  normal_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ normal
  unit_normal : ∀ t, UnitSurfaceNormal (phaseMap F t) (fun x => normal (x, t))
  outward : ∀ t x, PointsOutward (region t) (F (x, t)) (normal (x, t))

/-- Actual outward shape geometry and a scalar representative on E3. Its
off-surface values are irrelevant, and its on-surface values are forced to be
`trace(S)/2`. Thus this does not assume an arbitrary mean-curvature predicate. -/
structure OrientedEnclosedFamily (F : S2 × ℝ → E3) (g : SmoothSphereMetric)
    extends EnclosedRegionFamily F where
  geometry : ∀ t, ShapeGeometry (phaseMap F t) (fun x => normal (x, t))
  metric_self_adjoint : ∀ t x (v w : SphereTangent x),
    g.inner x ((geometry t).shape x v) w = g.inner x v ((geometry t).shape x w)
  ambientMean : ℝ → E3 → ℝ
  mean_identification : ∀ t x, ambientMean t (F (x, t)) = (geometry t).mean x

def EnclosedRegionFamily.enclosedVolume {F : S2 × ℝ → E3}
    (O : EnclosedRegionFamily F) (t : ℝ) : ℝ≥0∞ :=
  (volume : Measure E3) (O.region t)

def OrientedEnclosedFamily.totalMean {F : S2 × ℝ → E3} {g : SmoothSphereMetric}
    (O : OrientedEnclosedFamily F g) (t : ℝ) : ℝ :=
  ∫ y, O.ambientMean t y ∂imageAreaMeasure (phaseMap F t)

/-- Full target of `paper/flexible-surface-rewrite/01-introduction.tex:18–39`,
including all geometric quantities with their actual definitions. -/
structure ClosedBending where
  metric : SmoothSphereMetric
  family : S2 × ℝ → E3
  joint_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ family
  phase_embedding : ∀ t, Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ (phaseMap family t)
  same_metric : ∀ t x (v w : SphereTangent x),
    inner ℝ (sphereDifferential (phaseMap family t) x v)
      (sphereDifferential (phaseMap family t) x w) = metric.inner x v w
  periodic : ∀ x t, family (x, t + 1) = family (x, t)
  fixed_regions : FixedDiskRegions family
  noncongruent : ∃ s t : ℝ, ∀ A : E3 ≃ᵃⁱ[ℝ] E3,
    A '' Set.range (phaseMap family s) ≠ Set.range (phaseMap family t)
  enclosed : OrientedEnclosedFamily family metric
  area_finite : ∀ t, imageArea (phaseMap family t) < (⊤ : ℝ≥0∞)
  area_positive : ∀ t, 0 < imageArea (phaseMap family t)
  area_constant : ∀ t, imageArea (phaseMap family t) = imageArea (phaseMap family 0)
  volume_finite : ∀ t, enclosed.toEnclosedRegionFamily.enclosedVolume t < (⊤ : ℝ≥0∞)
  volume_positive : ∀ t, 0 < enclosed.toEnclosedRegionFamily.enclosedVolume t
  volume_constant : ∀ t,
    enclosed.toEnclosedRegionFamily.enclosedVolume t =
      enclosed.toEnclosedRegionFamily.enclosedVolume 0
  mean_integrable : ∀ t,
    Integrable (enclosed.ambientMean t) (imageAreaMeasure (phaseMap family t))
  mean_constant : ∀ t, enclosed.totalMean t = enclosed.totalMean 0

open ContinuousFlexibility in
/-- The project's target structure is the Challenge structure. -/
def closedBending_of_statements (B : Statements.ClosedBending) : ClosedBending where
  metric := B.metric
  family := B.family
  joint_smooth := B.joint_smooth
  phase_embedding := B.phase_embedding
  same_metric := B.same_metric
  periodic := B.periodic
  fixed_regions :=
    { graphDisk := B.fixed_regions.graphDisk
      innerDisk := B.fixed_regions.innerDisk
      cap := B.fixed_regions.cap
      graph_closed := B.fixed_regions.graph_closed
      inner_closed := B.fixed_regions.inner_closed
      cap_closed := B.fixed_regions.cap_closed
      graph_disk := B.fixed_regions.graph_disk
      inner_disk := B.fixed_regions.inner_disk
      cap_disk := B.fixed_regions.cap_disk
      graph_interior := B.fixed_regions.graph_interior
      inner_interior := B.fixed_regions.inner_interior
      cap_interior := B.fixed_regions.cap_interior
      graph_regular := B.fixed_regions.graph_regular
      inner_regular := B.fixed_regions.inner_regular
      cap_regular := B.fixed_regions.cap_regular
      nested := B.fixed_regions.nested
      complement := B.fixed_regions.complement
      fixed_inner := B.fixed_regions.fixed_inner
      fixed_cap := B.fixed_regions.fixed_cap }
  noncongruent := B.noncongruent
  enclosed :=
    { region := B.enclosed.region
      region_open := B.enclosed.region_open
      region_bounded := B.enclosed.region_bounded
      region_connected := B.enclosed.region_connected
      frontier_eq := B.enclosed.frontier_eq
      exterior_connected := B.enclosed.exterior_connected
      exterior_unbounded := B.enclosed.exterior_unbounded
      normal := B.enclosed.normal
      normal_smooth := B.enclosed.normal_smooth
      unit_normal := B.enclosed.unit_normal
      outward := B.enclosed.outward
      geometry := fun t =>
        { shape := (B.enclosed.geometry t).shape
          smooth_shape := (B.enclosed.geometry t).smooth_shape
          weingarten := (B.enclosed.geometry t).weingarten
          self_adjoint := (B.enclosed.geometry t).self_adjoint
          smooth_mean := (B.enclosed.geometry t).smooth_mean
          smooth_gaussian := (B.enclosed.geometry t).smooth_gaussian }
      metric_self_adjoint := B.enclosed.metric_self_adjoint
      ambientMean := B.enclosed.ambientMean
      mean_identification := B.enclosed.mean_identification }
  area_finite := B.area_finite
  area_positive := B.area_positive
  area_constant := B.area_constant
  volume_finite := B.volume_finite
  volume_positive := B.volume_positive
  volume_constant := B.volume_constant
  mean_integrable := B.mean_integrable
  mean_constant := B.mean_constant

/-- The geometric half of `thm:main`: an annular core gives the Challenge statement. -/
theorem exists_closedBending_of_core
    (hcore : Nonempty ContinuousFlexibility.FlatAnnularCore) : Nonempty ClosedBending := by
  obtain ⟨B⟩ := ContinuousFlexibility.mainStatement_of_flatAnnularCore hcore
  exact ⟨closedBending_of_statements B⟩

end FlexibleSphere
