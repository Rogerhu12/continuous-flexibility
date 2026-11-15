module

public import ContinuousFlexibility.Contracts.SphereClosedBending
public import ContinuousFlexibility.Blueprint.Assembly

/-!
# Solution: a smooth periodic isometric bending of an embedded sphere

The definitions below are copied verbatim from the independent Challenge
(`src/Challenge/FlexibleSphereChallenge.lean`); this module does not import it.

`closedBending_of_statements` transports the project's own target structure
`ContinuousFlexibility.Statements.ClosedBending` to the Challenge structure, and
`exists_closedBending_of_core` is the proved geometric half of the theorem: it reduces
the Challenge to `Nonempty ContinuousFlexibility.FlatAnnularCore`.

`exists_closedBending` is the Challenge theorem, assembled from the blueprint
(`ContinuousFlexibility.Blueprint`). It depends only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

@[expose] public section

noncomputable section

namespace FlexibleSphere

open Set MeasureTheory
open scoped ContDiff Manifold ENNReal

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

instance finrankE3 : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

/-- The unit sphere of `E3`, with Mathlib's smooth structure. -/
abbrev S2 := {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

instance nonemptyS2 : Nonempty S2 := ⟨⟨EuclideanSpace.single 2 1, by simp⟩⟩

/-- The model space of `S2`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

abbrev SphereTangent (x : S2) := TangentSpace (𝓡 2) x

/-- Smooth Riemannian metrics on `S2`. -/
abbrev SmoothSphereMetric :=
  Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ E2 (fun x : S2 => SphereTangent x)

/-- The differential of `f` at `x`, with values in `E3`. -/
def sphereDifferential (f : S2 → E3) (x : S2) : SphereTangent x →L[ℝ] E3 :=
  (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
    (mfderiv (𝓡 2) 𝓘(ℝ, E3) f x)

/-- The phase `t` of a family. -/
def phaseMap (F : S2 × ℝ → E3) (t : ℝ) : S2 → E3 := fun x => F (x, t)

/-- Two-dimensional Hausdorff measure on the image of `f`. -/
def imageAreaMeasure (f : S2 → E3) : Measure E3 :=
  (Measure.euclideanHausdorffMeasure 2).restrict (range f)

/-- The area of the image of `f`. -/
def imageArea (f : S2 → E3) : ℝ≥0∞ := imageAreaMeasure f univ

def outsideRegion (Ω : Set E3) : Set E3 := (closure Ω)ᶜ

/-- `n` points out of `Ω` at `p`: for small `s > 0`, `p - s • n` lies in `Ω` and
`p + s • n` lies outside the closure of `Ω`. -/
def PointsOutward (Ω : Set E3) (p n : E3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, s ∈ Ioo 0 ε →
    p - s • n ∈ Ω ∧ p + s • n ∈ outsideRegion Ω

/-- `n x` is a unit vector orthogonal to the image of the differential of `f` at `x`. -/
def UnitSurfaceNormal (f n : S2 → E3) : Prop :=
  ∀ x : S2, ‖n x‖ = 1 ∧
    ∀ v : SphereTangent x, inner ℝ (sphereDifferential f x v) (n x) = 0

/-- An inner disk and a complementary cap, both fixed pointwise by `F`. Each of `graphDisk`,
`innerDisk` and `cap` is homeomorphic to the closed unit disk and is the closure of its
interior; the inner disk lies in the interior of `graphDisk`, and the cap is the complement
of that interior. -/
structure FixedDiskRegions (F : S2 × ℝ → E3) where
  graphDisk : Set S2
  innerDisk : Set S2
  cap : Set S2
  graph_disk : Nonempty ({u : E2 // ‖u‖ ≤ 1} ≃ₜ graphDisk)
  inner_disk : Nonempty ({u : E2 // ‖u‖ ≤ 1} ≃ₜ innerDisk)
  cap_disk : Nonempty ({u : E2 // ‖u‖ ≤ 1} ≃ₜ cap)
  graph_regular : closure (interior graphDisk) = graphDisk
  inner_regular : closure (interior innerDisk) = innerDisk
  cap_regular : closure (interior cap) = cap
  nested : innerDisk ⊆ interior graphDisk
  complement : cap = (interior graphDisk)ᶜ
  fixed_inner : ∀ t x, x ∈ innerDisk → F (x, t) = F (x, 0)
  fixed_cap : ∀ t x, x ∈ cap → F (x, t) = F (x, 0)

/-- The shape operator of `f` for the normal `n`: `df ∘ S = -dn`, self-adjoint for the
first fundamental form. -/
structure ShapeGeometry (f n : S2 → E3) where
  shape (x : S2) : SphereTangent x →L[ℝ] SphereTangent x
  weingarten : ∀ x (v : SphereTangent x),
    sphereDifferential f x (shape x v) = -sphereDifferential n x v
  self_adjoint : ∀ x (v w : SphereTangent x),
    inner ℝ (sphereDifferential f x (shape x v)) (sphereDifferential f x w) =
      inner ℝ (sphereDifferential f x v) (sphereDifferential f x (shape x w))

/-- The mean curvature, half the trace of the shape operator. -/
def ShapeGeometry.mean {f n : S2 → E3} (G : ShapeGeometry f n) (x : S2) : ℝ :=
  LinearMap.trace ℝ (SphereTangent x) (G.shape x).toLinearMap / 2

/-- For every phase of `F`: the bounded region enclosed by the image, the outward unit
normal and its shape operator. Connectedness of the region and of its unbounded exterior
identifies the region as the inside of the image. -/
structure EnclosedFamily (F : S2 × ℝ → E3) where
  region : ℝ → Set E3
  region_open : ∀ t, IsOpen (region t)
  region_bounded : ∀ t, Bornology.IsBounded (region t)
  region_connected : ∀ t, IsConnected (region t)
  frontier_eq : ∀ t, frontier (region t) = range (phaseMap F t)
  exterior_connected : ∀ t, IsConnected (outsideRegion (region t))
  exterior_unbounded : ∀ t, ¬ Bornology.IsBounded (outsideRegion (region t))
  normal : S2 × ℝ → E3
  normal_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ normal
  unit_normal : ∀ t, UnitSurfaceNormal (phaseMap F t) (fun x => normal (x, t))
  outward : ∀ t x, PointsOutward (region t) (F (x, t)) (normal (x, t))
  geometry : ∀ t, ShapeGeometry (phaseMap F t) (fun x => normal (x, t))

/-- The enclosed volume at phase `t`. -/
def EnclosedFamily.enclosedVolume {F : S2 × ℝ → E3} (O : EnclosedFamily F) (t : ℝ) :
    ℝ≥0∞ :=
  (volume : Measure E3) (O.region t)

/-- The mean curvature at phase `t` as a function on the image: a point `y` of the image
is read at its preimage `Function.invFun (phaseMap F t) y`. -/
def EnclosedFamily.imageMean {F : S2 × ℝ → E3} (O : EnclosedFamily F) (t : ℝ) (y : E3) :
    ℝ :=
  (O.geometry t).mean (Function.invFun (phaseMap F t) y)

/-- The total mean curvature at phase `t`. -/
def EnclosedFamily.totalMean {F : S2 × ℝ → E3} (O : EnclosedFamily F) (t : ℝ) : ℝ :=
  ∫ y, O.imageMean t y ∂imageAreaMeasure (phaseMap F t)

/-- The statement of `thm:main`. -/
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
    A '' range (phaseMap family s) ≠ range (phaseMap family t)
  enclosed : EnclosedFamily family
  area_finite : ∀ t, imageArea (phaseMap family t) < ⊤
  area_constant : ∀ t, imageArea (phaseMap family t) = imageArea (phaseMap family 0)
  volume_constant : ∀ t, enclosed.enclosedVolume t = enclosed.enclosedVolume 0
  mean_integrable : ∀ t, Integrable (enclosed.imageMean t) (imageAreaMeasure (phaseMap family t))
  mean_constant : ∀ t, enclosed.totalMean t = enclosed.totalMean 0

/-- The area of an image is its two-dimensional Hausdorff measure. -/
theorem imageArea_eq_hausdorff (f : S2 → E3) :
    imageArea f = (Measure.euclideanHausdorffMeasure 2 : Measure E3) (range f) := by
  rw [imageArea, imageAreaMeasure, Measure.restrict_apply_univ]

open ContinuousFlexibility in
theorem continuous_phaseMap_of_statements (B : Statements.ClosedBending) (t : ℝ) :
    Continuous (phaseMap B.family t) :=
  B.joint_smooth.continuous.comp (Continuous.prodMk_left t)

open ContinuousFlexibility in
/-- The project's enclosed regions, outward normal and shape operator. -/
def enclosedFamily_of_statements (B : Statements.ClosedBending) : EnclosedFamily B.family where
  region := B.enclosed.region
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
      weingarten := (B.enclosed.geometry t).weingarten
      self_adjoint := (B.enclosed.geometry t).self_adjoint }

open ContinuousFlexibility in
/-- On the image, the project's ambient representative of the mean curvature is the mean
curvature read at the preimage. -/
theorem ambientMean_ae_eq_imageMean (B : Statements.ClosedBending) (t : ℝ) :
    B.enclosed.ambientMean t =ᵐ[imageAreaMeasure (phaseMap B.family t)]
      (enclosedFamily_of_statements B).imageMean t := by
  have hmeas : MeasurableSet (range (phaseMap B.family t)) :=
    (isCompact_range (continuous_phaseMap_of_statements B t)).isClosed.measurableSet
  rw [imageAreaMeasure]
  refine ae_restrict_of_forall_mem hmeas fun y hy => ?_
  have hpre : phaseMap B.family t (Function.invFun (phaseMap B.family t) y) = y :=
    Function.invFun_eq hy
  calc B.enclosed.ambientMean t y
      = B.enclosed.ambientMean t (B.family (Function.invFun (phaseMap B.family t) y, t)) :=
        (congrArg (B.enclosed.ambientMean t) hpre).symm
    _ = (enclosedFamily_of_statements B).imageMean t y :=
        B.enclosed.mean_identification t (Function.invFun (phaseMap B.family t) y)

open ContinuousFlexibility in
/-- The project's target structure gives the Challenge structure. -/
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
      graph_disk := B.fixed_regions.graph_disk
      inner_disk := B.fixed_regions.inner_disk
      cap_disk := B.fixed_regions.cap_disk
      graph_regular := B.fixed_regions.graph_regular
      inner_regular := B.fixed_regions.inner_regular
      cap_regular := B.fixed_regions.cap_regular
      nested := B.fixed_regions.nested
      complement := B.fixed_regions.complement
      fixed_inner := B.fixed_regions.fixed_inner
      fixed_cap := B.fixed_regions.fixed_cap }
  noncongruent := B.noncongruent
  enclosed := enclosedFamily_of_statements B
  area_finite := fun t => by
    rw [imageArea_eq_hausdorff]
    exact B.area_finite t
  area_constant := fun t => by
    rw [imageArea_eq_hausdorff, imageArea_eq_hausdorff]
    exact B.area_constant t
  volume_constant := B.volume_constant
  mean_integrable := fun t => (B.mean_integrable t).congr (ambientMean_ae_eq_imageMean B t)
  mean_constant := fun t =>
    (integral_congr_ae (ambientMean_ae_eq_imageMean B t)).symm.trans
      ((B.mean_constant t).trans (integral_congr_ae (ambientMean_ae_eq_imageMean B 0)))

/-- The geometric half of `thm:main`: an annular core gives the Challenge statement. -/
theorem exists_closedBending_of_core
    (hcore : Nonempty ContinuousFlexibility.FlatAnnularCore) : Nonempty ClosedBending := by
  obtain ⟨B⟩ := ContinuousFlexibility.mainStatement_of_flatAnnularCore hcore
  exact ⟨closedBending_of_statements B⟩

/-- `thm:main`, assembled from the blueprint. -/
theorem exists_closedBending : Nonempty ClosedBending :=
  exists_closedBending_of_core ContinuousFlexibility.Blueprint.flatAnnularCore_nonempty

end FlexibleSphere
