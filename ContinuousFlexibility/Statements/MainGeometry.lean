import ContinuousFlexibility.Geometry.SphereCapGluing
import ContinuousFlexibility.Geometry.SurfaceReparametrization
import ContinuousFlexibility.Contracts.GraphFamilyCurvature
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Trace

/-!
# Actual geometric statements for the full closed-sphere theorem

This module defines targets. In particular, `MAINStatement` is an unconditional
existence proposition, not a theorem proving that proposition. No analytic core,
cap, inverse, or implicit-function conclusion is a hypothesis of that target.

The sphere and the model are exactly those used by `SphereCoordinates` and
`SphereCapGluing`. Area is normalized Euclidean two-dimensional Hausdorff measure
on the actual image. The signed mean curvature is forced by the genuine normal
derivative and the tangent-space shape operator, rather than supplied as an
unidentified scalar invariant.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Bundle
open scoped ContDiff Manifold Topology ENNReal NNReal

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

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

/-- The unconditional complete theorem target; no existence proof is asserted. -/
def MainStatement : Prop := Nonempty ClosedBending

/-- Blueprint MAIN, corresponding to `thm:main` in the introduction. -/
abbrev MAINStatement : Prop := MainStatement

/-- Blueprint C00: the full geometric contract is the actual complete target. -/
abbrev C00Statement : Prop := MainStatement

structure SphereReparametrization where
  toHomeomorph : S2 ≃ₜ S2
  smooth : ContMDiff (𝓡 2) (𝓡 2) ∞ (toHomeomorph : S2 → S2)
  smooth_inverse : ContMDiff (𝓡 2) (𝓡 2) ∞ (toHomeomorph.symm : S2 → S2)

/-- The actual ambient tangent eigenspace of the actual shape operator. -/
def ShapeGeometry.principalSpace {f n : S2 → E3} (G : ShapeGeometry f n)
    (x : S2) (κ : ℝ) : Submodule ℝ E3 :=
  (LinearMap.ker ((G.shape x).toLinearMap - κ • LinearMap.id)).map
    (sphereDifferential f x).toLinearMap

/-- Global second-order geometry, including genuine naturality and principal
directions, for actual smooth sphere embeddings. -/
def GlobalSecondOrderGeometryStatement : Prop :=
  ∀ f n : S2 → E3,
  Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f →
  ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ n → UnitSurfaceNormal f n →
  ∃ G : ShapeGeometry f n,
    (∀ a : E3 ≃ᵃⁱ[ℝ] E3,
      ∃ G' : ShapeGeometry (fun x => a (f x)) (fun x => a.linearIsometryEquiv (n x)),
        ∀ x (v : SphereTangent x), G'.shape x v = G.shape x v) ∧
    (∀ e : SphereReparametrization,
      ∃ G' : ShapeGeometry (fun x => f (e.toHomeomorph x))
          (fun x => n (e.toHomeomorph x)),
        (∀ x (v : SphereTangent x),
          mfderiv (𝓡 2) (𝓡 2) (e.toHomeomorph : S2 → S2) x (G'.shape x v) =
            G.shape (e.toHomeomorph x)
              (mfderiv (𝓡 2) (𝓡 2) (e.toHomeomorph : S2 → S2) x v)) ∧
        (∀ x, G'.mean x = G.mean (e.toHomeomorph x)) ∧
        ∀ x, G'.gaussian x = G.gaussian (e.toHomeomorph x)) ∧
    (∀ (x : S2) (κ₁ κ₂ : ℝ) (u v : SphereTangent x), κ₁ ≠ κ₂ → u ≠ 0 → v ≠ 0 →
      G.shape x u = κ₁ • u → G.shape x v = κ₂ • v →
      inner ℝ (sphereDifferential f x u) (sphereDifferential f x v) = 0 ∧
      Submodule.span ℝ {sphereDifferential f x u, sphereDifferential f x v} =
        LinearMap.range (sphereDifferential f x).toLinearMap)

/-- The graph formulas use the real first/second forms, not named curvature predicates. -/
def GraphCurvatureFormulasStatement : Prop := ∀ z : PolarPoint → ℝ,
  ContDiff ℝ ∞ z → ∀ x : PolarPoint,
    surfaceGaussianCurvature (graphMap id z) (graphUpwardNormal z x) x =
      (graphHessian z x).det / graphAreaSq z x ^ 2 ∧
    surfaceMeanCurvature (graphMap id z) (graphUpwardNormal z x) x =
      ((1 + angularPartial z x ^ 2) * graphHessian z x 0 0 -
        2 * radialPartial z x * angularPartial z x * graphHessian z x 0 1 +
        (1 + radialPartial z x ^ 2) * graphHessian z x 1 1) /
      (2 * graphAreaSq z x * graphAreaDensity z x)

/-- D01; §2 marker geometry and the introduction's signed H convention. -/
def D01Statement : Prop :=
  GlobalSecondOrderGeometryStatement ∧ GraphCurvatureFormulasStatement

/-- Actual Euclidean area density in a planar parameterization. -/
def parameterAreaDensity (f : PolarPoint → E3) (x : PolarPoint) : ℝ :=
  Real.sqrt (surfaceGram f x).det

/-- Full local image area and scalar-integral formulas for any injective
immersion on an open set, with the standard normalized Euclidean area. -/
def ParametrizedImageAreaFormulaStatement : Prop := ∀ U : Set PolarPoint, IsOpen U →
  ∀ f : PolarPoint → E3, ContDiffOn ℝ ∞ f U → Set.InjOn f U →
  (∀ x ∈ U, Function.Injective (fderiv ℝ f x)) →
  ∀ s : Set PolarPoint, MeasurableSet s → s ⊆ U →
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (parameterAreaDensity f x) ∂volume ∧
    ∀ h : E3 → ℝ,
      IntegrableOn h (f '' s) (Measure.euclideanHausdorffMeasure 2) →
      IntegrableOn (fun x => h (f x) * parameterAreaDensity f x) s volume ∧
      (∫ y in f '' s, h y ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3)) =
        ∫ x in s, h (f x) * parameterAreaDensity f x ∂volume

/-- Global actual image area and integral transport; finite-chart independence
is secured by identifying every parameter integral with this same image measure. -/
def GlobalSurfaceIntegrationStatement : Prop :=
  (∀ f : S2 → E3, Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f →
    0 < imageArea f ∧ imageArea f < (⊤ : ℝ≥0∞)) ∧
  (∀ f : S2 → E3, Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f →
    ∀ a : E3 ≃ᵃⁱ[ℝ] E3,
      Measure.map a (imageAreaMeasure f) = imageAreaMeasure (fun x => a (f x))) ∧
  (∀ f : S2 → E3, Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f →
    ∀ h : E3 → ℝ, Integrable h (imageAreaMeasure f) →
      ∀ s t : Set E3, MeasurableSet s → MeasurableSet t → Disjoint s t →
        (∫ y in s ∪ t, h y ∂imageAreaMeasure f) =
          (∫ y in s, h y ∂imageAreaMeasure f) +
          ∫ y in t, h y ∂imageAreaMeasure f) ∧
  (∀ f n : S2 → E3,
    Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f →
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ n → UnitSurfaceNormal f n →
    ∀ G : ShapeGeometry f n, ∀ h : E3 → ℝ,
      (∀ x, h (f x) = G.mean x) → Integrable h (imageAreaMeasure f) ∧
      ∀ a : E3 ≃ᵃⁱ[ℝ] E3, ∀ h' : E3 → ℝ,
        (∀ x, h' (a (f x)) = G.mean x) →
          (∫ y, h' y ∂imageAreaMeasure (fun x => a (f x))) =
            ∫ y, h y ∂imageAreaMeasure f)

/-- D02; §2 actual image area, chart-independent integration, and signed H transport. -/
def D02Statement : Prop :=
  ParametrizedImageAreaFormulaStatement ∧ GlobalSurfaceIntegrationStatement

/-! ## Actual local-to-global geometric milestone targets -/

/-- The local development condition does not assume a homeomorphism or a
global inverse. The metric is the actual Cartesian remainder of the core. -/
def NormalizedPlanarDevelopment (A : FlatAnnularCore) (P : PolarPoint → PolarPoint) : Prop :=
  ContDiff ℝ ∞ P ∧
  (∀ x, A.b < cartesianRadius x → P x = x) ∧
  (∀ x u v, coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) =
    cartesianRemainder A.w A.cartesianHeight x u v) ∧
  ∀ x, 0 < planeJacobian P x

/-- Principal directions are actual tangent images satisfying the generalized
eigenvector equation II(u,w)=κ I(u,w), not merely coordinate Hessian entries. -/
def HasDistinctPrincipalDirections (C : PolarPoint → E3) (N : E3) (p : PolarPoint) : Prop :=
  ∃ κ₁ κ₂ : ℝ, ∃ u v : PolarPoint, κ₁ ≠ κ₂ ∧
    ‖fderiv ℝ C p u‖ = 1 ∧ ‖fderiv ℝ C p v‖ = 1 ∧
    inner ℝ (fderiv ℝ C p u) (fderiv ℝ C p v) = 0 ∧
    (∀ w, surfaceSecondForm C N p u w = κ₁ * surfaceFirstForm C p u w) ∧
    (∀ w, surfaceSecondForm C N p v w = κ₂ * surfaceFirstForm C p v w)

/-- The full fixed-cap output, including its actual map, bottom, open collar,
global marker comparison with all graph phases, and genuine principal data. -/
structure FixedMarkedCap {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R : ℝ) where
  length : ℝ
  length_pos : 0 < length
  map : PolarPoint → E3
  smooth_map : ContDiff ℝ ∞ map
  embedding : Topology.IsEmbedding (fun y : capDiskDomain => map y)
  immersion : ∀ y, cartesianRadius y ≤ 1 → Function.Injective (fderiv ℝ map y)
  boundary : ∀ y, cartesianRadius y = 1 → map y = graphMap id (fun _ => A.cRight) (R • y)
  open_collar : ∃ δ : ℝ, 0 < δ ∧ ∀ x,
    cartesianRadius x ∈ Ioo (R - δ) (R + δ) →
      map (capDiskRimChart R length x) = graphMap id (fun _ => A.cRight) x
  separation : ∀ t,
    graphPhaseDiskImage D R t ∩ map '' {y | cartesianRadius y ≤ 1} =
      capAttachingRim R A.cRight
  bottom : ℝ
  bottom_gap : ∀ t x, cartesianRadius x ≤ R → bottom < D.rotationFamily t x 2
  bottom_inside : ∀ y, cartesianRadius y ≤ 1 →
    cartesianRadius (graphBaseProjection (map y)) < R → map y 2 = bottom
  bottom_filled : ∀ x, cartesianRadius x < R →
    graphMap id (fun _ => bottom) x ∈ map '' {y | cartesianRadius y ≤ 1}
  normal : PolarPoint → E3
  smooth_normal : ContDiff ℝ ∞ normal
  unit_normal : ∀ y, cartesianRadius y ≤ 1 → IsUnitSurfaceNormal map y (normal y)
  marker : PolarPoint
  marker_interior : cartesianRadius marker < 1
  peak_cap : ∀ y, cartesianRadius y ≤ 1 → y ≠ marker →
    surfaceGaussianCurvature map (normal y) y <
      surfaceGaussianCurvature map (normal marker) marker
  peak_graph : ∀ t x, cartesianRadius x ≤ R →
    surfaceGaussianCurvature (D.rotationFamily t) (D.rotationNormal t x) x <
      surfaceGaussianCurvature map (normal marker) marker
  principal : HasDistinctPrincipalDirections map (normal marker) marker

def attachedSphereFamily {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R : ℝ) (C : FixedMarkedCap D R) : S2 × ℝ → E3 :=
  sphereGraphCapFamily D C.map R C.length

/-- Actual initial sphere and metric, before the phase conclusions are added. -/
structure InitialSphereData {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R : ℝ) (C : FixedMarkedCap D R) where
  metric : SmoothSphereMetric
  embedding : Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞
    (phaseMap (attachedSphereFamily D R C) 0)
  metric_identification : ∀ x (v w : SphereTangent x),
    metric.inner x v w =
      inner ℝ (sphereDifferential (phaseMap (attachedSphereFamily D R C) 0) x v)
        (sphereDifferential (phaseMap (attachedSphereFamily D R C) 0) x w)
  regions : DiskRegions
  graph_region : regions.graphDisk = {x : S2 | 0 ≤ (x : E3) 2}
  cap_region : regions.cap = {x : S2 | (x : E3) 2 ≤ 0}
  inner_region : regions.innerDisk =
    {x : S2 | x ∈ sphereNorthSource ∧ cartesianRadius (sphereNorthChart x) ≤ A.a / R}

structure SmoothSphereFamilyData {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R : ℝ) (C : FixedMarkedCap D R) extends InitialSphereData D R C where
  joint_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
    (attachedSphereFamily D R C)
  periodic : ∀ x t, attachedSphereFamily D R C (x, t + 1) =
    attachedSphereFamily D R C (x, t)
  fixed_inner : ∀ t x, x ∈ regions.innerDisk →
    attachedSphereFamily D R C (x, t) = attachedSphereFamily D R C (x, 0)
  fixed_cap : ∀ t x, x ∈ regions.cap →
    attachedSphereFamily D R C (x, t) = attachedSphereFamily D R C (x, 0)

structure IsometricSphereFamilyData {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R : ℝ) (C : FixedMarkedCap D R) extends SmoothSphereFamilyData D R C where
  phase_embedding : ∀ t, Manifold.IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞
    (phaseMap (attachedSphereFamily D R C) t)
  same_metric : ∀ t x (v w : SphereTangent x),
    inner ℝ (sphereDifferential (phaseMap (attachedSphereFamily D R C) t) x v)
      (sphereDifferential (phaseMap (attachedSphereFamily D R C) t) x w) = metric.inner x v w

/-- G01; §2 flat endpoints and §10 actual open-collar enlargement. -/
def G01Statement : Prop := ∀ A : FlatAnnularCore,
  ∃ B : AnnularSolution, B.toFlatAnnularCore = A ∧
    B.innerRadius = A.a / 2 ∧ B.outerRadius = A.b + 1 ∧
    (∀ r ∈ Ioo B.innerRadius B.a, ∀ θ, B.w r = 0 ∧ B.z (r, θ) = B.cLeft) ∧
    (∀ r ∈ Ioo B.b B.outerRadius, ∀ θ, B.w r = 0 ∧ B.z (r, θ) = B.cRight)

/-- G02; §2, lines 69–94: actual local development, with no assumed inverse. -/
def G02Statement : Prop := ∀ A : AnnularSolution,
  ∃ P : PolarPoint → PolarPoint, NormalizedPlanarDevelopment A.toFlatAnnularCore P

/-- G03; §2, lines 96–102: uniqueness, oddness, and the centered inner rotation. -/
def G03Statement : Prop := ∀ A : FlatAnnularCore, ∀ P : PolarPoint → PolarPoint,
  NormalizedPlanarDevelopment A P →
    (∀ Q, NormalizedPlanarDevelopment A Q → Q = P) ∧
    (∀ x, P (-x) = -P x) ∧ P 0 = 0 ∧
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      ∀ x, cartesianRadius x ≤ A.a → P x = planeRotationLinearMap c s x

/-- G04; §2, lines 104–108: actual global inverse and open/closed disk images. -/
def G04Statement : Prop := ∀ A : FlatAnnularCore, ∀ P : PolarPoint → PolarPoint,
  NormalizedPlanarDevelopment A P →
  ∃ e : PolarPoint ≃ₜ PolarPoint, (e : PolarPoint → PolarPoint) = P ∧
    ContDiff ℝ ∞ (e.symm : PolarPoint → PolarPoint) ∧
    ∀ R : ℝ, A.b < R →
      P '' {x | cartesianRadius x < R} = {x | cartesianRadius x < R} ∧
      P '' {x | cartesianRadius x ≤ R} = {x | cartesianRadius x ≤ R}

/-- G05; §2 planar reconstruction: the same P yields the actual E3 graph. -/
def G05Statement : Prop := ∀ A : FlatAnnularCore, ∀ P : PolarPoint → PolarPoint,
  NormalizedPlanarDevelopment A P →
  ∃ D : IsometricGraphDevelopment A, (D.planar : PolarPoint → PolarPoint) = P ∧
    (∀ x, A.b < cartesianRadius x →
      D.map x = graphMap id (fun _ => A.cRight) x) ∧
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      ∀ x, cartesianRadius x ≤ A.a →
        D.map x = graphMap (planeRotationLinearMap c s) (fun _ => A.cLeft) x

/-- G06; §2, lines 146–190: complete marked cap, not only a bump helper. -/
def G06Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → Nonempty (FixedMarkedCap D R)

/-- G07; §2 actual standard sphere and smooth positive pullback metric. -/
def G07Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R, Nonempty (InitialSphereData D R C)

/-- G08; §2, lines 230–237: the same initial data extend to one joint family. -/
def G08Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R, ∀ B : InitialSphereData D R C,
  ∃ P : SmoothSphereFamilyData D R C, P.toInitialSphereData = B

/-- G09; §2, lines 230–239: all real phases are actual smooth isometric embeddings. -/
def G09Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R, ∀ B : SmoothSphereFamilyData D R C,
  ∃ P : IsometricSphereFamilyData D R C, P.toSmoothSphereFamilyData = B

/-- G10; §2, lines 241–248: actual radial metric identity implies disk rigidity. -/
def G10Statement : Prop := ∀ A : FlatAnnularCore, ∀ R : ℝ, 0 < R →
  ∀ H : PolarPoint ≃ₜ PolarPoint,
  ContDiff ℝ ∞ (H : PolarPoint → PolarPoint) →
  ContDiff ℝ ∞ (H.symm : PolarPoint → PolarPoint) →
  (H '' {x | cartesianRadius x < R} = {x | cartesianRadius x < R}) →
  (∀ x, cartesianRadius x < R → ∀ u v,
    cartesianMetric A.w (H x) (fderiv ℝ (H : PolarPoint → PolarPoint) x u)
      (fderiv ℝ (H : PolarPoint → PolarPoint) x v) = cartesianMetric A.w x u v) →
  ∀ t : ℝ,
  (∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ x,
    cartesianRadius x ∈ Ioo (R - δ) R → H x = planarRotation t x) →
  ∀ x, cartesianRadius x ≤ R → H x = planarRotation t x

/-- G11; §2, lines 241–248: actual moving graph images are not all equal. -/
def G11Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∃ s t : ℝ,
    graphPhaseDiskImage D R s ≠ graphPhaseDiskImage D R t

/-- G12; §2, lines 250–253: all affine congruences lie in one set of at most four. -/
def G12Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R,
  IsometricSphereFamilyData D R C →
  EnclosedRegionFamily (attachedSphereFamily D R C) →
  ∃ candidates : Set (E3 ≃ᵃⁱ[ℝ] E3), candidates.Finite ∧ candidates.encard ≤ 4 ∧
    ∀ s t : ℝ, ∀ a : E3 ≃ᵃⁱ[ℝ] E3,
      a '' Set.range (phaseMap (attachedSphereFamily D R C) s) =
        Set.range (phaseMap (attachedSphereFamily D R C) t) → a ∈ candidates

/-- G13; §2, lines 250–256: noncongruence of actual closed images, including reflections. -/
def G13Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R,
  IsometricSphereFamilyData D R C →
  EnclosedRegionFamily (attachedSphereFamily D R C) →
  ∃ s t : ℝ, ∀ a : E3 ≃ᵃⁱ[ℝ] E3,
    a '' Set.range (phaseMap (attachedSphereFamily D R C) s) ≠
      Set.range (phaseMap (attachedSphereFamily D R C) t)

/-- G14; §2, lines 258–260: actual finite image area is phase independent. -/
def G14Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R,
  IsometricSphereFamilyData D R C → ∀ t : ℝ,
    imageArea (phaseMap (attachedSphereFamily D R C) t) < (⊤ : ℝ≥0∞) ∧
    imageArea (phaseMap (attachedSphereFamily D R C) t) =
      imageArea (phaseMap (attachedSphereFamily D R C) 0)

/-- G15; §2, lines 260–268: actual bounded inside, outward normal, and finite volume. -/
def G15Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R,
  IsometricSphereFamilyData D R C →
  ∃ O : EnclosedRegionFamily (attachedSphereFamily D R C), ∀ t : ℝ,
    0 < O.enclosedVolume t ∧ O.enclosedVolume t < (⊤ : ℝ≥0∞) ∧
    O.enclosedVolume t = O.enclosedVolume 0

/-- G16; §2, lines 258–260: actual integrable outward signed mean-curvature integral. -/
def G16Statement : Prop := ∀ A : FlatAnnularCore, ∀ D : IsometricGraphDevelopment A,
  ∀ R : ℝ, A.b < R → ∀ C : FixedMarkedCap D R,
  ∀ B : IsometricSphereFamilyData D R C,
  ∀ O : OrientedEnclosedFamily (attachedSphereFamily D R C) B.metric,
    (∀ t, Integrable (O.ambientMean t)
      (imageAreaMeasure (phaseMap (attachedSphereFamily D R C) t))) ∧
    ∀ t, O.totalMean t = O.totalMean 0

end ContinuousFlexibility.Statements
