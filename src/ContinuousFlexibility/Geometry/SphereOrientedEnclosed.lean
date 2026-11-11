import ContinuousFlexibility.Contracts.SphereEnclosedRegion
import ContinuousFlexibility.Geometry.EnclosedRegionUniqueness
import ContinuousFlexibility.Geometry.SphereMeanIntegral

/-!
# Oriented shape geometry of the constructed marked sphere

The constructed enclosure, normal, shape operator, and mean curvature all use
the same sphere family and the same cap parameters. Any other oriented
enclosure of this family has the same region, normal, and shape operator. Its
ambient mean agrees on the surface and has the same integral.
-/

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => Statements.S2
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

def IsometricGraphDevelopment.markedSpherePhaseShapeGeometry {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) : Statements.ShapeGeometry (D.markedSpherePhaseMap R L k ρ t)
      (D.markedSpherePhaseNormal R L k ρ t) := by
  let F := D.markedSpherePhaseMap R L k ρ t
  let N := D.markedSpherePhaseNormal R L k ρ t
  have hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F :=
    D.contMDiff_markedSpherePhaseMap hR hL hρ hsmall t
  have hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N :=
    D.contMDiff_markedSpherePhaseNormal hR hL hρ hsmall t
  have hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x) :=
    D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t
  have hu (x : SpherePoint) : ‖N x‖ = 1 := sphereMarkedNormal_norm D hR hL hρ hsmall (x, t)
  have ho (x : SpherePoint) (v : TangentSpace (𝓡 2) x) :
      inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0 :=
    sphereMarkedNormal_orthogonal D hR hL hρ hsmall t x v
  exact {
    shape := sphereShapeOperator F N
    smooth_shape := sphereShapeOperator_contMDiff hF hN hi hu ho
    weingarten := sphereShapeOperator_weingarten hN hi hu ho
    self_adjoint := sphereShapeOperator_self_adjoint hF hN hi hu ho
    smooth_mean := sphereShapeOperator_trace_contMDiff hF hN hi hu ho
    smooth_gaussian := sphereShapeOperator_det_contMDiff hF hN hi hu ho }

/-- The actual oriented enclosure equipped with the genuine shape operator and
the fixed pullback metric of the same marked sphere family. -/
def IsometricGraphDevelopment.markedSphereOrientedEnclosed {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hb : ∀ (t : ℝ) (q : PolarPoint), cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    (hmeet : ∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    Statements.OrientedEnclosedFamily
      (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L)
      (D.markedSphereMetric hR hL hk hρ hsmall) where
  toEnclosedRegionFamily := D.markedSphereEnclosedRegion hR hL hk hρ hsmall hb
  geometry := fun t => D.markedSpherePhaseShapeGeometry hR hL hk hρ hsmall t
  metric_self_adjoint := by
    intro t x v w
    let G := D.markedSpherePhaseShapeGeometry hR hL hk hρ hsmall t
    change (D.markedSphereMetric hR hL hk hρ hsmall).inner x (G.shape x v) w =
      (D.markedSphereMetric hR hL hk hρ hsmall).inner x v (G.shape x w)
    rw [← D.markedSphereFamily_pullback_metric hR hL hk hρ hsmall t x (G.shape x v) w,
      ← D.markedSphereFamily_pullback_metric hR hL hk hρ hsmall t x v (G.shape x w)]
    exact G.self_adjoint x v w
  ambientMean := D.markedSphereAmbientMean R L k ρ
  mean_identification := by
    intro t x
    have he := D.markedSpherePhaseMap_isEmbedding hR hL hk hρ hsmall (hmeet t)
    exact sphereImageScalar_apply he.injective (D.markedSphereMeanCurvature R L k ρ t) x

/-- The common frontier identifies the actual region. The actual outward
condition identifies the full normal function, which identifies its derivative
and the Weingarten endomorphism. -/
theorem IsometricGraphDevelopment.markedSphereEnclosure_unique {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ} {g : Statements.SmoothSphereMetric}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hb : ∀ (t : ℝ) (q : PolarPoint), cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    (O : Statements.OrientedEnclosedFamily
      (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) g) (t : ℝ) :
    O.region t = D.markedCapInterior t R L k ρ hL hk hρ ∧
    (fun x : SpherePoint => O.normal (x, t)) = D.markedSpherePhaseNormal R L k ρ t ∧
    ∀ x, (O.geometry t).shape x = sphereShapeOperator (D.markedSpherePhaseMap R L k ρ t)
      (D.markedSpherePhaseNormal R L k ρ t) x := by
  let P := D.markedSphereEnclosedRegion hR hL hk hρ hsmall hb
  let F := D.markedSpherePhaseMap R L k ρ t
  let N := D.markedSpherePhaseNormal R L k ρ t
  let M : SpherePoint → E3 := fun x => O.normal (x, t)
  have hr : O.region t = P.region t :=
    bounded_regions_eq_of_frontier_eq (O.region_open t) (P.region_open t)
      (O.region_bounded t) (P.region_bounded t) (O.exterior_connected t).isPreconnected
      (P.exterior_connected t).isPreconnected (O.exterior_unbounded t) (P.exterior_unbounded t)
      ((O.frontier_eq t).trans (P.frontier_eq t).symm)
  have hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F :=
    D.contMDiff_markedSpherePhaseMap hR hL hρ hsmall t
  have hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x) :=
    D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t
  have huN : ∀ x : SpherePoint, ‖N x‖ = 1 ∧ ∀ v : TangentSpace (𝓡 2) x,
      inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0 := P.unit_normal t
  have huM : ∀ x : SpherePoint, ‖M x‖ = 1 ∧ ∀ v : TangentSpace (𝓡 2) x,
      inner ℝ (mvfderiv (𝓡 2) F x v) (M x) = 0 := O.unit_normal t
  have houtN (x : SpherePoint) : PointsOutwardFrom (P.region t) (F x) (N x) := P.outward t x
  have houtM (x : SpherePoint) : PointsOutwardFrom (P.region t) (F x) (M x) := by
    rw [← hr]
    exact O.outward t x
  have hn : M = N := sphere_outward_normals_eq hF hi huN huM houtN houtM
  refine ⟨hr, hn, fun x => ?_⟩
  have hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N :=
    D.contMDiff_markedSpherePhaseNormal hR hL hρ hsmall t
  apply sphereShapeOperator_unique hN hi (fun y => (huN y).1) (fun y => (huN y).2)
  intro v
  have hw : mvfderiv (𝓡 2) F x ((O.geometry t).shape x v) = -mvfderiv (𝓡 2) M x v :=
    (O.geometry t).weingarten x v
  have hd := congrArg (fun n : SpherePoint → E3 => mvfderiv (𝓡 2) n x v) hn
  exact hw.trans (congrArg Neg.neg hd)

/-- Any oriented enclosure of the same constructed marked sphere has an
integrable ambient mean and the same signed mean integral in every phase. -/
theorem IsometricGraphDevelopment.markedSphereOrientedMean_invariant {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ} {g : Statements.SmoothSphereMetric}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hb : ∀ (t : ℝ) (q : PolarPoint), cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    (hmeet : ∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight)
    (O : Statements.OrientedEnclosedFamily
      (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) g) :
    (∀ t, Integrable (O.ambientMean t)
      (Statements.imageAreaMeasure (D.markedSpherePhaseMap R L k ρ t))) ∧
    ∀ t, O.totalMean t = O.totalMean 0 := by
  have hmean (t : ℝ) (x : SpherePoint) :
      O.ambientMean t (D.markedSpherePhaseMap R L k ρ t x) =
        D.markedSphereMeanCurvature R L k ρ t x := by
    refine (O.mean_identification t x).trans ?_
    have hs := (D.markedSphereEnclosure_unique hR hL hk hρ hsmall hb O t).2.2 x
    simp only [Statements.ShapeGeometry.mean, IsometricGraphDevelopment.markedSphereMeanCurvature,
      sphereMeanCurvature, hs]
  exact D.markedSphereMean_integral_invariant_of_identification hR hL hk hρ hsmall hmeet
    O.ambientMean hmean

end ContinuousFlexibility
