module

public import ContinuousFlexibility.Contracts.MarkedCapOutward
public import ContinuousFlexibility.Statements.MainGeometry

/-!
# The enclosed-region witness for the actual marked sphere

The same marked cap length, marker, sphere family and inside region appear
in every field. In particular, the normal is the explicit jointly smooth
sphere normal whose rays were proved outward for that very region.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set

set_option backward.isDefEq.respectTransparency false

def IsometricGraphDevelopment.markedSphereEnclosedRegion
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hb : ∀ (t : ℝ) (q : PolarPoint), cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q)) :
    Statements.EnclosedRegionFamily
      (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) where
  region := fun t => D.markedCapInterior t R L k ρ hL hk hρ
  region_open := fun t => D.isOpen_markedCapInterior t R L k ρ hL hk hρ
  region_bounded := fun t => D.isBounded_markedCapInterior t R L k ρ hL hk hρ
  region_connected := fun t => D.isConnected_markedCapInterior hR hL t k ρ hk hρ (hb t)
  frontier_eq := fun t =>
    D.frontier_markedCapInterior_eq_sphereRange hR hL t k ρ hk hρ hsmall (hb t)
  exterior_connected := fun t => D.isConnected_markedCapExterior hR hL t k ρ hk hρ (hb t)
  exterior_unbounded := fun t => D.unbounded_markedCapExterior t R L k ρ hL hk hρ
  normal := sphereMarkedNormal D R L k ρ
  normal_smooth := contMDiff_sphereMarkedNormal D hR hL hρ hsmall
  unit_normal := fun t x => ⟨sphereMarkedNormal_norm D hR hL hρ hsmall (x, t),
    sphereMarkedNormal_orthogonal D hR hL hρ hsmall t x⟩
  outward := fun t x => D.sphereMarkedNormal_pointsOutwardFrom hR hL hk hρ hsmall t (hb t) x

end ContinuousFlexibility
