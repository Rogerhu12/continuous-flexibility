import ContinuousFlexibility.Contracts.MarkedCapInterior
import ContinuousFlexibility.Geometry.GraphCapOutward
import ContinuousFlexibility.Geometry.MarkedCapPhysicalNormals

/-!
# The actual outward normal of the marked graph-cap body

Below the turning radius the actual inside is an open vertical interval.
Inserting the marker changes its roof by the physical bump and leaves its
bottom fixed. The marked top therefore has its own defining function. The
middle and turning circles have unchanged germs; on the bottom the regions
agree near the point even when the ambient deformation is not locally the
identity. This identifies the previously constructed sphere normal with the
outward orientation of the very same region whose volume was computed.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

set_option backward.isDefEq.respectTransparency false

theorem IsometricGraphDevelopment.graphCapInterior_mem_below_turning_radius
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ) {v : E3}
    (hr : cartesianRadius (graphBaseProjection v) ≤ R + L / 4) :
    v ∈ D.graphCapInterior t R L ↔
      v 2 ∈ Ioo (A.cRight - L * capDrop)
        (D.physicalHeight (planarRotation t (graphBaseProjection v))) := by
  have hc : v ∈ capRevolutionInterior R A.cRight L ↔
      v 2 ∈ Ioo (A.cRight - L * capDrop) A.cRight := by
    refine ⟨fun hv => hv.1, fun hz => ⟨hz, hr.trans_lt
      (capWallRadius_gt_rim R A.cRight hL hz)⟩⟩
  rw [D.graphCapInterior_partition hR t]
  by_cases hin : cartesianRadius (graphBaseProjection v) < R
  · constructor
    · rintro (h | h)
      · exact h.2
      · exact (not_lt_of_ge h.2 hin).elim
    · exact fun h => Or.inl ⟨hin, h⟩
  · have hout := le_of_not_gt hin
    rw [D.rotated_physicalHeight_outside t (hR.trans_le hout)]
    constructor
    · rintro (h | h)
      · exact (hin h.1).elim
      · exact hc.mp h.1
    · exact fun h => Or.inr ⟨hc.mpr h, hout⟩

/-- In the whole vertical band inside the turning radius, the physical roof
of the marked region is the developed graph height plus the actual bump. -/
theorem IsometricGraphDevelopment.markedCapInterior_mem_below_turning_radius
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) {v : E3} (hr : cartesianRadius (graphBaseProjection v) ≤ R + L / 4) :
    v ∈ D.markedCapInterior t R L k ρ hL hk hρ ↔
      v 2 ∈ Ioo (A.cRight - L * capDrop)
        (D.physicalHeight (planarRotation t (graphBaseProjection v)) +
          markerAmbientBump R L k ρ (graphBaseProjection v)) := by
  let H := markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ
  obtain ⟨w, rfl⟩ := H.surjective v
  have hbase : graphBaseProjection (H w) = graphBaseProjection w :=
    markerAmbientHomeomorph_base R A.cRight L k ρ hL hk hρ w
  rw [hbase] at hr
  rw [D.markedCapInterior_eq_preimage]
  change (H.symm (H w) ∈ D.graphCapInterior t R L) ↔ _
  rw [H.symm_apply_apply, D.graphCapInterior_mem_below_turning_radius hR hL t hr, hbase]
  let q := graphBaseProjection w
  let b := A.cRight - L * capDrop
  let a := markerAmbientScale R L k ρ q
  let z := D.physicalHeight (planarRotation t q)
  let β := markerAmbientBump R L k ρ q
  have ha : 0 < a := markerAmbientScale_pos R hL hk hρ q
  have htop : b + a * (z - b) = z + β := by
    by_cases hβ : β = 0
    · have ha1 : a = 1 := by
        change 1 + β / (L * capDrop) = 1
        simp [hβ]
      rw [ha1, hβ]
      ring
    · have hq := (markerAmbientBump_support_bounds (A.b_pos.trans hR) hL hρ hsmall hβ).1
      have hz : z = A.cRight := D.rotated_physicalHeight_outside t (by linarith)
      rw [hz]
      change b + (1 + β / (L * capDrop)) * (A.cRight - b) = A.cRight + β
      have hb : A.cRight - b = L * capDrop := by dsimp only [b]; ring
      rw [hb, add_mul, one_mul, div_mul_cancel₀ _ (mul_pos hL capDrop_pos).ne']
      dsimp only [b]
      ring
  change w 2 ∈ Ioo b z ↔ H w 2 ∈ Ioo b (z + β)
  rw [← htop, show H w 2 = b + a * (w 2 - b) from
    markerAmbientHomeomorph_height R A.cRight L k ρ hL hk hρ w]
  simp only [mem_Ioo, lt_add_iff_pos_right, mul_pos_iff_of_pos_left ha, sub_pos,
    add_lt_add_iff_left, mul_lt_mul_iff_right₀ ha, sub_lt_sub_iff_right]

private theorem markedCapInterior_germ_of_marker_identity
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (t : ℝ) {p : E3}
    (he : (markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ : E3 → E3) =ᶠ[𝓝 p] id) :
    D.markedCapInterior t R L k ρ hL hk hρ =ᶠ[𝓝 p] D.graphCapInterior t R L := by
  let H := markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [he] with v hv
  have hsymm : H.symm v = v := calc
    H.symm v = H.symm (H v) := congrArg H.symm hv.symm
    _ = v := H.symm_apply_apply v
  rw [D.markedCapInterior_eq_preimage]
  change (H.symm v ∈ D.graphCapInterior t R L) ↔ _
  rw [hsymm]

theorem IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom_markedCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    {x : PolarPoint} (hx : cartesianRadius x ≤ R) :
    PointsOutwardFrom (D.markedCapInterior t R L k ρ hL hk hρ)
      (D.rotationFamily t x) (D.rotationNormal t x) := by
  have hr := D.phase_disk_projection_bound t hR.le hx
  have he := markerAmbientHomeomorph_inner_germ (k := k) (A.b_pos.trans hR) hL hk hρ hsmall
    A.cRight (v := D.rotationFamily t x) (by linarith)
  exact (D.rotationNormal_pointsOutwardFrom_graphCapInterior_closed hR hL t hb hx).congr_germ
    (markedCapInterior_germ_of_marker_identity D hL hk hρ t he).symm

private theorem markedCapInterior_top_germ
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (ht : capDiskParameter R L y < L / 4) :
    D.markedCapInterior t R L k ρ hL hk hρ =ᶠ[𝓝 (markedCapMap R A.cRight L k ρ y)]
      {v : E3 | graphDefiningFunction (fun q => A.cRight + markerAmbientBump R L k ρ q) v < 0} := by
  let p := markedCapMap R A.cRight L k ρ y
  have hRp := A.b_pos.trans hR
  have hs := (capDiskParameter_mem hRp hL hy).1
  have hr : cartesianRadius (graphBaseProjection p) = R + capDiskParameter R L y := by
    change cartesianRadius (graphBaseProjection (markedCapMap R A.cRight L k ρ y)) = _
    rw [markedCapMap_base, capDiskBase_radius hRp hL hy, capMeridianRadius_eq_left R hL ht.le]
  have hheight : A.cRight - L * capDrop < p 2 := by
    change A.cRight - L * capDrop < markedCapMap R A.cRight L k ρ y 2
    rw [markedCapMap_physical_top hL A.cRight k ρ ht, graphMap_two]
    linarith [mul_pos hL capDrop_pos,
      markerAmbientBump_nonneg R L hk hρ (capDiskBase R L y)]
  have hcr := continuous_cartesianRadius.comp continuous_graphBaseProjection
  have hcz : Continuous (fun v : E3 => v 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hpb : A.b < cartesianRadius (graphBaseProjection p) := by rw [hr]; linarith
  have hpr : cartesianRadius (graphBaseProjection p) < R + L / 4 := by rw [hr]; linarith
  have hnear₁ : ∀ᶠ v in 𝓝 p, A.b < cartesianRadius (graphBaseProjection v) :=
    (isOpen_lt continuous_const hcr).mem_nhds hpb
  have hnear₂ : ∀ᶠ v in 𝓝 p, cartesianRadius (graphBaseProjection v) < R + L / 4 :=
    (isOpen_lt hcr continuous_const).mem_nhds hpr
  have hnear₃ : ∀ᶠ v in 𝓝 p, A.cRight - L * capDrop < v 2 :=
    (isOpen_lt continuous_const hcz).mem_nhds hheight
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [hnear₁, hnear₂, hnear₃] with v hv₁ hv₂ hv₃
  rw [D.markedCapInterior_mem_below_turning_radius hR hL hk hρ hsmall t hv₂.le,
    D.rotated_physicalHeight_outside t hv₁]
  change (_ ∧ _) ↔ v 2 - (A.cRight + markerAmbientBump R L k ρ (graphBaseProjection v)) < 0
  simp only [hv₃, true_and, sub_neg]

private theorem markedCapInterior_bottom_germ
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    {p : E3} (hp : p 2 = A.cRight - L * capDrop)
    (hr : cartesianRadius (graphBaseProjection p) < R + L / 4) :
    D.markedCapInterior t R L k ρ hL hk hρ =ᶠ[𝓝 p] D.graphCapInterior t R L := by
  have hcr := continuous_cartesianRadius.comp continuous_graphBaseProjection
  have hcz : Continuous (fun v : E3 => v 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hroof := D.contDiff_physicalHeight.continuous.comp
    ((planarRotation t).continuous.comp continuous_graphBaseProjection)
  have hnear₁ : ∀ᶠ v in 𝓝 p, cartesianRadius (graphBaseProjection v) < R + L / 4 :=
    (isOpen_lt hcr continuous_const).mem_nhds hr
  have hpRoof : p 2 < D.physicalHeight (planarRotation t (graphBaseProjection p)) := by
    rw [hp]
    exact D.physical_graph_above_bottom hR hL t hb _
  have hnear₂ : ∀ᶠ v in 𝓝 p, v 2 < D.physicalHeight (planarRotation t (graphBaseProjection v)) :=
    (isOpen_lt hcz hroof).mem_nhds hpRoof
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [hnear₁, hnear₂] with v hv₁ hv₂
  have hv₃ : v 2 < D.physicalHeight (planarRotation t (graphBaseProjection v)) +
      markerAmbientBump R L k ρ (graphBaseProjection v) := by
    linarith [markerAmbientBump_nonneg R L hk hρ (graphBaseProjection v)]
  rw [D.markedCapInterior_mem_below_turning_radius hR hL hk hρ hsmall t hv₁.le,
    D.graphCapInterior_mem_below_turning_radius hR hL t hv₁.le]
  simp only [mem_Ioo, hv₂, hv₃]

theorem IsometricGraphDevelopment.markedCapNormal_pointsOutwardFrom_markedCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    PointsOutwardFrom (D.markedCapInterior t R L k ρ hL hk hρ)
      (markedCapMap R A.cRight L k ρ y) (markedCapNormal R L k ρ y) := by
  have hRp := A.b_pos.trans hR
  by_cases ht : capDiskParameter R L y < L / 4
  · obtain ⟨c, hc, hd⟩ :=
      markedCapNormal_top_defining_derivative_pos hRp hL hρ hsmall A.cRight hy ht
    exact PointsOutwardFrom.of_defining_function
      (continuous_graphDefiningFunction
        (continuous_const.add (contDiff_markerAmbientBump R L k ρ).continuous))
      (markedCapInterior_top_germ D hR hL hk hρ hsmall t hy ht)
      (markedCapMap_top_defining_eq_zero hL A.cRight k ρ ht) hd hc
  · let p := capDiskMap R A.cRight L y
    let H := markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ
    have hmap : H p = markedCapMap R A.cRight L k ρ y :=
      markerAmbientHomeomorph_capDiskMap hRp hL hk hρ hsmall A.cRight hy
    have hn : markedCapNormal R L k ρ y = capDiskNormal R L y :=
      markedCapNormal_eq_capDiskNormal hRp hL hρ hsmall (le_of_not_gt ht)
    rw [← hmap, hn]
    have hout := D.capDiskNormal_pointsOutwardFrom_graphCapInterior hR hL t hb hy
    by_cases hr : R + 3 * L / 16 < cartesianRadius (graphBaseProjection p)
    · have he := markerAmbientHomeomorph_outer_germ hRp hL hk hρ hsmall A.cRight hr
      rw [show H p = p from he.eq_of_nhds]
      exact hout.congr_germ (markedCapInterior_germ_of_marker_identity D hL hk hρ t he).symm
    · have hbparam : 3 * L / 4 ≤ capDiskParameter R L y := by
        by_contra! hmid
        have hpbase : graphBaseProjection p = capDiskBase R L y := by simp [p, capDiskMap]
        have hrad : R + L / 4 ≤ cartesianRadius (graphBaseProjection p) := by
          rw [hpbase, capDiskBase_radius hRp hL hy]
          exact markedCap_meridian_middle_lower R hL ⟨le_of_not_gt ht, hmid.le⟩
        exact hr (by linarith)
      have hp : p 2 = A.cRight - L * capDrop := by
        simpa only [p, capDiskMap_two, capDiskHeight] using
          capMeridianHeight_eq_right A.cRight hL hbparam
      rw [show H p = p from markerAmbientHomeomorph_fixes_bottom R A.cRight L k ρ hL hk hρ hp]
      exact hout.congr_germ
        (markedCapInterior_bottom_germ D hR hL hk hρ hsmall t hb hp
          ((le_of_not_gt hr).trans_lt (by linarith))).symm

/-- The previously constructed smooth sphere normal is outward everywhere,
including the equator, for the actual bounded marked region. -/
theorem IsometricGraphDevelopment.sphereMarkedNormal_pointsOutwardFrom
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (hb : ∀ q : PolarPoint, cartesianRadius q ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t q))
    (x : SpherePoint) :
    PointsOutwardFrom (D.markedCapInterior t R L k ρ hL hk hρ)
      (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))
      (sphereMarkedNormal D R L k ρ (x, t)) := by
  have hRp := A.b_pos.trans hR
  by_cases hx : 0 ≤ (x : E3) 2
  · have hn : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
    have hr := (sphereNorthChart_radius_le_one_iff x hn).mpr hx
    have hrad : cartesianRadius (R • sphereNorthChart x) ≤ R := by
      rw [capDisk_radius_smul, abs_of_pos hRp]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hRp.le
    rw [sphereGraphCapFamily_north D _ R L t x hx, sphereMarkedNormal_north D R L k ρ t x hx]
    exact D.rotationNormal_pointsOutwardFrom_markedCapInterior hR hL hk hρ hsmall t hb hrad
  · have hx' := le_of_not_ge hx
    have hs : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
    have hr := (sphereSouthChart_radius_le_one_iff x hs).mpr hx'
    have ha := capSphereRatio_mem hRp hL
    have hrad := capSphereRadialMap_mapsTo_disk ha.1 ha.2 hr
    rw [sphereGraphCapFamily_south D hR
      (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
        hRp hL hρ hsmall A.cRight hy) x hx' t,
      sphereMarkedNormal_south D hR hL hρ hsmall t x hx']
    exact D.markedCapNormal_pointsOutwardFrom_markedCapInterior hR hL hk hρ hsmall t hb hrad

end ContinuousFlexibility
