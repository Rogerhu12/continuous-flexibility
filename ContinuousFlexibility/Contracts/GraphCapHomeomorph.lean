import ContinuousFlexibility.Contracts.CapInteriorTopology
import ContinuousFlexibility.Contracts.GraphCapInterior

/-!
# A genuine ambient homeomorphism inserting the moving central graph

An explicit positive vertical scale changes the top height and fixes the bottom
plane. For the actual developed graph it is the identity outside the graph
support. It transports the actual cap body to the previously constructed glued
body, so both components of the complement have their actual topology. This
does not yet insert the fixed curvature marker or identify the whole frontier
with the final marked sphere.
-/

noncomputable section

namespace ContinuousFlexibility

open Set

set_option backward.isDefEq.respectTransparency false

def verticalScaleHomeomorph (bottom : ℝ) (a : PolarPoint → ℝ)
    (hc : Continuous a) (ha : ∀ x, 0 < a x) :
    (PolarPoint × ℝ) ≃ₜ (PolarPoint × ℝ) where
  toFun := fun q => (q.1, bottom + a q.1 * (q.2 - bottom))
  invFun := fun q => (q.1, bottom + (a q.1)⁻¹ * (q.2 - bottom))
  left_inv := by
    intro q
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [(ha q.1).ne']; ring
  right_inv := by
    intro q
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [(ha q.1).ne']; ring
  continuous_toFun := continuous_fst.prodMk (continuous_const.add
    ((hc.comp continuous_fst).mul (continuous_snd.sub continuous_const)))
  continuous_invFun := continuous_fst.prodMk (continuous_const.add
    (((hc.comp continuous_fst).inv₀ (fun q => (ha q.1).ne')).mul
      (continuous_snd.sub continuous_const)))

theorem vertical_height_interval_iff {bottom top newtop z : ℝ}
    (ht : bottom < top) (hn : bottom < newtop) :
    bottom + ((newtop - bottom) / (top - bottom)) * (z - bottom) ∈ Ioo bottom newtop ↔
      z ∈ Ioo bottom top := by
  let a := (newtop - bottom) / (top - bottom)
  have ha : 0 < a := div_pos (sub_pos.mpr hn) (sub_pos.mpr ht)
  have he : a * (top - bottom) = newtop - bottom := by
    dsimp [a]
    exact div_mul_cancel₀ _ (sub_pos.mpr ht).ne'
  change (bottom < bottom + a * (z - bottom) ∧
    bottom + a * (z - bottom) < newtop) ↔ _
  constructor
  · rintro ⟨hl, hr⟩
    have hp : 0 < a * (z - bottom) := by linarith
    have hz := (mul_pos_iff_of_pos_left ha).mp hp
    have hlt : a * (z - bottom) < a * (top - bottom) := by linarith
    have hz' : z - bottom < top - bottom := by nlinarith
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hr⟩
    have hp := mul_pos ha (sub_pos.mpr hl)
    have hlt := mul_lt_mul_of_pos_left (sub_lt_sub_right hr bottom) ha
    exact ⟨by linarith, by linarith⟩

theorem IsometricGraphDevelopment.physical_graph_above_bottom
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x))
    (x : PolarPoint) :
    A.cRight - L * capDrop < D.physicalHeight (planarRotation t x) := by
  by_cases hx : cartesianRadius x ≤ R
  · exact hb x hx
  · rw [D.rotated_physicalHeight_outside t (hR.trans (lt_of_not_ge hx))]
    linarith [mul_pos hL capDrop_pos]

def IsometricGraphDevelopment.graphHeightScale
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t L : ℝ) (x : PolarPoint) : ℝ :=
  (D.physicalHeight (planarRotation t x) - (A.cRight - L * capDrop)) / (L * capDrop)

def IsometricGraphDevelopment.graphCapHomeomorph
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) : E3 ≃ₜ E3 :=
  euclideanCoordinatesHomeomorph.trans
    ((verticalScaleHomeomorph (A.cRight - L * capDrop) (D.graphHeightScale t L)
      (((D.contDiff_physicalHeight.continuous.comp (planarRotation t).continuous).sub
        continuous_const).div_const _)
      (fun x => div_pos (sub_pos.mpr (D.physical_graph_above_bottom hR hL t hb x))
        (mul_pos hL capDrop_pos))).trans euclideanCoordinatesHomeomorph.symm)

@[simp] theorem IsometricGraphDevelopment.graphCapHomeomorph_base
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) (v : E3) :
    graphBaseProjection (D.graphCapHomeomorph hR hL t hb v) = graphBaseProjection v := by
  simp [IsometricGraphDevelopment.graphCapHomeomorph, verticalScaleHomeomorph,
    euclideanCoordinatesHomeomorph, euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]

@[simp] theorem IsometricGraphDevelopment.graphCapHomeomorph_height
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) (v : E3) :
    D.graphCapHomeomorph hR hL t hb v 2 = A.cRight - L * capDrop +
      D.graphHeightScale t L (graphBaseProjection v) * (v 2 - (A.cRight - L * capDrop)) := by
  simp [IsometricGraphDevelopment.graphCapHomeomorph, verticalScaleHomeomorph,
    euclideanCoordinatesHomeomorph, euclideanVectorOfCoordinates, e3Basis]

theorem IsometricGraphDevelopment.graphCapHomeomorph_outside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) {v : E3}
    (hv : A.b < cartesianRadius (graphBaseProjection v)) :
    D.graphCapHomeomorph hR hL t hb v = v := by
  apply e3_eq_of_base_height
  · exact D.graphCapHomeomorph_base hR hL t hb v
  · rw [D.graphCapHomeomorph_height]
    simp only [IsometricGraphDevelopment.graphHeightScale,
      D.rotated_physicalHeight_outside t hv]
    have he : A.cRight - (A.cRight - L * capDrop) = L * capDrop := by ring
    rw [he, div_self (mul_pos hL capDrop_pos).ne']
    ring

theorem capRevolutionInterior_mem_of_radius_lt {R h L : ℝ} (hL : 0 < L) {v : E3}
    (hv : cartesianRadius (graphBaseProjection v) < R) :
    v ∈ capRevolutionInterior R h L ↔ v 2 ∈ Ioo (h - L * capDrop) h := by
  constructor
  · exact fun hmem => hmem.1
  · intro hz
    exact ⟨hz, hv.trans (capWallRadius_gt hL hz)⟩

theorem IsometricGraphDevelopment.graphCapHomeomorph_mem
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) (v : E3) :
    D.graphCapHomeomorph hR hL t hb v ∈ D.graphCapInterior t R L ↔
      v ∈ capRevolutionInterior R A.cRight L := by
  rw [D.graphCapInterior_partition hR]
  by_cases hv : cartesianRadius (graphBaseProjection v) < R
  · have hnb : ¬R ≤ cartesianRadius (graphBaseProjection v) := not_le_of_gt hv
    change (cartesianRadius (graphBaseProjection (D.graphCapHomeomorph hR hL t hb v)) < R ∧
      A.cRight - L * capDrop < D.graphCapHomeomorph hR hL t hb v 2 ∧
      D.graphCapHomeomorph hR hL t hb v 2 < D.physicalHeight
        (planarRotation t (graphBaseProjection (D.graphCapHomeomorph hR hL t hb v)))) ∨
      (D.graphCapHomeomorph hR hL t hb v ∈ capRevolutionInterior R A.cRight L ∧
        R ≤ cartesianRadius (graphBaseProjection (D.graphCapHomeomorph hR hL t hb v))) ↔ _
    simp only [D.graphCapHomeomorph_base, hv, hnb, true_and, and_false, or_false]
    rw [capRevolutionInterior_mem_of_radius_lt hL hv, D.graphCapHomeomorph_height]
    have hd : A.cRight - L * capDrop < A.cRight := by linarith [mul_pos hL capDrop_pos]
    have he : A.cRight - (A.cRight - L * capDrop) = L * capDrop := by ring
    simpa only [mem_Ioo, IsometricGraphDevelopment.graphHeightScale, he] using
      (vertical_height_interval_iff (z := v 2) hd (hb _ hv.le))
  · have he := D.graphCapHomeomorph_outside hR hL t hb (hR.trans_le (le_of_not_gt hv))
    rw [he]
    change ((cartesianRadius (graphBaseProjection v) < R ∧ _) ∨
      (v ∈ capRevolutionInterior R A.cRight L ∧ R ≤ cartesianRadius (graphBaseProjection v))) ↔ _
    simp only [hv, le_of_not_gt hv, false_and, and_true, false_or]

theorem IsometricGraphDevelopment.graphCapInterior_eq_preimage
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    D.graphCapInterior t R L = (D.graphCapHomeomorph hR hL t hb).symm ⁻¹'
      capRevolutionInterior R A.cRight L := by
  ext v
  simpa only [mem_preimage, Homeomorph.apply_symm_apply] using
    (D.graphCapHomeomorph_mem hR hL t hb ((D.graphCapHomeomorph hR hL t hb).symm v))

theorem IsometricGraphDevelopment.isConnected_graphCapInterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    IsConnected (D.graphCapInterior t R L) := by
  rw [D.graphCapInterior_eq_preimage hR hL t hb]
  exact (D.graphCapHomeomorph hR hL t hb).symm.isConnected_preimage.mpr
    (isConnected_capRevolutionInterior (A.b_pos.trans hR) hL A.cRight)

theorem IsometricGraphDevelopment.isConnected_graphCapExterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (t : ℝ)
    (hb : ∀ x : PolarPoint, cartesianRadius x ≤ R →
      A.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) :
    IsConnected (closure (D.graphCapInterior t R L))ᶜ := by
  rw [D.graphCapInterior_eq_preimage hR hL t hb,
    ← (D.graphCapHomeomorph hR hL t hb).symm.preimage_closure, ← preimage_compl]
  exact (D.graphCapHomeomorph hR hL t hb).symm.isConnected_preimage.mpr
    (isConnected_capRevolutionExterior (A.b_pos.trans hR) hL A.cRight)

theorem IsometricGraphDevelopment.unbounded_graphCapExterior
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) {L : ℝ} (hL : 0 < L) :
    ¬Bornology.IsBounded (closure (D.graphCapInterior t R L))ᶜ := by
  obtain ⟨K, hK, hsub⟩ := D.exists_compact_graphCapInterior_bound R hL
  have hb : Bornology.IsBounded (closure (D.graphCapInterior t R L)) :=
    hK.isBounded.subset (closure_minimal (hsub t) hK.isClosed)
  intro he
  apply NormedSpace.unbounded_univ ℝ E3
  simpa only [union_compl_self] using hb.union he

end ContinuousFlexibility
