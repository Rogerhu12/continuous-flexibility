import ContinuousFlexibility.Geometry.SphereCommonCapLength
import ContinuousFlexibility.Statements.MainGeometry

/-!
# The actual marked cap satisfies the geometric specification

The same marked cap map supplies its smoothness, embedded disk, open rim
collar, bottom disk, and strict curvature maximum. The principal directions
come from the cap shape eigenvectors. The differential gives their lengths,
and symmetry of the second form gives their orthogonality.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem secondForm_eq_mul_firstForm_of_shape_eigenvector
    {F : PolarPoint → E3} {p : PolarPoint} {N : E3}
    (hF : ContDiff ℝ ∞ F) (hi : Function.Injective (fderiv ℝ F p))
    {a : Fin 2 → ℝ} {κ : ℝ}
    (heig : (surfaceShapeMatrix F N p).mulVec a = κ • a) (w : PolarPoint) :
    surfaceSecondForm F N p (a 0, a 1) w = κ * surfaceFirstForm F p (a 0, a 1) w := by
  have hII : surfaceSecondForm F N p w (a 0, a 1) =
      dotProduct ![w.1, w.2] ((surfaceSecondMatrix F N p).mulVec a) := by
    rw [surfaceSecondForm_coordinates]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have hI : dotProduct ![w.1, w.2] ((surfaceGram F p).mulVec a) =
      surfaceFirstForm F p w (a 0, a 1) := by
    rw [surfaceFirstForm_coordinates]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  calc
    surfaceSecondForm F N p (a 0, a 1) w = surfaceSecondForm F N p w (a 0, a 1) :=
      surfaceSecondForm_symm hF N p _ _
    _ = dotProduct ![w.1, w.2] ((surfaceSecondMatrix F N p).mulVec a) := hII
    _ = dotProduct ![w.1, w.2]
        ((surfaceGram F p).mulVec ((surfaceShapeMatrix F N p).mulVec a)) := by
      rw [Matrix.mulVec_mulVec, surfaceGram_mul_shape hi N]
    _ = κ * dotProduct ![w.1, w.2] ((surfaceGram F p).mulVec a) := by
      rw [heig, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    _ = κ * surfaceFirstForm F p (a 0, a 1) w := by
      rw [hI, surfaceFirstForm_symm F p w (a 0, a 1)]

private theorem normalized_principalDirections_of_shape_eigenvectors
    {F : PolarPoint → E3} {p : PolarPoint} {N : E3}
    (hF : ContDiff ℝ ∞ F) (hi : Function.Injective (fderiv ℝ F p))
    {a b : Fin 2 → ℝ} {κ₁ κ₂ : ℝ} (hne : κ₁ ≠ κ₂)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (heig₁ : (surfaceShapeMatrix F N p).mulVec a = κ₁ • a)
    (heig₂ : (surfaceShapeMatrix F N p).mulVec b = κ₂ • b) :
    Statements.HasDistinctPrincipalDirections F N p := by
  let T := fderiv ℝ F p
  have hnormalize (v : Fin 2 → ℝ) (hv : v ≠ 0) {κ : ℝ}
      (heig : (surfaceShapeMatrix F N p).mulVec v = κ • v) :
      ∃ u : PolarPoint, ‖T u‖ = 1 ∧ ∀ w,
        surfaceSecondForm F N p u w = κ * surfaceFirstForm F p u w := by
    have hn : 0 < ‖T (v 0, v 1)‖ := by
      apply norm_pos_iff.mpr
      intro hz
      have hpair : (v 0, v 1) = (0 : PolarPoint) :=
        hi (by simpa only [map_zero] using hz)
      apply hv
      funext i
      fin_cases i
      · exact congrArg Prod.fst hpair
      · exact congrArg Prod.snd hpair
    let c := ‖T (v 0, v 1)‖⁻¹
    have hscaled : (surfaceShapeMatrix F N p).mulVec (c • v) = κ • (c • v) := by
      rw [Matrix.mulVec_smul, heig]
      exact smul_comm c κ v
    refine ⟨((c • v) 0, (c • v) 1), ?_, ?_⟩
    · change ‖T (c • (v 0, v 1))‖ = 1
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
      exact inv_mul_cancel₀ hn.ne'
    · exact secondForm_eq_mul_firstForm_of_shape_eigenvector hF hi hscaled
  obtain ⟨u, hunit₁, hform₁⟩ := hnormalize a ha heig₁
  obtain ⟨v, hunit₂, hform₂⟩ := hnormalize b hb heig₂
  have hs := surfaceSecondForm_symm hF N p u v
  rw [hform₁ v, hform₂ u, surfaceFirstForm_symm F p v u] at hs
  have hz : (κ₁ - κ₂) * surfaceFirstForm F p u v = 0 := by
    rw [sub_mul, hs, sub_self]
  have ho : surfaceFirstForm F p u v = 0 :=
    (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
  exact ⟨κ₁, κ₂, u, v, hne, hunit₁, hunit₂, ho, hform₁, hform₂⟩

/-- Unit orthogonal principal directions in the actual tangent plane of the marker. -/
theorem markedCap_hasDistinctPrincipalDirections {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 < k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) :
    Statements.HasDistinctPrincipalDirections (markedCapMap R h L k ρ)
      (markedCapNormal R L k ρ (markedCapCenterParameter R L))
      (markedCapCenterParameter R L) := by
  obtain ⟨hne, ha, hb, heig₁, heig₂⟩ :=
    surfaceShapeMatrix_markedCap_center_eigenvectors hR hL hk.ne' h ρ
  exact normalized_principalDirections_of_shape_eigenvectors
    (contDiff_markedCapMap hR hL h k ρ)
    (markedCapMap_fderiv_injective hR hL hk.le hρ hsmall h
      (markedCapCenterParameter_mem hR hL).le) hne ha hb heig₁ heig₂

private theorem markedCap_open_physical_collar {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : PolarPoint,
      cartesianRadius x ∈ Ioo (R - δ) (R + δ) →
        markedCapMap R h L k ρ (capDiskRimChart R L x) = graphMap id (fun _ => h) x := by
  let δ := min (R / 2) (L / 16)
  have hδR : δ ≤ R / 2 := min_le_left _ _
  have hδL : δ ≤ L / 16 := min_le_right _ _
  refine ⟨δ, lt_min (by linarith) (by linarith), fun x hx => ?_⟩
  have hx0 : 0 < cartesianRadius x := by linarith [hx.1]
  have hx16 : cartesianRadius x < R + L / 16 := by linarith [hx.2]
  have hx4 : cartesianRadius x < R + L / 4 := by linarith
  have hb : cartesianRadius (capDiskBase R L (capDiskRimChart R L x)) ≤ R + L / 16 := by
    rw [capDiskBase_rimChart hR hL hx0 hx4]
    exact hx16.le
  rw [markedCapMap_eq_capDiskMap_of_inner hR hL hρ hsmall h hb]
  exact capDiskMap_rimChart hR hL h hx0 hx4

private theorem markedCap_inside_cylinder_bottom {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (hinside : cartesianRadius (graphBaseProjection (markedCapMap R h L k ρ y)) < R) :
    markedCapMap R h L k ρ y 2 = h - L * capDrop := by
  have hb : cartesianRadius (capDiskBase R L y) < R := by
    simpa only [markedCapMap_base] using hinside
  have he := markedCapMap_eq_capDiskMap_of_inner (k := k) hR hL hρ hsmall h
    (by linarith : cartesianRadius (capDiskBase R L y) ≤ R + L / 16)
  rw [he] at hinside ⊢
  exact capDisk_inside_cylinder_bottom hR hL h hy hinside

private theorem markedCap_bottom_filled {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {x : PolarPoint} (hx : cartesianRadius x < R) :
    graphMap id (fun _ => h - L * capDrop) x ∈
      markedCapMap R h L k ρ '' {y | cartesianRadius y ≤ 1} := by
  let y : PolarPoint := (L + R)⁻¹ • x
  have hsum : 0 < L + R := add_pos hL hR
  have hyr : cartesianRadius y = cartesianRadius x / (L + R) := by
    change cartesianRadius ((L + R)⁻¹ • x) = _
    rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hsum), div_eq_mul_inv, mul_comm]
  have hy : cartesianRadius y ≤ 1 := by
    rw [hyr]
    exact (div_le_one hsum).mpr (by linarith)
  have hs : capDiskParameter R L y = L + R - cartesianRadius x := by
    rw [capDiskParameter, hyr]
    field_simp [hsum.ne']
  have hright : 3 * L / 4 ≤ capDiskParameter R L y := by
    rw [hs]
    linarith
  have hbscale : capDiskBase R L y = (L + R) • y := by
    unfold capDiskBase
    rw [capMeridianRadius_eq_right R hL hright]
    rw [show R + L - capDiskParameter R L y = (L + R) * cartesianRadius y by
      unfold capDiskParameter
      ring]
    by_cases hy0 : y = 0
    · simp [hy0]
    · rw [mul_div_cancel_right₀ _ (cartesianRadius_pos hy0).ne']
  have hb : capDiskBase R L y = x := by
    rw [hbscale]
    change (L + R) • ((L + R)⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hsum.ne', one_smul]
  have hinner : cartesianRadius (capDiskBase R L y) ≤ R + L / 16 := by
    rw [hb]
    linarith
  refine ⟨y, hy, ?_⟩
  rw [markedCapMap_eq_capDiskMap_of_inner hR hL hρ hsmall h hinner]
  apply e3_eq_of_base_height
  · simp only [capDiskMap, graphBaseProjection_graphMap, hb, id_eq]
  · rw [capDiskMap_two, graphMap_two, capDiskHeight]
    exact capMeridianHeight_eq_right h hL hright

private theorem markedCap_intersection_eq_rim {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    graphPhaseDiskImage D R t ∩ (markedCapMap R A.cRight L k ρ ''
      {y | cartesianRadius y ≤ 1}) = capAttachingRim R A.cRight := by
  apply Set.Subset.antisymm (D.marked_cap_meeting_subset hR hL hρ hsmall hmeet)
  rintro _ ⟨x, hx, rfl⟩
  have hRp := A.b_pos.trans hR
  have hxR : cartesianRadius x = R := hx
  constructor
  · exact ⟨x, hxR.le, D.phase_flat_outside t (hxR.symm ▸ hR)⟩
  · have hy := (capDisk_physical_boundary hRp A.cRight L hxR).1
    refine ⟨R⁻¹ • x, hy.le, ?_⟩
    simpa only [smul_smul, mul_inv_cancel₀ hRp.ne', one_smul] using
      (markedCap_boundary (k := k) hRp hL hρ hsmall A.cRight hy)

/-- Package the actual cap at the supplied length and marker parameters. -/
def IsometricGraphDevelopment.markedCapSpecification {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 < k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hgap : ∀ t x, cartesianRadius x ≤ R → A.cRight - L * capDrop < D.rotationFamily t x 2)
    (hmeet : ∀ t, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight)
    (hcap : ∀ y, cartesianRadius y ≤ 1 → y ≠ markedCapCenterParameter R L →
      surfaceGaussianCurvature (markedCapMap R A.cRight L k ρ) (markedCapNormal R L k ρ y) y <
        surfaceGaussianCurvature (markedCapMap R A.cRight L k ρ)
          (markedCapNormal R L k ρ (markedCapCenterParameter R L)) (markedCapCenterParameter R L))
    (hgraph : ∀ t x, cartesianRadius x ≤ R →
      surfaceGaussianCurvature (D.rotationFamily t) (D.rotationNormal t x) x <
        surfaceGaussianCurvature (markedCapMap R A.cRight L k ρ)
          (markedCapNormal R L k ρ (markedCapCenterParameter R L)) (markedCapCenterParameter R L)) :
    Statements.FixedMarkedCap D R := by
  have hRp : 0 < R := A.b_pos.trans hR
  exact {
    length := L
    length_pos := hL
    map := markedCapMap R A.cRight L k ρ
    smooth_map := contDiff_markedCapMap hRp hL A.cRight k ρ
    embedding := isEmbedding_markedCapEmbeddingMap hRp hL hk.le hρ hsmall A.cRight
    immersion := fun _ hy => markedCapMap_fderiv_injective hRp hL hk.le hρ hsmall A.cRight hy
    boundary := fun _ hy => markedCap_boundary hRp hL hρ hsmall A.cRight hy
    open_collar := markedCap_open_physical_collar hRp hL hρ hsmall A.cRight
    separation := fun t => markedCap_intersection_eq_rim D hR hL hρ hsmall t (hmeet t)
    bottom := A.cRight - L * capDrop
    bottom_gap := hgap
    bottom_inside := fun _ hy hr => markedCap_inside_cylinder_bottom hRp hL hρ hsmall A.cRight hy hr
    bottom_filled := fun _ hx => markedCap_bottom_filled hRp hL hρ hsmall A.cRight hx
    normal := markedCapNormal R L k ρ
    smooth_normal := contDiff_markedCapNormal hRp hL k ρ
    unit_normal := fun y _ => isUnitSurfaceNormal_markedCap hRp hL hρ hsmall A.cRight y
    marker := markedCapCenterParameter R L
    marker_interior := markedCapCenterParameter_mem hRp hL
    peak_cap := hcap
    peak_graph := hgraph
    principal := markedCap_hasDistinctPrincipalDirections hRp hL hk hρ hsmall A.cRight }

/-- Choose the marker strength from the actual curvature bounds, then choose
the support radius at the supplied length and within any positive height budget. -/
theorem IsometricGraphDevelopment.exists_markedCapSpecification_given_length
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L)
    (hgap : ∀ t x, cartesianRadius x ≤ R → A.cRight - L * capDrop < D.rotationFamily t x 2)
    (hmeet : ∀ t, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      ∃ C : Statements.FixedMarkedCap D R,
        C.length = L ∧ C.map = markedCapMap R A.cRight L k ρ ∧
        C.normal = markedCapNormal R L k ρ ∧ C.marker = markedCapCenterParameter R L ∧
        C.bottom = A.cRight - L * capDrop := by
  obtain ⟨B, _, hbound⟩ := D.exists_rotationFamily_curvature_bounds R
  obtain ⟨k, hk, hBk, hradius⟩ :=
    exists_markedCap_unique_peak (A.b_pos.trans hR) hL A.cRight B
  refine ⟨k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, hcenter, hcap⟩ := hradius ε hε
  let C := D.markedCapSpecification (k := k) (ρ := ρ) hR hL hk hρ hsmall hgap hmeet
    (by
      intro y hy hne
      rw [hcenter]
      exact hcap y hy hne)
    (by
      intro t x hx
      rw [hcenter]
      exact (le_abs_self _).trans_lt ((hbound t x hx).1.trans_lt hBk))
  exact ⟨ρ, hρ, hsmall, hheight, C, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual fixed marked cap output in the public G06 statement. -/
theorem markedCap_G06_statement : Statements.G06Statement := by
  intro A D R hR
  obtain ⟨L, hL, _, hgap, _, hmeet, _⟩ := D.exists_markedSphere_common_cap_length hR
  obtain ⟨_, _, hradius⟩ := D.exists_markedCapSpecification_given_length hR hL hgap hmeet
  obtain ⟨_, _, _, _, C, _⟩ := hradius 1 zero_lt_one
  exact ⟨C⟩

end ContinuousFlexibility
