import ContinuousFlexibility.Geometry.GraphRotationFamily

/-!
# Actual ambient rotations of the graph-disk images

The ambient map is a genuine Euclidean linear isometry equivalence of
`E3`. Image identities concern the whole closed graph disk, and do not
assert noncongruence of closed surfaces before attaching a marked cap.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def axialRotationMap (t : ℝ) (v : E3) : E3 :=
  (planarRotation t (graphBaseProjection v)).1 • e3Basis 0 +
    (planarRotation t (graphBaseProjection v)).2 • e3Basis 1 + v 2 • e3Basis 2

@[simp] theorem axialRotationMap_base (t : ℝ) (v : E3) :
    graphBaseProjection (axialRotationMap t v) = planarRotation t (graphBaseProjection v) := by
  apply Prod.ext <;> simp [axialRotationMap, graphBaseProjection, e3Basis]

@[simp] theorem axialRotationMap_height (t : ℝ) (v : E3) :
    axialRotationMap t v 2 = v 2 := by
  simp [axialRotationMap, e3Basis]

theorem e3_eq_of_base_height {u v : E3}
    (hb : graphBaseProjection u = graphBaseProjection v) (hz : u 2 = v 2) : u = v := by
  ext i
  fin_cases i
  · exact congrArg Prod.fst hb
  · exact congrArg Prod.snd hb
  · exact hz

@[simp] theorem axialRotationMap_zero (v : E3) : axialRotationMap 0 v = v := by
  apply e3_eq_of_base_height
  · simp
  · simp

theorem axialRotationMap_add (t s : ℝ) (v : E3) :
    axialRotationMap (t + s) v = axialRotationMap t (axialRotationMap s v) := by
  apply e3_eq_of_base_height
  · simp only [axialRotationMap_base, planarRotation_add]
  · simp

theorem axialRotationMap_inner (t : ℝ) (u v : E3) :
    inner ℝ (axialRotationMap t u) (axialRotationMap t v) = inner ℝ u v := by
  have hp := planarRotation_metric t (graphBaseProjection u) (graphBaseProjection v)
  rw [e3_inner_coordinates, e3_inner_coordinates]
  have hbu := axialRotationMap_base t u
  have hbv := axialRotationMap_base t v
  change (axialRotationMap t u) 0 * (axialRotationMap t v) 0 +
    (axialRotationMap t u) 1 * (axialRotationMap t v) 1 +
    (axialRotationMap t u) 2 * (axialRotationMap t v) 2 = _
  rw [axialRotationMap_height, axialRotationMap_height]
  have hpair : (axialRotationMap t u) 0 * (axialRotationMap t v) 0 +
      (axialRotationMap t u) 1 * (axialRotationMap t v) 1 = u 0 * v 0 + u 1 * v 1 := by
    change coordinateEuclideanPair (graphBaseProjection (axialRotationMap t u))
      (graphBaseProjection (axialRotationMap t v)) =
        coordinateEuclideanPair (graphBaseProjection u) (graphBaseProjection v)
    rw [hbu, hbv]
    exact hp
  rw [hpair]

def axialRotationLinearMap (t : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun := axialRotationMap t
  map_add' u v := by
    apply e3_eq_of_base_height
    · change graphBaseProjection (axialRotationMap t (u + v)) =
        graphBaseProjection (axialRotationMap t u) + graphBaseProjection (axialRotationMap t v)
      rw [axialRotationMap_base, axialRotationMap_base, axialRotationMap_base]
      exact (planarRotation t).map_add (graphBaseProjection u) (graphBaseProjection v)
    · simp
  map_smul' c v := by
    apply e3_eq_of_base_height
    · change graphBaseProjection (axialRotationMap t (c • v)) =
        c • graphBaseProjection (axialRotationMap t v)
      rw [axialRotationMap_base, axialRotationMap_base]
      exact (planarRotation t).map_smul c (graphBaseProjection v)
    · simp

/-- Actual Euclidean rotation about the third coordinate axis. -/
def axialRotation (t : ℝ) : E3 ≃ₗᵢ[ℝ] E3 where
  toLinearEquiv := {
    toLinearMap := axialRotationLinearMap t
    invFun := axialRotationMap (-t)
    left_inv := fun v => by
      change axialRotationMap (-t) (axialRotationMap t v) = v
      rw [← axialRotationMap_add, neg_add_cancel, axialRotationMap_zero]
    right_inv := fun v => by
      change axialRotationMap t (axialRotationMap (-t) v) = v
      rw [← axialRotationMap_add, add_neg_cancel, axialRotationMap_zero] }
  norm_map' := (LinearMap.norm_map_iff_inner_map_map (axialRotationLinearMap t)).mpr
    (axialRotationMap_inner t)

@[simp] theorem axialRotation_apply (t : ℝ) (v : E3) :
    axialRotation t v = axialRotationMap t v := rfl

theorem contDiff_axialRotation_joint :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => axialRotation q.1 q.2) := by
  simp only [axialRotation_apply]
  have ha : ContDiff ℝ ∞ (fun q : ℝ × E3 => 2 * Real.pi * q.1) :=
    contDiff_const.mul contDiff_fst
  have hx : ContDiff ℝ ∞ (fun q : ℝ × E3 => q.2 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.comp contDiff_snd
  have hy : ContDiff ℝ ∞ (fun q : ℝ × E3 => q.2 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.comp contDiff_snd
  have hz : ContDiff ℝ ∞ (fun q : ℝ × E3 => q.2 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.comp contDiff_snd
  have h := ((((ha.cos.mul hx).sub (ha.sin.mul hy)).smul_const (e3Basis 0)).add
    (((ha.sin.mul hx).add (ha.cos.mul hy)).smul_const (e3Basis 1))).add
      (hz.smul_const (e3Basis 2))
  simpa only [axialRotationMap, planarRotation, planeRotationLinearMap_apply,
    graphBaseProjection] using h

theorem axialRotation_periodic : Function.Periodic axialRotation 1 := by
  intro t
  apply LinearIsometryEquiv.ext
  intro v
  apply e3_eq_of_base_height
  · simp only [axialRotation_apply, axialRotationMap_base, planarRotation_add_one]
  · simp

theorem IsometricGraphDevelopment.rotationFamily_eq_axialRotation
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    D.rotationFamily t x = axialRotation (-t) (D.map (planarRotation t x)) := by
  apply e3_eq_of_base_height
  · simp only [IsometricGraphDevelopment.rotationFamily, IsometricGraphDevelopment.map,
      graphBaseProjection_graphMap, rotationConjugate_apply, axialRotation_apply,
      axialRotationMap_base]
  · simp only [IsometricGraphDevelopment.rotationFamily, IsometricGraphDevelopment.map,
      graphMap_two, rotatedHeight, axialRotation_apply, axialRotationMap_height]

theorem planarRotation_image_closedCartesianDisk (t R : ℝ) :
    planarRotation t '' {x : PolarPoint | cartesianRadius x ≤ R} =
      {x : PolarPoint | cartesianRadius x ≤ R} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_ofPred_eq, cartesianRadius_planarRotation] using hy
  · intro hx
    exact ⟨planarRotation (-t) x, by simpa using hx, planarRotation_neg_cancel t x⟩

theorem IsometricGraphDevelopment.rotationFamily_image_closedDisk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) :
    D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R} =
      axialRotation (-t) '' (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    change cartesianRadius x ≤ R at hx
    refine ⟨D.map (planarRotation t x), ⟨planarRotation t x, ?_, rfl⟩, ?_⟩
    · change cartesianRadius (planarRotation t x) ≤ R
      simpa only [cartesianRadius_planarRotation] using hx
    · exact (D.rotationFamily_eq_axialRotation t x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change cartesianRadius x ≤ R at hx
    refine ⟨planarRotation (-t) x, ?_, ?_⟩
    · change cartesianRadius (planarRotation (-t) x) ≤ R
      simpa only [cartesianRadius_planarRotation] using hx
    · rw [D.rotationFamily_eq_axialRotation, planarRotation_neg_cancel]

theorem IsometricGraphDevelopment.rotationFamily_projects_onto_disk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) {R : ℝ} (hR : A.b ≤ R) :
    graphBaseProjection '' (D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R}) =
      {x : PolarPoint | cartesianRadius x ≤ R} := by
  rw [D.rotationFamily_image_closedDisk]
  calc
    _ = (fun v => graphBaseProjection (axialRotation (-t) v)) ''
        (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) := image_image _ _ _
    _ = (fun v => planarRotation (-t) (graphBaseProjection v)) ''
        (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) := by
      congr 1
      funext v
      exact axialRotationMap_base (-t) v
    _ = planarRotation (-t) ''
        (graphBaseProjection '' (D.map '' {x : PolarPoint | cartesianRadius x ≤ R})) :=
      (image_image _ _ _).symm
    _ = _ := by rw [D.graph_projects_onto_disk hR, planarRotation_image_closedCartesianDisk]

theorem isCompact_closedCartesianDisk (R : ℝ) :
    IsCompact {x : PolarPoint | cartesianRadius x ≤ R} := by
  have heq : Complex.equivRealProdCLM '' Metric.closedBall (0 : ℂ) R =
      {x : PolarPoint | cartesianRadius x ≤ R} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have he : cartesianRadius (Complex.equivRealProdCLM z) = ‖z‖ := by
        unfold cartesianRadius
        rw [ContinuousLinearEquiv.symm_apply_apply]
      change cartesianRadius (Complex.equivRealProdCLM z) ≤ R
      rw [he]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    · intro hx
      refine ⟨Complex.equivRealProdCLM.symm x, ?_,
        Complex.equivRealProdCLM.apply_symm_apply x⟩
      simpa [cartesianRadius] using hx
  rw [← heq]
  exact (isCompact_closedBall (0 : ℂ) R).image Complex.equivRealProdCLM.continuous

/-- One genuine compactness bound controls the height of every rotated
graph disk. This gives the uniform room needed to place the bottom cap. -/
theorem IsometricGraphDevelopment.exists_rotationFamily_height_bounds
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R : ℝ) :
    ∃ lo hi : ℝ, ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
      lo ≤ D.rotationFamily t x 2 ∧ D.rotationFamily t x 2 ≤ hi := by
  have hc := isCompact_closedCartesianDisk R
  obtain ⟨lo, hlo⟩ := hc.bddBelow_image A.contDiff_cartesianHeight.continuous.continuousOn
  obtain ⟨hi, hhi⟩ := hc.bddAbove_image A.contDiff_cartesianHeight.continuous.continuousOn
  refine ⟨lo, hi, fun t x hx => ?_⟩
  have hm : A.cartesianHeight (planarRotation t x) ∈
      A.cartesianHeight '' {x : PolarPoint | cartesianRadius x ≤ R} :=
    ⟨planarRotation t x, by
      change cartesianRadius (planarRotation t x) ≤ R
      simpa only [cartesianRadius_planarRotation] using hx, rfl⟩
  constructor
  · simpa only [IsometricGraphDevelopment.rotationFamily, graphMap_two, rotatedHeight]
      using hlo hm
  · simpa only [IsometricGraphDevelopment.rotationFamily, graphMap_two, rotatedHeight]
      using hhi hm

end ContinuousFlexibility
