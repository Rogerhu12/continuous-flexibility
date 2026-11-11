import ContinuousFlexibility.Radial.CentralPositionInverse

/-!
# Position weights for the actual mode-two reduced inverse

The same closed differential and physical energy graphs are used at
frequency two. The genuine normalized Gaussian projection is retained
in every source equation; it is removed only through proved orthogonality.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

theorem centralEnergyShift_two : centralEnergyShift 2 = 3 := by
  unfold centralEnergyShift
  rw [centralRadiusA_sq]
  ring

theorem centralGroundProjection_inner_zero (f u : HermiteL2)
    (hu : hermiteCoefficient 2 u 0 = 0) :
    ⟪centralGroundProjection f, u⟫_ℝ = 0 := by
  rw [centralGroundProjection_apply, real_inner_smul_left,
    inner_hermiteL2Vector_left, hu, mul_zero]

theorem centralReducedHilbertInverse_inner_swap (f g : HermiteL2) :
    ⟪centralReducedHilbertInverse f, g⟫_ℝ =
      ⟪f, centralReducedHilbertInverse g⟫_ℝ := by
  have h := centralClosedGraph_symmetric (by norm_num : (0 : ℝ) < 2)
    (centralReducedHilbertInverse f) (f - centralGroundProjection f)
    (centralReducedHilbertInverse g) (g - centralGroundProjection g)
    (centralReducedHilbertInverse_graph_projected f) (centralReducedHilbertInverse_graph_projected g)
  rw [inner_sub_left, inner_sub_right,
    centralGroundProjection_inner_zero f _ (centralReducedHilbertInverse_zero_coefficient g)] at h
  have hp : ⟪centralReducedHilbertInverse f, centralGroundProjection g⟫_ℝ = 0 :=
    (real_inner_comm _ _).trans
      (centralGroundProjection_inner_zero g _ (centralReducedHilbertInverse_zero_coefficient f))
  rw [hp, sub_zero, sub_zero] at h
  exact h.symm

def centralReducedInverseEnergyLift (f : HermiteL2) : PhysicalEnergySpace 2 :=
  physicalFormRepresentative 2
    (f - centralGroundProjection f + centralEnergyShift 2 • centralReducedHilbertInverse f)

theorem centralReducedInverseEnergyLift_base (f : HermiteL2) :
    physicalEnergyBase 2 (centralReducedInverseEnergyLift f) = centralReducedHilbertInverse f := by
  apply (physicalClosedFormEquation_iff_representative _ _ _).mp
  exact physicalClosedFormEquation_of_mem_centralClosedGraph
    (by norm_num : (0 : ℝ) < 2) _ _ (centralReducedHilbertInverse_graph_projected f)

theorem centralReducedInverseEnergyLift_pairing (f : HermiteL2) (V : PhysicalEnergySpace 2) :
    ⟪centralReducedInverseEnergyLift f, V⟫_ℝ =
      ⟪f - centralGroundProjection f + centralEnergyShift 2 • centralReducedHilbertInverse f,
        physicalEnergyBase 2 V⟫_ℝ :=
  physicalFormRepresentative_pairing _ _ V

theorem centralReducedInverseEnergyLift_energy (f : HermiteL2) :
    ‖centralReducedInverseEnergyLift f‖ ^ 2 =
      ⟪f, centralReducedHilbertInverse f⟫_ℝ + 3 * ‖centralReducedHilbertInverse f‖ ^ 2 := by
  have h := centralReducedInverseEnergyLift_pairing f (centralReducedInverseEnergyLift f)
  rw [real_inner_self_eq_norm_sq, centralReducedInverseEnergyLift_base,
    inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    centralGroundProjection_inner_zero f _ (centralReducedHilbertInverse_zero_coefficient f),
    sub_zero, centralEnergyShift_two] at h
  exact h

theorem centralReducedInverseEnergyLift_norm_bound (f : HermiteL2) :
    ‖centralReducedInverseEnergyLift f‖ ≤ 2 * ‖f‖ := by
  let F : ℝ := ‖f‖
  let u := centralReducedHilbertInverse f
  have hu : ‖u‖ ≤ (1 / 4 : ℝ) * F := centralReducedHilbertInverse_bound f
  have husq : ‖u‖ ^ 2 ≤ (1 / 16 : ℝ) * F ^ 2 := by
    calc
      _ ≤ ((1 / 4 : ℝ) * F) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      _ = _ := by ring
  have hfirst : F * ‖u‖ ≤ (1 / 4 : ℝ) * F ^ 2 := by
    calc
      _ ≤ F * ((1 / 4 : ℝ) * F) := mul_le_mul_of_nonneg_left hu (norm_nonneg f)
      _ = _ := by ring
  have hsq : ‖centralReducedInverseEnergyLift f‖ ^ 2 ≤ (7 / 16 : ℝ) * F ^ 2 := by
    calc
      _ = ⟪f, u⟫_ℝ + 3 * ‖u‖ ^ 2 := centralReducedInverseEnergyLift_energy f
      _ ≤ F * ‖u‖ + 3 * ‖u‖ ^ 2 := add_le_add (real_inner_le_norm f u) le_rfl
      _ ≤ (1 / 4 : ℝ) * F ^ 2 + 3 * ((1 / 16 : ℝ) * F ^ 2) :=
        add_le_add hfirst (mul_le_mul_of_nonneg_left husq (by norm_num))
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg f))).mp
  nlinarith only [hsq, sq_nonneg F]

def centralReducedPositionInverseValue (f : HermiteL2) : HermiteL2 :=
  (2 : ℝ)⁻¹ • physicalEnergyPosition 2 (centralReducedInverseEnergyLift f)

theorem centralReducedPositionInverseValue_ae (f : HermiteL2) :
    HasPositionL2 (centralReducedHilbertInverse f) (centralReducedPositionInverseValue f) := by
  have h := physicalEnergy_scaledPosition_ae (by norm_num : (0 : ℝ) < 2)
    (centralReducedInverseEnergyLift f)
  rwa [centralReducedInverseEnergyLift_base] at h

theorem centralReducedPositionInverseValue_norm_bound (f : HermiteL2) :
    ‖centralReducedPositionInverseValue f‖ ≤ ‖f‖ := by
  have hp : ‖physicalEnergyPosition 2 (centralReducedInverseEnergyLift f)‖ ≤ 2 * ‖f‖ :=
    (physicalEnergyCoordinate_norm_le 2 2 _).trans (centralReducedInverseEnergyLift_norm_bound f)
  calc
    _ = (1 / 2 : ℝ) * ‖physicalEnergyPosition 2 (centralReducedInverseEnergyLift f)‖ := by
      rw [centralReducedPositionInverseValue, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

theorem centralReducedHilbertInverse_position_memLp (f : HermiteL2) :
    MemLp (fun x : ℝ => x * centralReducedHilbertInverse f x) 2 volume :=
  (memLp_congr_ae (centralReducedPositionInverseValue_ae f)).mp
    (Lp.memLp (centralReducedPositionInverseValue f))

private def centralReducedPositionInverseLinearMap : HermiteL2 →ₗ[ℝ] HermiteL2 where
  toFun := centralReducedPositionInverseValue
  map_add' f g := by
    apply Lp.ext
    have hsum := centralReducedPositionInverseValue_ae (f + g)
    rw [centralReducedHilbertInverse.map_add] at hsum
    filter_upwards [hsum, centralReducedPositionInverseValue_ae f,
      centralReducedPositionInverseValue_ae g,
      Lp.coeFn_add (centralReducedHilbertInverse f) (centralReducedHilbertInverse g),
      Lp.coeFn_add (centralReducedPositionInverseValue f) (centralReducedPositionInverseValue g)]
      with x hs hf hg hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.add_apply]
    rw [hf, hg]
    ring
  map_smul' a f := by
    change centralReducedPositionInverseValue (a • f) = a • centralReducedPositionInverseValue f
    apply Lp.ext
    have hscale := centralReducedPositionInverseValue_ae (a • f)
    rw [centralReducedHilbertInverse.map_smul] at hscale
    filter_upwards [hscale, centralReducedPositionInverseValue_ae f,
      Lp.coeFn_smul a (centralReducedHilbertInverse f),
      Lp.coeFn_smul a (centralReducedPositionInverseValue f)] with x hs hf hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    ring

def centralReducedPositionInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  centralReducedPositionInverseLinearMap.mkContinuous 1
    (fun f => by
      change ‖centralReducedPositionInverseValue f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using centralReducedPositionInverseValue_norm_bound f)

theorem centralReducedPositionInverse_norm_le : ‖centralReducedPositionInverse‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem centralReducedPositionInverse_ae (f : HermiteL2) :
    HasPositionL2 (centralReducedHilbertInverse f) (centralReducedPositionInverse f) :=
  centralReducedPositionInverseValue_ae f

def centralReducedRightPositionInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  ContinuousLinearMap.adjoint centralReducedPositionInverse

theorem centralReducedRightPositionInverse_norm_le : ‖centralReducedRightPositionInverse‖ ≤ 1 :=
  (ContinuousLinearMap.adjoint.norm_map centralReducedPositionInverse).trans_le
    centralReducedPositionInverse_norm_le

theorem centralReducedRightPositionInverse_bound (f : HermiteL2) :
    ‖centralReducedRightPositionInverse f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using
    centralReducedRightPositionInverse.le_of_opNorm_le centralReducedRightPositionInverse_norm_le f

theorem centralReducedRightPositionInverse_eq (f xf : HermiteL2) (hf : HasPositionL2 f xf) :
    centralReducedRightPositionInverse f = centralReducedHilbertInverse xf := by
  apply ext_inner_right ℝ
  intro g
  change ⟪ContinuousLinearMap.adjoint centralReducedPositionInverse f, g⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    _ = ⟪xf, centralReducedHilbertInverse g⟫_ℝ :=
      (positionL2_pairing_swap hf (centralReducedPositionInverse_ae g)).symm
    _ = _ := (centralReducedHilbertInverse_inner_swap xf g).symm

theorem centralReducedHilbertInverse_mode (m : ℕ) :
    centralReducedHilbertInverse (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) m) =
      (4 * (m : ℝ))⁻¹ • hermiteL2Vector (by norm_num : (0 : ℝ) < 2) m :=
  hermiteBoundedMultiplier_vector _ _ _ _ _ m

theorem centralReducedPositionInverse_mode (m : ℕ) :
    centralReducedPositionInverse (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) m) =
      (4 * (m : ℝ))⁻¹ • centralHermitePositionVector (by norm_num : (0 : ℝ) < 2) m := by
  have hX : HasPositionL2
      (centralReducedHilbertInverse (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) m))
      (centralReducedPositionInverse (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) m)) :=
    centralReducedPositionInverse_ae _
  rw [centralReducedHilbertInverse_mode] at hX
  exact hX.unique ((centralHermitePositionVector_ae (by norm_num : (0 : ℝ) < 2) m).smul _)

theorem centralReducedRightPositionInverse_coefficient (f : HermiteL2) (m : ℕ) :
    hermiteCoefficient 2 (centralReducedRightPositionInverse f) m =
      (4 * (m : ℝ))⁻¹ * ⟪f, centralHermitePositionVector (by norm_num : (0 : ℝ) < 2) m⟫_ℝ := by
  rw [← inner_hermiteL2Vector_right (by norm_num : (0 : ℝ) < 2)]
  change ⟪ContinuousLinearMap.adjoint centralReducedPositionInverse f,
    hermiteL2Vector (by norm_num : (0 : ℝ) < 2) m⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_left, centralReducedPositionInverse_mode,
    real_inner_smul_right]

theorem centralReducedRightPositionInverse_zero_coefficient (f : HermiteL2) :
    hermiteCoefficient 2 (centralReducedRightPositionInverse f) 0 = 0 := by
  rw [centralReducedRightPositionInverse_coefficient]
  norm_num

theorem centralReducedRightPositionInverse_coefficient_energy (f : HermiteL2)
    (m : ℕ) (hm : m ≠ 0) :
    4 * (m : ℝ) * hermiteCoefficient 2 (centralReducedRightPositionInverse f) m =
      ⟪f, centralHermitePositionVector (by norm_num : (0 : ℝ) < 2) m⟫_ℝ := by
  rw [centralReducedRightPositionInverse_coefficient]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp

/-- The rank-one source correction is retained in the physical right
energy functional. It is the actual Gaussian projection of `Xf`. -/
def centralReducedRightEnergyFunctional (f : HermiteL2) : StrongDual ℝ (PhysicalEnergySpace 2) :=
  ((innerSL ℝ f).comp ((2 : ℝ)⁻¹ • physicalEnergyPosition 2)) -
    ⟪f, centralHermitePositionVector (by norm_num : (0 : ℝ) < 2) 0⟫_ℝ •
      ((innerSL ℝ (hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0)).comp (physicalEnergyBase 2)) +
    (3 : ℝ) • ((innerSL ℝ (centralReducedRightPositionInverse f)).comp (physicalEnergyBase 2))

def centralReducedRightInverseEnergyLift (f : HermiteL2) : PhysicalEnergySpace 2 :=
  (InnerProductSpace.toDual ℝ (PhysicalEnergySpace 2)).symm (centralReducedRightEnergyFunctional f)

theorem centralReducedRightInverseEnergyLift_pairing (f : HermiteL2) (V : PhysicalEnergySpace 2) :
    ⟪centralReducedRightInverseEnergyLift f, V⟫_ℝ =
      ⟪f, (2 : ℝ)⁻¹ • physicalEnergyPosition 2 V⟫_ℝ -
        ⟪f, centralHermitePositionVector (by norm_num : (0 : ℝ) < 2) 0⟫_ℝ *
          ⟪hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0, physicalEnergyBase 2 V⟫_ℝ +
        3 * ⟪centralReducedRightPositionInverse f, physicalEnergyBase 2 V⟫_ℝ :=
  InnerProductSpace.toDual_symm_apply

/-- The actual projected weak right-source has the intended physical
base, including its zero Gaussian coefficient. -/
theorem centralReducedRightInverseEnergyLift_base (f : HermiteL2) :
    physicalEnergyBase 2 (centralReducedRightInverseEnergyLift f) =
      centralReducedRightPositionInverse f := by
  apply (hermiteCoefficientTransform (by norm_num : (0 : ℝ) < 2)).injective
  apply lp.ext
  funext m
  rw [hermiteCoefficientTransform_apply, hermiteCoefficientTransform_apply]
  have h := centralReducedRightInverseEnergyLift_pairing f
    (physicalHermiteLift (by norm_num : (0 : ℝ) < 2) m)
  rw [physicalEnergy_inner_hermite, physicalHermiteLift_scaledPosition, physicalHermiteLift_base,
    inner_hermiteL2Vector_left, hermiteCoefficient_hermiteL2Vector,
    inner_hermiteL2Vector_right] at h
  by_cases hm : m = 0
  · subst m
    rw [centralReducedRightPositionInverse_zero_coefficient] at h ⊢
    norm_num [physicalHermiteWeight] at h
    simpa only [physicalEnergyBase_apply] using h
  · have h0m : ¬0 = m := Ne.symm hm
    simp only [ite_eq_right h0m, mul_zero, sub_zero] at h
    rw [← centralReducedRightPositionInverse_coefficient_energy f m hm] at h
    have hw : 4 * (m : ℝ) + 3 = physicalHermiteWeight 2 m := by
      unfold physicalHermiteWeight
      ring
    rw [← add_mul, hw] at h
    exact mul_left_cancel₀ (physicalHermiteWeight_pos (by norm_num : (0 : ℝ) < 2) m).ne' h

def centralReducedDoublePositionInverseValue (f : HermiteL2) : HermiteL2 :=
  (2 : ℝ)⁻¹ • physicalEnergyPosition 2 (centralReducedRightInverseEnergyLift f)

theorem centralReducedDoublePositionInverseValue_ae (f : HermiteL2) :
    HasPositionL2 (centralReducedRightPositionInverse f) (centralReducedDoublePositionInverseValue f) := by
  have h := physicalEnergy_scaledPosition_ae (by norm_num : (0 : ℝ) < 2)
    (centralReducedRightInverseEnergyLift f)
  rwa [centralReducedRightInverseEnergyLift_base] at h

theorem centralReducedRightInverseEnergyLift_energy (f : HermiteL2) :
    ‖centralReducedRightInverseEnergyLift f‖ ^ 2 =
      ⟪f, centralReducedDoublePositionInverseValue f⟫_ℝ +
        3 * ‖centralReducedRightPositionInverse f‖ ^ 2 := by
  have h := centralReducedRightInverseEnergyLift_pairing f (centralReducedRightInverseEnergyLift f)
  rw [real_inner_self_eq_norm_sq, centralReducedRightInverseEnergyLift_base,
    inner_hermiteL2Vector_left, centralReducedRightPositionInverse_zero_coefficient,
    mul_zero, sub_zero, real_inner_self_eq_norm_sq] at h
  exact h

/-- The actual rank-one correction vanishes only after testing the
proved zero-ground-component right inverse. Energy absorption then
controls the genuine two-sided position weight. -/
theorem centralReducedDoublePositionInverseValue_norm_bound (f : HermiteL2) :
    ‖centralReducedDoublePositionInverseValue f‖ ≤ ‖f‖ := by
  let p : ℝ := ‖centralReducedDoublePositionInverseValue f‖
  let F : ℝ := ‖f‖
  let U := centralReducedRightInverseEnergyLift f
  have hpos : (2 : ℝ) • centralReducedDoublePositionInverseValue f = physicalEnergyPosition 2 U := by
    change (2 : ℝ) • ((2 : ℝ)⁻¹ • physicalEnergyPosition 2 U) = _
    rw [smul_smul]
    norm_num
  have hnorm := congrArg (fun v : HermiteL2 => ‖v‖ ^ 2) hpos
  rw [norm_smul, mul_pow] at hnorm
  norm_num at hnorm
  have hcoor : ‖physicalEnergyPosition 2 U‖ ≤ ‖U‖ := physicalEnergyCoordinate_norm_le 2 2 U
  have hleft : 4 * p ^ 2 ≤ ‖U‖ ^ 2 :=
    hnorm.trans_le (pow_le_pow_left₀ (norm_nonneg _) hcoor 2)
  have hu := centralReducedRightPositionInverse_bound f
  have husq : ‖centralReducedRightPositionInverse f‖ ^ 2 ≤ F ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hmain : 4 * p ^ 2 ≤ F * p + 3 * F ^ 2 := by
    calc
      _ ≤ ‖U‖ ^ 2 := hleft
      _ = ⟪f, centralReducedDoublePositionInverseValue f⟫_ℝ +
          3 * ‖centralReducedRightPositionInverse f‖ ^ 2 := centralReducedRightInverseEnergyLift_energy f
      _ ≤ F * p + 3 * F ^ 2 :=
        add_le_add (real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left husq (by norm_num))
  change p ≤ F
  by_contra h
  have hlt : F < p := lt_of_not_ge h
  have hF : 0 ≤ F := norm_nonneg f
  have hp : 0 < p := hF.trans_lt hlt
  have hFp : F * p < p ^ 2 := by
    simpa only [pow_two] using mul_lt_mul_of_pos_right hlt hp
  have hF2 : F ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hF hlt.le 2
  have hstrict : F * p + 3 * F ^ 2 < 4 * p ^ 2 := by
    calc
      _ < p ^ 2 + 3 * F ^ 2 := add_lt_add_of_lt_of_le hFp le_rfl
      _ ≤ p ^ 2 + 3 * p ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hF2 (by norm_num))
      _ = _ := by ring
  exact (lt_irrefl (4 * p ^ 2)) (hmain.trans_lt hstrict)

private def centralReducedDoublePositionInverseLinearMap : HermiteL2 →ₗ[ℝ] HermiteL2 where
  toFun := centralReducedDoublePositionInverseValue
  map_add' f g := by
    apply Lp.ext
    have hsum := centralReducedDoublePositionInverseValue_ae (f + g)
    rw [centralReducedRightPositionInverse.map_add] at hsum
    filter_upwards [hsum, centralReducedDoublePositionInverseValue_ae f,
      centralReducedDoublePositionInverseValue_ae g,
      Lp.coeFn_add (centralReducedRightPositionInverse f) (centralReducedRightPositionInverse g),
      Lp.coeFn_add (centralReducedDoublePositionInverseValue f) (centralReducedDoublePositionInverseValue g)]
      with x hs hf hg hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.add_apply]
    rw [hf, hg]
    ring
  map_smul' a f := by
    change centralReducedDoublePositionInverseValue (a • f) = a • centralReducedDoublePositionInverseValue f
    apply Lp.ext
    have hscale := centralReducedDoublePositionInverseValue_ae (a • f)
    rw [centralReducedRightPositionInverse.map_smul] at hscale
    filter_upwards [hscale, centralReducedDoublePositionInverseValue_ae f,
      Lp.coeFn_smul a (centralReducedRightPositionInverse f),
      Lp.coeFn_smul a (centralReducedDoublePositionInverseValue f)] with x hs hf hgin hout
    rw [hs, hout, hgin]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    ring

def centralReducedDoublePositionInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  centralReducedDoublePositionInverseLinearMap.mkContinuous 1
    (fun f => by
      change ‖centralReducedDoublePositionInverseValue f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using centralReducedDoublePositionInverseValue_norm_bound f)

theorem centralReducedDoublePositionInverse_norm_le : ‖centralReducedDoublePositionInverse‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem centralReducedDoublePositionInverse_ae (f : HermiteL2) :
    HasPositionL2 (centralReducedRightPositionInverse f) (centralReducedDoublePositionInverse f) :=
  centralReducedDoublePositionInverseValue_ae f

theorem centralReducedDoublePositionInverse_eq (f xf : HermiteL2) (hf : HasPositionL2 f xf) :
    centralReducedDoublePositionInverse f = centralReducedPositionInverse xf := by
  have h := centralReducedDoublePositionInverse_ae f
  rw [centralReducedRightPositionInverse_eq f xf hf] at h
  exact h.unique (centralReducedPositionInverse_ae xf)

theorem centralReducedDoublePositionInverse_inner_swap (f g : HermiteL2) :
    ⟪centralReducedDoublePositionInverse f, g⟫_ℝ =
      ⟪f, centralReducedDoublePositionInverse g⟫_ℝ := by
  have hfg := centralReducedRightInverseEnergyLift_pairing f (centralReducedRightInverseEnergyLift g)
  have hgf := centralReducedRightInverseEnergyLift_pairing g (centralReducedRightInverseEnergyLift f)
  rw [centralReducedRightInverseEnergyLift_base, inner_hermiteL2Vector_left,
    centralReducedRightPositionInverse_zero_coefficient, mul_zero, sub_zero] at hfg hgf
  change ⟪centralReducedRightInverseEnergyLift f, centralReducedRightInverseEnergyLift g⟫_ℝ =
    ⟪f, centralReducedDoublePositionInverseValue g⟫_ℝ +
      3 * ⟪centralReducedRightPositionInverse f, centralReducedRightPositionInverse g⟫_ℝ at hfg
  change ⟪centralReducedRightInverseEnergyLift g, centralReducedRightInverseEnergyLift f⟫_ℝ =
    ⟪g, centralReducedDoublePositionInverseValue f⟫_ℝ +
      3 * ⟪centralReducedRightPositionInverse g, centralReducedRightPositionInverse f⟫_ℝ at hgf
  have hE := real_inner_comm (centralReducedRightInverseEnergyLift f) (centralReducedRightInverseEnergyLift g)
  have hR := real_inner_comm (centralReducedRightPositionInverse f) (centralReducedRightPositionInverse g)
  rw [hE, hR] at hgf
  have h : ⟪f, centralReducedDoublePositionInverseValue g⟫_ℝ =
      ⟪g, centralReducedDoublePositionInverseValue f⟫_ℝ := add_right_cancel (hfg.symm.trans hgf)
  change ⟪centralReducedDoublePositionInverseValue f, g⟫_ℝ =
    ⟪f, centralReducedDoublePositionInverseValue g⟫_ℝ
  exact (real_inner_comm _ _).trans h.symm

end ContinuousFlexibility.Radial
