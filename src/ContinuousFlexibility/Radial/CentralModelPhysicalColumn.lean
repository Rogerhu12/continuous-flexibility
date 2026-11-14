module

public import ContinuousFlexibility.Radial.CentralModelColumnInverse
public import ContinuousFlexibility.Radial.ReferenceCentralInverse

/-!
# The physical column in the ordinary central Liouville model

Here s = sqrt(w(R) / R') = sqrt(scale) * centralDensityRoot.
The model column is R' * g(R) / s. Its ordinary dx ground pairing
is the ordinary dr pairing divided only by the explicit normalizations.
This differs from the weighted radial Hilbert transform.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

theorem centralModelLiouvilleDensity_eq {scale : ℝ} (hscale : 0 < scale) (x : ℝ) :
    sqrt (centralRadialProfile scale (centralRadius x) / deriv centralRadius x) =
      sqrt scale * centralDensityRoot x := by
  have heq : centralRadialProfile scale (centralRadius x) / deriv centralRadius x =
      scale * centralDensityRoot x ^ 2 := by
    rw [centralRadialProfile_pullback]
    field_simp [(deriv_centralRadius_pos x).ne']
  rw [heq, sqrt_mul hscale.le, sqrt_sq (centralDensityRoot_pos x).le]

def centralModelPhysicalColumnFunction (scale : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv centralRadius x / (sqrt scale * centralDensityRoot x) * g (centralRadius x)

theorem centralModelPhysicalColumnFunction_liouville {scale : ℝ} (hscale : 0 < scale)
    (g : ℝ → ℝ) (x : ℝ) :
    centralModelPhysicalColumnFunction scale g x =
      deriv centralRadius x /
        sqrt (centralRadialProfile scale (centralRadius x) / deriv centralRadius x) *
          g (centralRadius x) := by
  rw [centralModelLiouvilleDensity_eq hscale]
  rfl

theorem contDiff_centralModelPhysicalColumnFunction {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (centralModelPhysicalColumnFunction scale g) := by
  have hd : ContDiff ℝ ∞ (deriv centralRadius) :=
    (contDiff_infty_iff_deriv.mp contDiff_centralRadius).2
  exact (hd.div (contDiff_const.mul contDiff_centralDensityRoot)
    (fun x => mul_ne_zero (sqrt_pos.mpr hscale).ne'
      (centralDensityRoot_pos x).ne')).mul (hg.comp contDiff_centralRadius)

theorem centralModelPhysicalColumnFunction_tsupport_subset (scale : ℝ) (g : ℝ → ℝ) :
    tsupport (centralModelPhysicalColumnFunction scale g) ⊆
      centralRadius ⁻¹' tsupport g := by
  apply closure_minimal
  · intro x hx
    change centralRadius x ∈ tsupport g
    apply subset_tsupport g
    intro hz
    apply hx
    change centralModelPhysicalColumnFunction scale g x = 0
    simp only [centralModelPhysicalColumnFunction, hz, mul_zero]
  · exact (isClosed_tsupport g).preimage contDiff_centralRadius.continuous

theorem centralModelPhysicalColumnFunction_hasCompactSupport (scale : ℝ)
    {g : ℝ → ℝ} (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi 0) :
    HasCompactSupport (centralModelPhysicalColumnFunction scale g) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (centralRadialTestPullback_hasCompactSupport hc hp)
  intro x hx
  apply subset_tsupport (centralRadialTestPullback g)
  change centralDensityRoot x * g (centralRadius x) ≠ 0
  apply mul_ne_zero (centralDensityRoot_pos x).ne'
  intro hz
  apply hx
  change centralModelPhysicalColumnFunction scale g x = 0
  simp only [centralModelPhysicalColumnFunction, hz, mul_zero]

theorem centralModelPhysicalColumnFunction_memLp {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    MemLp (centralModelPhysicalColumnFunction scale g) 2 volume :=
  (contDiff_centralModelPhysicalColumnFunction hscale hg).continuous.memLp_of_hasCompactSupport
    (centralModelPhysicalColumnFunction_hasCompactSupport scale hc hp)

def centralModelPhysicalColumn {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) : HermiteL2 :=
  (centralModelPhysicalColumnFunction_memLp hscale hg hc hp).toLp
    (centralModelPhysicalColumnFunction scale g)

theorem centralModelPhysicalColumn_ae {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    (centralModelPhysicalColumn hscale hg hc hp : ℝ → ℝ) =ᵐ[volume]
      centralModelPhysicalColumnFunction scale g :=
  (centralModelPhysicalColumnFunction_memLp hscale hg hc hp).coeFn_toLp

private theorem model_ground_normalization (x : ℝ) :
    oscillatorHermiteNorm 2 0 * normalizedOscillatorHermite 2 0 x =
      centralOscillatorGround x := by
  have hm : oscillatorHermiteMode 2 0 x = centralOscillatorGround x := by
    rw [oscillatorHermiteMode_eq]
    simp only [hermitePolynomial_zero, Polynomial.eval_one, one_mul]
    unfold centralOscillatorGround
    congr 1
    ring
  unfold normalizedOscillatorHermite
  rw [hm]
  field_simp [(oscillatorHermiteNorm_pos (by norm_num : (0 : ℝ) < 2) 0).ne']

private theorem model_column_times_ground {scale : ℝ} (hscale : 0 < scale)
    (g : ℝ → ℝ) (x : ℝ) :
    centralModelPhysicalColumnFunction scale g x * normalizedOscillatorHermite 2 0 x =
      (deriv centralRadius x * (g (centralRadius x) * centralKernelHeight (centralRadius x))) /
        (sqrt scale * oscillatorHermiteNorm 2 0) := by
  have hN := (oscillatorHermiteNorm_pos (by norm_num : (0 : ℝ) < 2) 0).ne'
  have hn : normalizedOscillatorHermite 2 0 x =
      centralOscillatorGround x / oscillatorHermiteNorm 2 0 := by
    apply (eq_div_iff hN).mpr
    simpa only [mul_comm] using model_ground_normalization x
  rw [centralModelPhysicalColumnFunction, hn, centralKernelHeight_liouville_pullback]
  field_simp [(sqrt_pos.mpr hscale).ne', (centralDensityRoot_pos x).ne', hN] <;> ring

/-- The precise Jacobian and both scalar normalizations are retained. -/
theorem centralModelPhysicalColumn_ground_pairing {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    ⟪centralModelGroundVector, centralModelPhysicalColumn hscale hg hc hp⟫_ℝ =
      (∫ r : ℝ, g r * centralKernelHeight r) /
        (sqrt scale * oscillatorHermiteNorm 2 0) := by
  have hinner : ⟪centralModelGroundVector, centralModelPhysicalColumn hscale hg hc hp⟫_ℝ =
      ∫ x, centralModelPhysicalColumnFunction scale g x *
        normalizedOscillatorHermite 2 0 x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hermiteL2Vector_coeFn (by norm_num : (0 : ℝ) < 2) 0,
      centralModelPhysicalColumn_ae hscale hg hc hp] with x hk hg'
    simp only [RCLike.inner_apply, conj_trivial, centralModelGroundVector, hk, hg', mul_comm]
  have heq : (fun x => centralModelPhysicalColumnFunction scale g x *
      normalizedOscillatorHermite 2 0 x) = fun x =>
        (deriv centralRadius x * (g (centralRadius x) * centralKernelHeight (centralRadius x))) /
          (sqrt scale * oscillatorHermiteNorm 2 0) :=
    funext (model_column_times_ground hscale g)
  have hwhole : (∫ r in Ioi 0, g r * centralKernelHeight r) =
      ∫ r : ℝ, g r * centralKernelHeight r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hz : g r = 0 := image_eq_zero_of_notMem_tsupport (fun h => hr (hp h))
    change g r * centralKernelHeight r = 0
    rw [hz, zero_mul]
  rw [hinner, heq, integral_div,
    ← centralRadius_integral_change (fun r => g r * centralKernelHeight r), hwhole]

theorem centralModelPhysicalColumn_ground_pairing_ne_zero {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0) :
    ⟪centralModelGroundVector, centralModelPhysicalColumn hscale hg hc hp⟫_ℝ ≠ 0 := by
  rw [centralModelPhysicalColumn_ground_pairing hscale hg hc hp]
  exact div_ne_zero hpair (mul_ne_zero (sqrt_pos.mpr hscale).ne'
    (oscillatorHermiteNorm_pos (by norm_num : (0 : ℝ) < 2) 0).ne')

theorem exists_centralModelPhysicalColumnInverse {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0)
    (hpair : (∫ r : ℝ, g r * centralKernelHeight r) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
      ‖G‖ ≤ C ∧
      (∀ F, BorderedFullGraph (centralPotential 2) (centralModelPhysicalColumn hscale hg hc hp)
        true (G F) F) ∧
      (∀ U F, BorderedFullGraph (centralPotential 2)
        (centralModelPhysicalColumn hscale hg hc hp) true U F → G F = U) :=
  exists_centralModelColumnInverse (centralModelPhysicalColumn hscale hg hc hp)
    (centralModelPhysicalColumn_ground_pairing_ne_zero hscale hg hc hp hpair)

/-- The R09 central model inverse for the actual column of this reference. -/
def ReferenceCentralModelInverseRealization (D : ReferenceData) (l h : ℝ) : Prop :=
  ∃ scale amplitude : ℝ, ∃ hscale : 0 < scale,
    amplitude ≠ 0 ∧ EqOn D.w (centralRadialProfile scale) (Ioo l h) ∧
    EqOn D.phi (fun r => amplitude * centralKernelHeight r) (Ioo l h) ∧
    ∃ (hg : ContDiff ℝ ∞ (referenceColumn D))
      (hc : HasCompactSupport (referenceColumn D))
      (hp : tsupport (referenceColumn D) ⊆ Ioi 0),
      ∃ C : ℝ, 0 < C ∧ ∃ G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
        ‖G‖ ≤ C ∧
        (∀ F, BorderedFullGraph (centralPotential 2)
          (centralModelPhysicalColumn hscale hg hc hp) true (G F) F) ∧
        (∀ U F, BorderedFullGraph (centralPotential 2)
          (centralModelPhysicalColumn hscale hg hc hp) true U F → G F = U)

theorem ConnectedReferenceGeometry.centralModelInverseRealization
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes) :
    ReferenceCentralModelInverseRealization Γ.reference Γ.centralLeft Γ.centralRight := by
  obtain ⟨scale, amplitude, hscale, hamplitude, hwmodel, hφmodel,
      hg, hc, hp, hpair, _⟩ := ConnectedReferenceGeometry.centralInverseRealization hΓ
  refine ⟨scale, amplitude, hscale, hamplitude, hwmodel, hφmodel, hg, hc, hp, ?_⟩
  apply exists_centralModelPhysicalColumnInverse hscale hg hc hp
  rw [hpair]
  exact div_ne_zero one_ne_zero hamplitude

theorem exists_connectedReferenceGeometry_model_inverse (hR08 : R08Statement)
    (requiredHead : ℝ) (hhead : 0 < requiredHead) :
    ∃ Γ : ConnectedReferenceGeometry,
      Γ.headLength = requiredHead ∧ Γ.Realizes ∧
      ReferenceCentralModelInverseRealization Γ.reference Γ.centralLeft Γ.centralRight := by
  obtain ⟨Γ, hlength, hΓ⟩ := exists_connectedReferenceGeometry hR08 requiredHead hhead
  exact ⟨Γ, hlength, hΓ, ConnectedReferenceGeometry.centralModelInverseRealization hΓ⟩

end ContinuousFlexibility.Radial
