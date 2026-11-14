import ContinuousFlexibility.Analysis.N01RootSpeedPowerMaterialJets
import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly
import ContinuousFlexibility.Analysis.N04bOpticalHeightVariation
import ContinuousFlexibility.Analysis.N05ReferenceResidual
import ContinuousFlexibility.Analysis.RetainedPositiveEndpointHostSample
import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets

/-!
# Fixed root-speed factors at the actual positive samples

The fixed factor is exactly the actual factored speed at the reference
state. The existing material theorem therefore bounds every finite list
of its ordinary radial derivatives. The retained endpoint geometry then
puts that bound at the original positive midpoint sample. The division
function and its actual root strip remain the ones used by the source.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n04PositiveGeometry_reference_grading_zero
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (x : E) (k : ℕ) : p k (x - x) ≤ 1 := by
  rw [sub_self, map_zero]
  exact zero_le_one

theorem n04PositiveGeometry_reference_grading_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (x : E) (k : ℕ) {a b : ℝ}
    (h : a ≤ b * (1 + p k (x - x))) : a ≤ b := by
  rw [sub_self, map_zero, add_zero, mul_one] at h
  exact h

/-- At the genuine reference state the actual denominator is the
reference profile and the discriminant is one. -/
theorem n04PositiveGeometry_referenceRootSpeedFactor_eq_actual
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hw : ContDiff ℝ ∞ D.w) (href : referenceStateConditions D S C)
    (g : ℝ → ℝ) (r σ : ℝ) :
    factoredCharacteristicSpeed D.w g (stateProfile D S C C.referenceState)
        (stateHeight D S C (C.referenceState, 0)) r σ =
      (fun p => referenceRootSpeedFactor D.w g r σ p.1) := by
  have hprimitive (x : ℝ) :
      HasDerivAt (fun y => ∫ t in D.b..y, D.w t) (D.w x) x :=
    (hw.continuous.integral_hasStrictDerivAt D.b x).hasDerivAt
  rw [n05_stateProfile_reference href, n05_stateHeight_reference href]
  funext p
  simp only [factoredCharacteristicSpeed,
    polarDiscriminant_radialHeightField hprimitive,
    n04b_heightQ_radialHeightField hprimitive, Real.sqrt_one, mul_one]
  rfl

theorem n04PositiveGeometry_scalar_radial_norm_le
    {f : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (j : ℕ) :
    |iteratedDeriv j f 0| ≤
      ‖iteratedFDeriv ℝ j (fun p : PolarPoint => f p.1) (0, 0)‖ := by
  let L : ℝ →L[ℝ] PolarPoint := ContinuousLinearMap.inl ℝ ℝ ℝ
  have hF : ContDiffAt ℝ ∞ (fun p : PolarPoint => f p.1) (L 0) :=
    hf.comp (L 0) contDiffAt_fst
  have hb := norm_iteratedFDeriv_comp_linear_le_at L hF j
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ ℝ ℝ
  have hp : ‖L‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  have he : (fun p : PolarPoint => f p.1) ∘ L = f := rfl
  rw [he, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq
    (by simp only [mul_one, L, ContinuousLinearMap.inl_apply]))

/-- For each fixed finite radial order there is one material cost before
every positive component, source, actual smooth division and root strip.
The endpoint orientation is the genuine opposite negative root. -/
theorem n04PositiveGeometry_referenceRootSpeedFactor_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
    ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
    ∀ side m, (X.src i side).val = some m →
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
      (∀ t, -deriv W.D.w (n01ComponentRoot W.C m (!side) +
        n01ComponentRootOrientation (!side) * t) = t * g t) →
    ∀ R : ℝ, 0 < R →
      RootCoefficientStripConditions W.D.w g
        (stateProfile W.D W.S W.C W.C.referenceState)
        (stateHeight W.D W.S W.C (W.C.referenceState, 0))
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) R →
    ∀ j : ℕ, j ≤ N →
      |iteratedDeriv j (referenceRootSpeedFactor W.D.w g
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side))) 0| ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B := by
  obtain ⟨C0, low, outLoss, hC0, hfloor, hpowers⟩ :=
    n01_rootSpeed_axis_rpow_material_jets_of_component_optical
      W.hS W.hT W.through03.1.1 X.κ_pos
  obtain ⟨A, hA, hjets⟩ := hpowers 1
  let B₀ : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), A j
  have hsum : 0 ≤ ∑ j ∈ Finset.range (N + 1), A j :=
    Finset.sum_nonneg fun j _ => (hA j).le
  have hB₀ : 1 ≤ B₀ := by dsimp only [B₀]; linarith only [hsum]
  have hAB (j : ℕ) (hj : j ≤ N) : A j ≤ B₀ := by
    have hs : A j ≤ ∑ k ∈ Finset.range (N + 1), A k :=
      Finset.single_le_sum (fun k _ => (hA k).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    dsimp only [B₀]
    linarith only [hs]
  obtain ⟨K₁, A₁, hK₁, hA₁, hsample⟩ :=
    retainedReference_positive_endpoint_host_sample_bound W.P W.metadata.selected
      W.metadata.first_two one_pos W.realizes W.hw W.coordinates
      W.through03.1.1.2.2.2.1 W.hT (zero_le_one.trans hB₀)
  let D : ℝ := B₀ * C0 ^ B₀ * K₁
  have hD : 0 < D := mul_pos
    (mul_pos (zero_lt_one.trans_le hB₀)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hC0) _)) hK₁
  obtain ⟨B₁, _, hpack⟩ := coefficientEnvelope_pack D A₁
  let B : ℝ := max 1 B₁
  have hB : 1 ≤ B := le_max_left _ _
  have hB₁B : B₁ ≤ B := le_max_right _ _
  have href : (W.C.referenceState, 0) ∈ stateNeighborhood W.S W.C W.base W.ε :=
    reference_mem_stateNeighborhood W.S W.C W.base W.ε_pos
  have hsref : stateSector W.S W.C.referenceState := W.through03.1.1.2.2.1.stateSector
  have hlow := n04PositiveGeometry_reference_grading_zero
    (pairGrading (stateGrading W.S) realGrading) (W.C.referenceState, 0) low
  have hw : ContDiff ℝ ∞ W.D.w := W.through03.1.1.1.1.choose_spec.1.2.2.1.1
  refine ⟨B, hB, ?_⟩
  intro i side m hm g hg hfactor R hR hstrip j hj
  let r := n01ComponentRoot W.C m (!side)
  let σ := n01ComponentRootOrientation (!side)
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let V : ℝ := C0 * W.T.E0 (W.T.sample (W.C.cell m))
  have hV : 1 ≤ V := hfloor _
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤ E := le_enlargedMaterialData_E0 W.T _
  have hend : n04PositiveEndpoint i side =
      (if side then W.C.left m else W.C.right m) := by
    simpa only [hm] using (X.src i side).property
  have hsampleBound := hsample i side m (W.C.cell m) (X.cell i)
    (W.host m) hend (X.cell_mem i)
  have hmaterial : B₀ * V ^ B₀ ≤ B * E ^ B := by
    calc
      _ = (B₀ * C0 ^ B₀) * W.T.E0 (W.T.sample (W.C.cell m)) ^ B₀ := by
        dsimp only [V]
        rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans (W.floor _))]
        ring
      _ ≤ (B₀ * C0 ^ B₀) * (K₁ * W.T.E0 (W.T.sample (X.cell i)) ^ A₁) :=
        mul_le_mul_of_nonneg_left hsampleBound
          (mul_nonneg (zero_le_one.trans hB₀) (Real.rpow_nonneg (zero_le_one.trans hC0) _))
      _ = D * W.T.E0 (W.T.sample (X.cell i)) ^ A₁ := by dsimp only [D]; ring
      _ ≤ D * E ^ A₁ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_le_one.trans (W.floor _)) hEU hA₁) hD.le
      _ ≤ B₁ * E ^ B₁ := hpack E hE
      _ ≤ B * E ^ B := mul_le_mul hB₁B
        (Real.rpow_le_rpow_of_exponent_le hE hB₁B)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hraw := hjets (W.C.referenceState, 0) href hsref hlow
    m (W.C.cell m) (W.host m) (X.optical m) (!side) g hg hfactor R hR hstrip 0 j
  have hraw' := n04PositiveGeometry_reference_grading_bound
    (pairGrading (stateGrading W.S) realGrading) (W.C.referenceState, 0)
    (j + outLoss) hraw
  have heq := n04PositiveGeometry_referenceRootSpeedFactor_eq_actual hw
    W.through03.1.1.2.2.1 g r σ
  have heq' : (fun p => factoredCharacteristicSpeed W.D.w g
      (stateProfile W.D W.S W.C W.C.referenceState)
      (stateHeight W.D W.S W.C (W.C.referenceState, 0)) r σ p ^ (1 : ℝ)) =
      (fun p => referenceRootSpeedFactor W.D.w g r σ p.1) := by
    funext p
    exact (Real.rpow_one _).trans (congrFun heq p)
  have hpolar : ‖iteratedFDeriv ℝ j
      (fun p : PolarPoint => referenceRootSpeedFactor W.D.w g r σ p.1) (0, 0)‖ ≤
      A j * V ^ (A j) :=
    (congrArg (fun f : PolarPoint → ℝ =>
      ‖iteratedFDeriv ℝ j f (0, 0)‖ ≤ A j * V ^ (A j)) heq').mp hraw'
  have hzero : ((0, 0) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩
  have hroot := hstrip (0, 0) hzero
  have hsmooth : ContDiffAt ℝ ∞ (referenceRootSpeedFactor W.D.w g r σ) 0 :=
    contDiffAt_referenceRootSpeedFactor hw hg hroot.1 hroot.2.1 hroot.2.2.1
  exact (n04PositiveGeometry_scalar_radial_norm_le hsmooth j).trans (hpolar.trans
    ((mul_le_mul (hAB j hj) (Real.rpow_le_rpow_of_exponent_le hV (hAB j hj))
      (Real.rpow_nonneg (zero_le_one.trans hV) _) (zero_le_one.trans hB₀)).trans hmaterial))

end ContinuousFlexibility.Analysis
