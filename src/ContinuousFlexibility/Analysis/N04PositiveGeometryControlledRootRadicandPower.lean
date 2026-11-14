module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootSpeedFactor

/-!
# Fixed radicand powers at the positive midpoint sample

At the reference state the actual coefficient factor equals the fixed
root radicand on its genuine strip. The existing material theorem for
all real powers therefore controls every finite radial prefix of the
fixed factor needed by the true root height formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n04PositiveGeometry_referenceRootFactor_eqOn
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hw : ContDiff ℝ ∞ D.w) (href : referenceStateConditions D S C)
    {g : ℝ → ℝ} {r σ R : ℝ}
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C C.referenceState) (stateHeight D S C (C.referenceState, 0)) r σ R) :
    EqOn (rootCoefficientRadialFactor D.w g (stateProfile D S C C.referenceState)
      (stateHeight D S C (C.referenceState, 0)) r σ)
      (fun p => rootProfileRadicand D.w g r σ p.1)
      (Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ)) := by
  have hprimitive (x : ℝ) :
      HasDerivAt (fun y => ∫ t in D.b..y, D.w t) (D.w x) x :=
    (hw.continuous.integral_hasStrictDerivAt D.b x).hasDerivAt
  intro p hp
  have hdata := hstrip p hp
  rw [rootCoefficientRadialFactor_eq hdata.1 hdata.2.1 hdata.2.2.1
    hdata.2.2.2.1 hdata.2.2.2.2.1.ne',
    n05_stateProfile_reference href, n05_stateHeight_reference href,
    polarDiscriminant_radialHeightField hprimitive, one_pow, div_one]

/-- Every fixed real power and finite radial prefix has one sample
envelope before all components, actual divisions and reference strips. -/
theorem n04PositiveGeometry_referenceRootRadicandPower_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W) (γ : ℝ) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
    ∀ i side m, (X.src i side).val = some m →
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
      (∀ t, -deriv W.D.w (n01ComponentRoot W.C m (!side) +
        n01ComponentRootOrientation (!side) * t) = t * g t) →
    ∀ R : ℝ, 0 < R →
      RootCoefficientStripConditions W.D.w g
        (stateProfile W.D W.S W.C W.C.referenceState)
        (stateHeight W.D W.S W.C (W.C.referenceState, 0))
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) R →
    ∀ j : ℕ, j ≤ N →
      |iteratedDeriv j (fun t => rootProfileRadicand W.D.w g
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) t ^ γ) 0| ≤
        B * W.U.E0 (W.U.sample (X.cell i)) ^ B := by
  obtain ⟨C0, low, outLoss, hC0, hfloor, hpowers⟩ :=
    n01_rootFactor_axis_rpow_material_jets_of_component_optical
      W.hS W.hT W.through03.1.1 X.κ_pos
  obtain ⟨A, hA, hjets⟩ := hpowers γ
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
    reference_mem_stateNeighborhood W.S W.C W.base W.through03.1.1.2.1
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
    (pairGrading (stateGrading W.S) realGrading) (W.C.referenceState, 0) (j + outLoss) hraw
  have hzero : ((0, 0) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩
  have heq := n04PositiveGeometry_referenceRootFactor_eqOn hw W.through03.1.1.2.2.1 hstrip
  have hgerm : (fun p => rootCoefficientRadialFactor W.D.w g
      (stateProfile W.D W.S W.C W.C.referenceState)
      (stateHeight W.D W.S W.C (W.C.referenceState, 0)) r σ p ^ γ) =ᶠ[𝓝 (0, 0)]
      (fun p : PolarPoint => rootProfileRadicand W.D.w g r σ p.1 ^ γ) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hzero] with p hp
    exact congrArg (fun a : ℝ => a ^ γ) (heq hp)
  have hpolar : ‖iteratedFDeriv ℝ j
      (fun p : PolarPoint => rootProfileRadicand W.D.w g r σ p.1 ^ γ) (0, 0)‖ ≤
      A j * V ^ (A j) :=
    (congrArg norm (hgerm.iteratedFDeriv ℝ j).self_of_nhds).symm.trans_le hraw'
  have hroot := hstrip (0, 0) hzero
  have hsmooth : ContDiffAt ℝ ∞ (fun t => rootProfileRadicand W.D.w g r σ t ^ γ) 0 :=
    (contDiffAt_rootProfileRadicand hw hg hroot.1.ne').rpow_const_of_ne
      (rootProfileRadicand_pos hroot.1 hroot.2.1 hroot.2.2.1).ne'
  exact (n04PositiveGeometry_scalar_radial_norm_le hsmooth j).trans (hpolar.trans
    ((mul_le_mul (hAB j hj) (Real.rpow_le_rpow_of_exponent_le hV (hAB j hj))
      (Real.rpow_nonneg (zero_le_one.trans hV) _) (zero_le_one.trans hB₀)).trans hmaterial))

end ContinuousFlexibility.Analysis
