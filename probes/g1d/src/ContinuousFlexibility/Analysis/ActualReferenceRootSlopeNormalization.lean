import ContinuousFlexibility.Analysis.ActualReferenceNegativeEndpointData

/-!
# Exact normalization of the actual reference slope at a root

The unit radial density gives the height--slope product on the open
negative component. Actual ordinary smoothness at its boundary passes
this identity to the root. The existing inward orientation then removes
the absolute value. No quantitative collar, auxiliary reference chart,
or lower bound for the desired inverse slope is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem radial_unit_density_height_slope
    {F : PolarPoint → PolarPoint} {H : PolarPoint → ℝ}
    {A : SymmetricCoefficients} {w : ℝ → ℝ} {a b r : ℝ}
    (hr : r ∈ Ioo a b) (hF : DifferentiableAt ℝ F (r, 0))
    (he : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F p = ((F (p.1, 0)).1, p.2))
    (ha : A.a (r, 0) = w r)
    (hu : (coordinatePrincipalDensity A F H).a (r, 0) = 1) :
    H (r, 0) ^ 2 * w r * |deriv (fun x : ℝ => (F (x, 0)).1) r| = 1 := by
  let f : ℝ → ℝ := fun x => (F (x, 0)).1
  let j : ℝ := deriv f r
  have hf : HasDerivAt f j r :=
    (hasDerivAt_radial_slice hF.fst).differentiableAt.hasDerivAt
  have h1 : HasFDerivAt (fun p : PolarPoint => f p.1)
      (j • ContinuousLinearMap.fst ℝ ℝ ℝ) ((r, 0) : PolarPoint) :=
    (hf.comp_hasFDerivAt (f := fun p : PolarPoint => p.1) ((r, 0) : PolarPoint)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := ((r, 0) : PolarPoint))) :)
  have h2 : HasFDerivAt (fun p : PolarPoint => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) ((r, 0) : PolarPoint) :=
    hasFDerivAt_snd (𝕜 := ℝ) (p := ((r, 0) : PolarPoint))
  have hd : HasFDerivAt (fun p : PolarPoint => (f p.1, p.2))
      ((j • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))
      ((r, 0) : PolarPoint) := h1.prodMk h2
  have hnear : F =ᶠ[𝓝 (r, 0)] (fun p : PolarPoint => (f p.1, p.2)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show (r, (0 : ℝ)) ∈ Ioo a b ×ˢ (univ : Set ℝ) from ⟨hr, mem_univ _⟩)]
      with p hp
    exact he p hp
  have hDF (v : PolarPoint) : fderiv ℝ F (r, 0) v = (j * v.1, v.2) := by
    rw [hnear.fderiv_eq (𝕜 := ℝ), hd.fderiv]
    simp only [Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hJ : planeJacobian F (r, 0) = j := by
    simp only [planeJacobian, hDF, mul_one, mul_zero, sub_zero]
  have hunit : H (r, 0) ^ 2 / |j| * (w r * j ^ 2) = 1 := by
    simpa only [coordinatePrincipalDensity, coefficientQuadratic, hDF, hJ, ha,
      mul_one, mul_zero, zero_pow two_ne_zero, add_zero] using hu
  have hj : |j| ≠ 0 := by
    intro hz
    rw [hz, div_zero, zero_mul] at hunit
    exact zero_ne_one hunit
  change H (r, 0) ^ 2 * w r * |j| = 1
  apply mul_right_cancel₀ hj
  calc
    _ = H (r, 0) ^ 2 * (w r * j ^ 2) := by rw [← sq_abs j]; ring
    _ = |j| := by
      have h := congrArg (fun x : ℝ => x * |j|) hunit
      field_simp [hj] at h
      nlinarith only [h]
    _ = 1 * |j| := (one_mul _).symm

/-- The inverse of the true inward reference slope is the actual height
squared times the original profile. Both endpoints share one proof. -/
theorem n04Coordinates_actual_reference_root_slope_normalization
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (m : ℕ) (side : Bool) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := e.symm (.inl (m, side))
    let c := if side then C.right m else C.left m
    let σ : ℝ := if side then -1 else 1
    let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
    let q := σ * deriv (fun r : ℝ => (K.chart z₀ k (r, 0)).1) c
    K.height z₀ k (c, 0) ^ 2 * D.w c * q = 1 ∧
      q⁻¹ = K.height z₀ k (c, 0) ^ 2 * D.w c := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let c := if side then C.right m else C.left m
  let σ : ℝ := if side then -1 else 1
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let F := K.chart z₀ k
  let H := K.height z₀ k
  let f : ℝ → ℝ := fun r => (F (r, 0)).1
  have hroot := n04Coordinates_actual_reference_negative_endpoint_data
    hT hS hN hfield e m side
  have hopen := n04Coordinates_actual_reference_negative_radial_fields
    hT hS hN hfield e m side
  have href : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S z₀.1 := n04b_referenceState_sector hN.1.1.2.2.1
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf : ContDiffAt ℝ ∞ f c := ((hroot.1 0).1.fst.comp c hline :)
  have hH : ContinuousAt (fun r : ℝ => H (r, 0)) c :=
    ((hroot.1 0).2.1.comp c hline).continuousAt
  have hj : ContinuousAt (deriv f) c :=
    (hf.derivWithin (m := 0) (by simp)).continuousAt
  have hw : ContinuousAt D.w c :=
    (n04b_profileGeometry_of_through03 hN).2.2.1.1.continuous.continuousAt
  have hcont : ContinuousAt (fun r : ℝ => H (r, 0) ^ 2 * D.w r * |deriv f r|) c :=
    ((hH.pow 2).mul hw).mul hj.abs
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hc : c ∈ closure (Ioo (C.left m) (C.right m)) := by
    rw [closure_Ioo hab.ne]
    cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have hnorm : H (c, 0) ^ 2 * D.w c * |deriv f c| = 1 := by
    apply hcont.continuousWithinAt.eq_const_of_mem_closure hc
    intro r hr
    have hp : (r, (0 : ℝ)) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨hr, mem_univ _⟩
    have hFr : DifferentiableAt ℝ F (r, 0) :=
      ((hopen.1 _ hp).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
        (by simp)
    exact radial_unit_density_height_slope hr hFr hopen.2.2.1
      ((hN.2.1 z₀ href hsref (r, 0)).trans (hN.1.1.reference_coefficients (r, 0)).1)
      (n04Coordinates_actualAtlas_negativePrincipalDensity hT hS hN hfield e href hsref
        k m side (e.apply_symm_apply _) hp).1
  have hq : 0 < σ * deriv f c := hroot.2
  have hσ : |σ| = 1 := by cases side <;> norm_num [σ]
  have hsigned : |deriv f c| = σ * deriv f c := by
    calc
      _ = |σ * deriv f c| := by rw [abs_mul, hσ, one_mul]
      _ = _ := abs_of_pos hq
  rw [hsigned] at hnorm
  exact ⟨hnorm, inv_eq_of_mul_eq_one_left hnorm⟩

end ContinuousFlexibility.Analysis
