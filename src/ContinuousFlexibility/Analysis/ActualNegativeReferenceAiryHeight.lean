import ContinuousFlexibility.Analysis.ActualNegativeReferenceAiryCoordinate
import ContinuousFlexibility.Analysis.PositiveReferenceCylinder

/-!
# The same stored reference height on a complete optical half

The genuine integral coordinate determines its signed radial derivative.
The actual unit radial density and positive stored height then determine
the original height itself. Thus the Airy integral formula is a local
representative of the stored field throughout the half, rather than a
new atlas normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem positive_height_of_radial_unit_density
    {H w j : ℝ} (hH : 0 < H) (hw : 0 < w)
    (hu : H ^ 2 / |j| * (w * j ^ 2) = 1) :
    H = (w * |j|) ^ (-1 / 2 : ℝ) := by
  have hj : |j| ≠ 0 := by
    intro he
    rw [he, div_zero, zero_mul] at hu
    exact zero_ne_one hu
  have hjpos : 0 < |j| := by
    by_contra hn
    exact hj (le_antisymm (le_of_not_gt hn) (abs_nonneg _))
  have hnorm : H ^ 2 * w * |j| = 1 := by
    apply mul_right_cancel₀ hj
    calc
      _ = H ^ 2 * (w * j ^ 2) := by rw [← sq_abs j]; ring
      _ = |j| := by
        have he := congrArg (fun t : ℝ => t * |j|) hu
        field_simp [hj] at he
        nlinarith only [he]
      _ = 1 * |j| := (one_mul _).symm
  have hpositive : 0 < w * |j| := mul_pos hw hjpos
  have hsquare : (H * Real.sqrt (w * |j|)) ^ 2 = (1 : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpositive.le]
    nlinarith only [hnorm]
  have hone : H * Real.sqrt (w * |j|) = 1 :=
    (sq_eq_sq₀ (mul_nonneg hH.le (Real.sqrt_nonneg _)) zero_le_one).mp hsquare
  have hdiv : H = 1 / Real.sqrt (w * |j|) :=
    (eq_div_iff (Real.sqrt_pos.mpr hpositive).ne').mpr hone
  calc
    H = 1 / Real.sqrt (w * |j|) := hdiv
    _ = (w * |j|) ^ (-1 / 2 : ℝ) := by
      rw [one_div, Real.sqrt_eq_rpow,
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hpositive.le]

/-- The height formula uses the same original typed atlas and the same
speed representative as its actual integral chart. -/
theorem n04Coordinates_actual_reference_negative_airy_height
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (m : ℕ) (side : Bool) {g c : ℝ → ℝ} {d : ℝ}
    (hd : d ≤ C.right m - C.left m)
    (hfactor : ∀ t ∈ Icc (0 : ℝ) d,
      n01aOpticalRadicand D.w
        (inwardComponentPoint (C.left m) (C.right m) side t) = t * g t)
    (hc : ContDiff ℝ ∞ c) (hcpos : ∀ t, 0 < c t)
    (hApos : ∀ t, 0 < n06AiryAverage c t)
    (hceq : ∀ t ∈ Icc (0 : ℝ) d, c t = Real.sqrt (g t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) d) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    K.height (C.referenceState, 0) (e.symm (.inl (m, side)))
        (inwardComponentPoint (C.left m) (C.right m) side x, θ) =
      n06AiryRadialHeight c
        (fun t => D.w (inwardComponentPoint (C.left m) (C.right m) side t)) x := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let p : PolarPoint := (inwardComponentPoint (C.left m) (C.right m) side x, θ)
  let X : ℝ → ℝ := fun r => if side then C.right m - r else r - C.left m
  let Y : ℝ → ℝ := fun r => n06AiryRadialCoordinate c (X r)
  let j : ℝ := n06AiryRadialSlope c x * (if side then (-1 : ℝ) else 1)
  have hXinward (r : ℝ) :
      inwardComponentPoint (C.left m) (C.right m) side (X r) = r := by
    cases side <;> simp only [X, inwardComponentPoint, Bool.false_eq_true, ↓reduceIte] <;> ring
  have hXp : X p.1 = x := by
    cases side <;> simp only [X, p, inwardComponentPoint, Bool.false_eq_true, ↓reduceIte] <;> ring
  have hXcontinuous : Continuous X := by
    cases side
    · exact continuous_id.sub continuous_const
    · exact continuous_const.sub continuous_id
  have hXderiv : HasDerivAt X (if side then (-1 : ℝ) else 1) p.1 := by
    cases side
    · exact (hasDerivAt_id p.1).sub_const (C.left m)
    · exact (hasDerivAt_id p.1).const_sub (C.right m)
  have hYderiv : HasDerivAt Y j p.1 := by
    have h := (n06_hasDerivAt_airyRadialCoordinate hc (X p.1) (hApos _)).comp p.1 hXderiv
    rw [hXp] at h
    exact h
  have hFg : K.chart z₀ k =ᶠ[𝓝 p] positiveReferenceCylinderChart Y := by
    have hpX : X p.1 ∈ Ioo (0 : ℝ) d := by simpa only [hXp] using hx
    filter_upwards [(hXcontinuous.comp continuous_fst).continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds hpX)] with q hq
    have he : K.chart z₀ k
        (inwardComponentPoint (C.left m) (C.right m) side (X q.1), q.2) =
        (n06AiryRadialCoordinate c (X q.1), q.2) :=
      n04Coordinates_actual_reference_negative_airy_chart
        hT hS hN hfield e m side hd hfactor hceq hq (hApos _).le q.2
    rw [hXinward q.1] at he
    exact he
  have hfirst : HasFDerivAt (fun q : PolarPoint => Y q.1)
      (j • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    have hecomp : Y ∘ (fun q : PolarPoint => q.1) = (fun q : PolarPoint => Y q.1) := by
      funext q
      exact Function.comp_apply
    rw [← hecomp]
    exact HasDerivAt.comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ)
      (h₂ := Y) (h₂' := j) (f := fun q : PolarPoint => q.1)
      (f' := ContinuousLinearMap.fst ℝ ℝ ℝ) p hYderiv
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hdF : HasFDerivAt (positiveReferenceCylinderChart Y)
      ((j • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hfirst.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hDF (v : PolarPoint) : fderiv ℝ (K.chart z₀ k) p v = (j * v.1, v.2) := by
    rw [hFg.fderiv_eq (𝕜 := ℝ), hdF.fderiv]
    simp only [positiveReferenceCylinderChart, Function.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hJ : planeJacobian (K.chart z₀ k) p = j := by
    simp only [planeJacobian, hDF, mul_one, mul_zero, sub_zero]
  have hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    refine ⟨?_, mem_univ _⟩
    have hxL := hx.2.trans_le hd
    cases side <;> simp only [p, inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
      <;> constructor <;> linarith only [hx.1, hxL]
  have hD : RadialProfileGeometry D := n04b_profileGeometry_of_through03 hN
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hw : 0 < D.w p.1 := hD.2.2.2.2.1 p.1
    ⟨(hC.1 m).1.trans hp.1.1, hp.1.2.trans (hC.1 m).2.2⟩
  have href : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have ha : (L.coefficients z₀).a p = D.w p.1 :=
    (hN.2.1 z₀ href hsref p).trans (hN.1.1.reference_coefficients p).1
  have hunit : K.height z₀ k p ^ 2 / |j| * (D.w p.1 * j ^ 2) = 1 := by
    have h : (coordinatePrincipalDensity (L.coefficients z₀) (K.chart z₀ k)
        (K.height z₀ k)).a p = 1 :=
      (n04Coordinates_actualAtlas_negativePrincipalDensity
        hT hS hN hfield e href hsref k m side (e.apply_symm_apply _) hp).1
    simpa only [coordinatePrincipalDensity, coefficientQuadratic, hDF, hJ, ha,
      mul_one, mul_zero, zero_pow two_ne_zero, add_zero] using h
  have hHpos : 0 < K.height z₀ k p :=
    (n04Coordinates_actual_reference_negative_radial_fields hT hS hN hfield e m side).2.2.2.2 p hp
  have hslope : 0 < n06AiryRadialSlope c x :=
    mul_pos (hcpos x) (Real.rpow_pos_of_pos (hApos x) _)
  have hj : |j| = n06AiryRadialSlope c x := by
    show |n06AiryRadialSlope c x * (if side then (-1 : ℝ) else 1)| = _
    rw [abs_mul, abs_of_pos hslope]
    cases side <;> norm_num
  have he := positive_height_of_radial_unit_density hHpos hw hunit
  rw [hj] at he
  exact he

end ContinuousFlexibility.Analysis
