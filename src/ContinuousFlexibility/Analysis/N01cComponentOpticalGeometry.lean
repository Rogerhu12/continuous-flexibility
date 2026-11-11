import ContinuousFlexibility.Analysis.N01cFiniteAffineInputs
import ContinuousFlexibility.Analysis.N01cOpticalSquareBounds
import ContinuousFlexibility.Analysis.N01cCommonType

/-!
# The actual component optical square through its two roots

The reference-relative formula is defined on the whole radial core. On
the negative component it equals the optical square of the actual state
profile. Its smooth endpoint quotient is positive on the entire closed
component on one common state neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

def componentOpticalSquare (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (m : ℕ) (z : AnnularState S × ℝ) (r : ℝ) : ℝ :=
  referenceOpticalSquare D r - stateKappa S z.1 m * controlOpticalFactor C m r

theorem componentOpticalSquare_eq_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hA : N01PartA D T S C)
    (m : ℕ) (z : AnnularState S × ℝ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    componentOpticalSquare D S C m z r =
      -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r) := by
  rw [n01_stateProfile_opticalSquare_eq hA z.1 m hr]
  simp only [componentOpticalSquare, referenceOpticalSquare, controlOpticalFactor,
    mul_div_assoc]

theorem controlOpticalFactor_contDiffOn_core
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    ContDiffOn ℝ ∞ (controlOpticalFactor C m) (Ioo D.a D.b) := by
  have hd : ContDiff ℝ ∞ (deriv (C.control m)) :=
    (contDiff_infty_iff_deriv.mp (hC.2.2.2.2.2.1 m).1).2
  exact hd.contDiffOn.div contDiff_id.contDiffOn (fun r hr => (hD.1.trans hr.1).ne')

theorem componentOpticalSquare_contDiffOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hA : N01PartA D T S C)
    (m : ℕ) (z : AnnularState S × ℝ) :
    ContDiffOn ℝ ∞ (componentOpticalSquare D S C m z) (Ioo D.a D.b) :=
  (show ContDiffOn ℝ ∞ (referenceOpticalSquare D) (Ioo D.a D.b) from
    fun r hr => (referenceOpticalSquare_contDiffAt hA.1.1.choose_spec.1 hr).contDiffWithinAt).sub
    (contDiffOn_const.mul (controlOpticalFactor_contDiffOn_core
      hA.1.1.choose_spec.1 hA.2.2.1 m))

/-- One boundary lemma handles the two endpoints of every component. -/
theorem componentOpticalSquare_boundary_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hA : N01PartA D T S C)
    (m : ℕ) (z : AnnularState S × ℝ) {r : ℝ}
    (hr : r = C.left m ∨ r = C.right m) : componentOpticalSquare D S C m z r = 0 := by
  have hC := hA.2.2.1
  have hw : deriv D.w r = 0 := by
    rcases hr with rfl | rfl
    · exact (hC.2.1 m).1
    · exact (hC.2.1 m).2.1
  have hnot : r ∉ Ioo (C.left m) (C.right m) := by
    rcases hr with rfl | rfl
    · exact fun h => lt_irrefl _ h.1
    · exact fun h => lt_irrefl _ h.2
  have hc : deriv (C.control m) r = 0 := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_zero_off_open_interval
      (hC.2.2.2.2.2.1 m).1 (hC.2.2.2.2.2.1 m).2.2 1 hnot
  simp only [componentOpticalSquare, referenceOpticalSquare, controlOpticalFactor,
    hw, hc, neg_zero, zero_div, mul_zero, sub_zero]

theorem contDiffOn_componentOpticalSquare_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (m : ℕ) {n : ℕ} (x : AnnularState S × ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (AnnularState S × ℝ)) :
    ContDiffOn ℝ ∞ (fun p : (Fin n → ℝ) × ℝ =>
      componentOpticalSquare D S C m (x + L p.1) p.2)
      ((univ : Set (Fin n → ℝ)) ×ˢ Ioo D.a D.b) := by
  let K : (AnnularState S × ℝ) →L[ℝ] ℝ :=
    (stateKappaCLM hS hT hA.1.1 m).comp
      (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ)
  have hk : ContDiffOn ℝ ∞
      (fun p : (Fin n → ℝ) × ℝ => stateKappa S (x + L p.1).1 m)
      ((univ : Set (Fin n → ℝ)) ×ˢ Ioo D.a D.b) :=
    contDiffOn_finiteAffine_linearField (fun z _ => stateKappa S z.1 m)
      (fun _ _ => K)
      (fun r hr z => by
        simp only [K, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
          stateKappaCLM_apply])
      (fun _ => contDiffOn_const) x L
  have href : ContDiffOn ℝ ∞ (referenceOpticalSquare D) (Ioo D.a D.b) :=
    fun r hr => (referenceOpticalSquare_contDiffAt hA.1.1.choose_spec.1 hr).contDiffWithinAt
  have hctrl := controlOpticalFactor_contDiffOn_core hA.1.1.choose_spec.1 hA.2.2.1 m
  exact (href.comp contDiff_snd.contDiffOn (fun p hp => hp.2)).sub
    (hk.mul (hctrl.comp contDiff_snd.contDiffOn (fun p hp => hp.2)))

/-- The same quotient is positive at both endpoints and everywhere
between them, uniformly over one neighbourhood of the actual states. -/
theorem n01_exists_componentOpticalQuotient_positive
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hG : N01PrimitiveGeometry D T S C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ base : ℕ, ∀ z ∈ stateNeighborhood S C base ε,
      ∀ m r, r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z) (C.left m) (C.right m) r := by
  obtain ⟨K, hK, hbound⟩ := hG.2.2
  obtain ⟨ε, hε, hopt⟩ := n01_exists_common_opticalBounds_of_referenceLower hS hT hA hG.2.2
  refine ⟨ε, hε, fun base z hz m r hr => ?_⟩
  have hC := hA.2.2.1
  have hlh := (hC.1 m).2.1
  have hclosed : Icc (C.left m) (C.right m) ⊆ Ioo D.a D.b :=
    fun y hy => ⟨(hC.1 m).1.trans_le hy.1, hy.2.trans_lt (hC.1 m).2.2⟩
  have hs := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  have hE : 0 < T.E0 (T.sample (C.cell m)) := (hT.2.1 _ hs).2.2.1
  let c : ℝ := (K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K)) / 2
  have hc : 0 < c := div_pos (mul_pos (inv_pos.mpr hK)
    (Real.rpow_pos_of_pos hE (-K))) (by norm_num)
  have hq (y : ℝ) (hy : y ∈ Ioo (C.left m) (C.right m)) :
      c * min (y - C.left m) (C.right m - y) ≤ componentOpticalSquare D S C m z y := by
    rw [componentOpticalSquare_eq_actual hA m z hy]
    calc
      _ = (K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (y - C.left m) (C.right m - y)) / 2 := by dsimp only [c]; ring
      _ ≤ (-deriv D.w y / (y * D.w y)) / 2 :=
        div_le_div_of_nonneg_right (hbound m y hy) (by norm_num)
      _ ≤ _ := (hopt base z hz m y hy).2.1
  exact (div_pos hc (sub_pos.mpr hlh)).trans_le
    (twoRootDivided_lower_on_Icc isOpen_Ioo (convex_Ioo D.a D.b)
      (componentOpticalSquare_contDiffOn hA m z) hlh hclosed
      (componentOpticalSquare_boundary_zero hA m z (Or.inl rfl))
      (componentOpticalSquare_boundary_zero hA m z (Or.inr rfl)) hc.le hq hr)

end ContinuousFlexibility.Statements
