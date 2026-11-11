import ContinuousFlexibility.Radial.FixedCentralBorder
import ContinuousFlexibility.Radial.CentralBufferChoice
import ContinuousFlexibility.Radial.ModeCoreSource
import ContinuousFlexibility.Radial.InnerRadialActualPieces

/-!
# The fixed true column as an actual central model chart

The column is chosen before the reference geometry.  Its ordinary model
Liouville image is transported back by the inverse-adjoint map, and the
result is proved equal to the reference's genuine `matchingBorderVector`.
No replacement by the auxiliary R03 column occurs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

namespace FixedCentralBorder

theorem column_positive (B : FixedCentralBorder) :
    tsupport (fixedCentralColumn B.chi) ⊆ Ioi 0 := by
  intro r hr
  exact fixedCentralCap_order.1.trans (B.column_support hr).1

def modelColumn (B : FixedCentralBorder) : RadialL2 :=
  centralModelPhysicalColumn (by norm_num : (0 : ℝ) < 1)
    B.column_smooth B.column_compact B.column_positive

theorem modelColumn_ae (B : FixedCentralBorder) :
    (B.modelColumn : ℝ → ℝ) =ᵐ[volume]
      centralModelPhysicalColumnFunction 1 (fixedCentralColumn B.chi) :=
  centralModelPhysicalColumn_ae (by norm_num) B.column_smooth B.column_compact B.column_positive

def modelBuffer (B : FixedCentralBorder) (q : ℕ) (T B₀ : ℝ) : BufferData :=
  centralModelBuffer (2 * (q : ℝ)) T B₀ (centralModelBordered q) B.modelColumn
    (centralModelPhysicalColumnFunction 1 (fixedCentralColumn B.chi))

theorem column_support_in_model (B : FixedCentralBorder) {T : ℝ}
    (hT : sqrt centralOscillatorA + 2 ≤ T) :
    Function.support (fixedCentralColumn B.chi) ⊆
      Ioo (centralRadius (-T)) (centralRadius T) := by
  intro r hr
  have hs := B.column_support (subset_tsupport _ hr)
  have hl : -T < sqrt centralOscillatorA + 1 := by
    linarith only [sqrt_nonneg centralOscillatorA, hT]
  exact ⟨(strictMono_centralRadius hl).trans hs.1,
    hs.2.trans_le (strictMono_centralRadius.monotone hT)⟩

end FixedCentralBorder

theorem fixedCentralModel_chart_positive (T : ℝ) :
    ∀ x ∈ Icc (-T) T,
      0 < centralRadius x ∧ 0 < deriv centralRadius x ∧ 0 < centralDensityRoot x :=
  fun x _ => ⟨centralRadius_pos x, deriv_centralRadius_pos x, centralDensityRoot_pos x⟩

section Column

variable (B : FixedCentralBorder) {D : ReferenceData}
  (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
  {T : ℝ} (hT : 8 ≤ T) (hcap : sqrt centralOscillatorA + 2 ≤ T)
  (hcolumn : referenceColumn D = fixedCentralColumn B.chi)
  (hcore : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc (-T) T,
    D.w (centralRadius x) = 1 * centralDensityRoot x ^ 2 * deriv centralRadius x)

include hT hcap hcolumn

/-- The transported model column is the original radial border divided by
the original radial Hilbert density, on the whole reference measure. -/
theorem FixedCentralBorder.modelColumnLift_eq_matchingBorderVector :
    innerLiouvilleColumnLift D (by linarith : -T ≤ T) (by norm_num : (0 : ℝ) < 1)
      contDiff_centralRadius contDiff_centralDensityRoot
      (fixedCentralModel_chart_positive T) hcore hw B.modelColumn =
        matchingBorderVector D hD hborder := by
  let c := innerLiouvilleColumnLift D (by linarith : -T ≤ T)
    (by norm_num : (0 : ℝ) < 1) contDiff_centralRadius contDiff_centralDensityRoot
    (fixedCentralModel_chart_positive T) hcore hw B.modelColumn
  have hin : (c : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo (centralRadius (-T)) (centralRadius T))] matchingBorderTest D := by
    apply innerLiouvilleInterval_pushforward_ae D (by linarith : -T ≤ T)
      (by norm_num : (0 : ℝ) < 1) contDiff_centralRadius contDiff_centralDensityRoot
      (fixedCentralModel_chart_positive T) hcore hw
      ((Lp.memLp c).restrict _).aestronglyMeasurable
      ((matchingBorderTest_memLp hD hborder).restrict _).aestronglyMeasurable
    filter_upwards [innerLiouvilleColumnLift_pullback_ae D (by linarith : -T ≤ T)
      (by norm_num : (0 : ℝ) < 1) contDiff_centralRadius contDiff_centralDensityRoot
      (fixedCentralModel_chart_positive T) hcore hw B.modelColumn,
      ae_restrict_of_ae (s := Ioo (-T) T) B.modelColumn_ae,
      ae_restrict_mem measurableSet_Ioo] with x hx hg hxi
    change innerLiouvilleColumnLift D (by linarith : -T ≤ T)
      (by norm_num : (0 : ℝ) < 1) contDiff_centralRadius contDiff_centralDensityRoot
      (fixedCentralModel_chart_positive T) hcore hw B.modelColumn (centralRadius x) = _
    rw [hx, hg]
    change (deriv centralRadius x / (sqrt 1 * centralDensityRoot x) *
        fixedCentralColumn B.chi (centralRadius x)) /
        (12 * sqrt 1 * centralDensityRoot x *
          (deriv centralRadius x / centralRadius x) ^ 2) =
      referenceColumn D (centralRadius x) / (12 * D.w (centralRadius x) / centralRadius x ^ 2)
    rw [hcolumn, hw x (Ioo_subset_Icc_self hxi)]
    simp only [sqrt_one, one_mul]
    field_simp [(centralRadius_pos x).ne', (deriv_centralRadius_pos x).ne',
      (centralDensityRoot_pos x).ne']
    <;> ring
  have hout := innerLiouvilleColumnLift_support_ae D (by linarith : -T ≤ T)
    (by norm_num : (0 : ℝ) < 1) contDiff_centralRadius contDiff_centralDensityRoot
    (fixedCentralModel_chart_positive T) hcore hw B.modelColumn
  apply Lp.ext
  filter_upwards [ae_imp_of_ae_restrict hin, hout,
    matchingBorderVector_coe hD hborder] with r hi ho hb
  rw [hb]
  by_cases hr : r ∈ Ioo (centralRadius (-T)) (centralRadius T)
  · exact hi hr
  · have hz : fixedCentralColumn B.chi r = 0 := by
      by_contra hne
      exact hr (B.column_support_in_model hcap hne)
    rw [ho hr]
    change 0 = referenceColumn D r / matchingDensity D r
    rw [hcolumn, hz, zero_div]

end Column

/-- The compact fixed column has actual localized R09 models at one common
central cut, chosen before any later connected reference. -/
theorem FixedCentralBorder.exists_localized_model_buffers (B : FixedCentralBorder)
    (hR09 : R09Statement) (Tmin : ℝ) :
    ∃ C K B₀ T : ℝ, 0 < C ∧ 0 < K ∧ 0 < B₀ ∧ 8 ≤ T ∧ Tmin ≤ T ∧
      sqrt centralOscillatorA + 2 ≤ T ∧
      ∀ q : ℕ, 1 ≤ q → BufferHypotheses (B.modelBuffer q T B₀) ∧
        Nonempty (InnerBufferLocalizedData (B.modelBuffer q T B₀) C K) := by
  obtain ⟨C, ε, B₀, T, hC, _hε, hB₀, hT, hmin, hmodels⟩ :=
    exists_actualCentralModelBuffer_compression hR09 (by norm_num : (0 : ℝ) < 1)
      B.column_smooth B.column_compact B.column_positive
      (by rw [B.column_pairing]; norm_num)
      (max Tmin (sqrt centralOscillatorA + 2))
  obtain ⟨K, hK, hlocal⟩ := exists_innerBufferLocalizedData
  refine ⟨C, K, B₀, T, hC, hK, hB₀, hT, (le_max_left _ _).trans hmin,
    (le_max_right _ _).trans hmin, ?_⟩
  intro q hq
  obtain ⟨hB, _hsmall, hcompression⟩ := hmodels q hq
  exact ⟨hB, hlocal _ C hB hcompression⟩

section Chart

variable (B : FixedCentralBorder) (D : ReferenceData)
  (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
  {n : ℕ} (G : InnerRadialChainGeometry D n) (central : Fin (n + 1))
  (q : ℕ) {T B₀ C K : ℝ} (hT : 8 ≤ T)
  (hcap : sqrt centralOscillatorA + 2 ≤ T)
  (hcolumn : referenceColumn D = fixedCentralColumn B.chi)
  (hcore : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc (-T) T,
    D.w (centralRadius x) = 1 * centralDensityRoot x ^ 2 * deriv centralRadius x)
  (hleft : G.left central = centralRadius (-T))
  (hright : G.right central = centralRadius T)
  (hB : BufferHypotheses (B.modelBuffer q T B₀))
  (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)

/-- The genuine central piece for the original fixed reference border. -/
def fixedCentralPhysicalModelChart :
    InnerRadialModelChart D G (centralModelBordered q) (2 * (q : ℝ)) central
      (matchingBorderVector D hD hborder) central where
  buffer := B.modelBuffer q T B₀
  buffer_hypotheses := hB
  C := C
  K := K
  localized := M
  radius := centralRadius
  scale := centralDensityRoot
  height := 1
  height_pos := by norm_num
  radius_smooth := contDiff_centralRadius
  scale_smooth := contDiff_centralDensityRoot
  chart_pos := fixedCentralModel_chart_positive T
  in_core := hcore
  weight_identity := hw
  U := centralRadiusWeightConstant * (1 + T)
  U_nonneg := mul_nonneg centralRadiusWeightConstant_pos.le (by linarith)
  log_deriv_bound := by
    intro x hx
    change x ∈ Icc (-T) T at hx
    have hxabs : |x| ≤ T := abs_le.mpr hx
    have h := (centralRadiusLogDerivative_norm_le_linear x).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hxabs] : 1 + |x| ≤ 1 + T)
        centralRadiusWeightConstant_pos.le)
    simpa only [centralRadiusLogDerivative, Real.norm_eq_abs] using h
  potential_identity := by
    intro x _
    change centralPotential (2 * (q : ℝ)) x =
      liouvilleV0 centralDensityRoot x - (2 * (q : ℝ)) ^ 2 *
        liouvilleRho centralRadius centralDensityRoot x
    rw [centralDensityRoot_liouvilleV0, centralRadius_liouvilleRho]
    unfold centralPotential
    ring
  left_eq := hleft
  right_eq := hright
  bordered_eq := by
    simp only [FixedCentralBorder.modelBuffer, centralModelBuffer, if_pos rfl, ite_true]
  column_eq := fun _ => B.modelColumnLift_eq_matchingBorderVector
    hD hborder hT hcap hcolumn hcore hw

/-- This cost depends only on the already fixed model cut and R09 constants. -/
def fixedCentralModelDirichletCost (T B₀ C : ℝ) : ℝ :=
  (sqrt 2 * (sqrt 12 + 1) ^ 2 * (1 + 2 * C)) *
    (1 + B₀ + centralRadiusWeightConstant * (1 + T)) ^ 4

theorem fixedCentralPhysicalModelChart_dirichlet_bound (hq : 1 ≤ q) (hC : 0 ≤ C) :
    ‖(fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap hcolumn hcore hw
      hleft hright hB M).dirichlet‖ ≤ fixedCentralModelDirichletCost T B₀ C := by
  let A := fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap hcolumn hcore hw
    hleft hright hB M
  let coeff : ℝ := 1 + B₀ + centralRadiusWeightConstant * (1 + T)
  have hB₀ : 0 < B₀ := hB.2.2.1
  have hU : 0 ≤ centralRadiusWeightConstant * (1 + T) :=
    mul_nonneg centralRadiusWeightConstant_pos.le (by linarith)
  have hc : 1 ≤ coeff := by dsimp only [coeff]; linarith only [hB₀, hU]
  have hBc : B₀ ≤ coeff := by dsimp only [coeff]; linarith only [hU]
  have hUc : centralRadiusWeightConstant * (1 + T) ≤ coeff := by
    dsimp only [coeff]
    linarith only [hB₀]
  have hj : (2 : ℝ) ≤ 2 * (q : ℝ) := by
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith only [hq']
  have hm : 1 ≤ centralBufferMass (2 * (q : ℝ)) T :=
    (by norm_num : (1 : ℝ) ≤ 4).trans (centralBufferMass_ge_four hj hT)
  have hmass (i : Fin 2) : ((B.modelBuffer q T B₀).mass i)⁻¹ ≤ coeff := by
    change (centralBufferMass (2 * (q : ℝ)) T)⁻¹ ≤ coeff
    have hi : (centralBufferMass (2 * (q : ℝ)) T)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hm
    exact hi.trans hc
  exact innerLiouvilleHilbertDirichlet_coefficient_cost D A.buffer_hypotheses.1.le
    A.height_pos A.radius_smooth A.scale_smooth A.chart_pos A.in_core A.weight_identity
    A.U A.U_nonneg A.log_deriv_bound A.localized A.buffer_hypotheses hC hc hBc hmass hUc

end Chart

end ContinuousFlexibility.Radial
