import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05ReferenceCoefficients
import ContinuousFlexibility.Analysis.N05ReferenceQuadraticTests

/-!
# The frozen negative canonical identity determines the reference symbol

The operator identity is read directly from N04, at the actual chart image.
The inverse-chart identity and the true coefficient germs give its conjugation
form.  The physical reference symbol is then identified on actual local tests.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n05_divergenceOperator_coeff_congr
    {L A : SymmetricCoefficients} {p : PolarPoint}
    (ha : L.a =ᶠ[𝓝 p] A.a) (hb : L.b =ᶠ[𝓝 p] A.b) (hc : L.c =ᶠ[𝓝 p] A.c)
    (f : PolarPoint → ℝ) :
    divergenceOperator L f p = divergenceOperator A f p := by
  have hN : (fun q => L.a q * radialPartial f q + L.b q * angularPartial f q) =ᶠ[𝓝 p]
      (fun q => A.a q * radialPartial f q + A.b q * angularPartial f q) := by
    filter_upwards [ha, hb] with q hqa hqb
    rw [hqa, hqb]
  have hT : (fun q => L.b q * radialPartial f q + L.c q * angularPartial f q) =ᶠ[𝓝 p]
      (fun q => A.b q * radialPartial f q + A.c q * angularPartial f q) := by
    filter_upwards [hb, hc] with q hqb hqc
    rw [hqb, hqc]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
      (hN.fderiv_eq (𝕜 := ℝ)))
    (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1))
      (hT.fderiv_eq (𝕜 := ℝ)))

/-- The true N04 operator formula, in physical coordinates on a negative piece. -/
theorem n05_negative_conjugation_from_N04
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {m : ℕ} (hm : K.positive m = false)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m)
    (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W) :
    K.height z m x / |planeJacobian (K.chart z m) x| *
        divergenceOperator (L.coefficients z)
          (fun y => K.height z m y * W (K.chart z m y)) x =
      divergenceOperator n05TricomiCoefficients W (K.chart z m x) +
        K.potential z m (K.chart z m x) * W (K.chart z m x) := by
  have hcharts := h04.1.charts
  have hop := h04.2.1.2.2.1
  have hcoeff := h04.2.1.2.2.2.1
  have hchart := hcharts z hz hs m
  have hy := hchart.1 hx
  have hinv := hchart.2.2.1 x hx
  have hnear : ∀ᶠ q in 𝓝 (K.chart z m x), q ∈ canonicalOpen S K m :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hy
  have ha : (K.coefficients z m).a =ᶠ[𝓝 (K.chart z m x)] n05TricomiCoefficients.a := by
    filter_upwards [hnear] with q hq
    exact (hcoeff z hz hs m hm q hq).1
  have hb : (K.coefficients z m).b =ᶠ[𝓝 (K.chart z m x)] n05TricomiCoefficients.b := by
    filter_upwards [hnear] with q hq
    exact (hcoeff z hz hs m hm q hq).2.1
  have hc : (K.coefficients z m).c =ᶠ[𝓝 (K.chart z m x)] n05TricomiCoefficients.c := by
    filter_upwards [hnear] with q hq
    exact (hcoeff z hz hs m hm q hq).2.2
  have heq := hop z hz hs m W hW (K.chart z m x) hy
  simp only [canonicalOperator, canonicalSource, hm, Bool.false_eq_true, ↓reduceIte,
    one_mul, hinv] at heq
  rw [n05_divergenceOperator_coeff_congr ha hb hc W] at heq
  convert heq using 1 <;> ring

/-- The determinant relation at non-reflection reference points follows from
the actual N04 identity and the reference coefficient rigidity theorem. -/
theorem n05_negative_reference_determinant_nonreflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false)
    {x : PolarPoint} (hx : x ∈ referencePhysicalPieceOpen S K m)
    (hθ : x.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    K.height (C.referenceState, 0) m x ^ 4 *
        (D.w x.1 * (deriv D.w x.1 / x.1)) =
      -(K.chart (C.referenceState, 0) m x).1 := by
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hnegative := h04.1.referenceNegative
  have hclosed := n05_reference_closed_properties h04
  have hxD : x ∈ annularOpen D := ⟨(hpieces m).2.2 hx.1, mem_univ _⟩
  have hd : deriv D.w x.1 ≠ 0 := (hnegative m hm x.1 hx.1).ne
  have h01 := h.1.1.1
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  obtain ⟨hΨ, hh, hJ, _⟩ :=
    hclosed hmem hsector m x ⟨hx.1.1.le, hx.1.2.le⟩
  obtain ⟨ha, hb, hc⟩ :=
    n05_reference_coefficients_contDiffAt hT hS h.1 hxD hd hθ
  have hdet := n05_negative_height_determinant ha hb hc hh hΨ hJ
    (n05_negative_conjugation_from_N04 h.2.2.2.2.1 hmem hsector hm
      (by simpa only [h04.1.referenceDomain m] using hx))
  have hcoeff := n05_reference_coefficients_nonreflection hT hS h.1 hxD hd hθ
  have hLa : (L.coefficients (C.referenceState, 0)).a x = D.w x.1 :=
    (h.1.2.1 (C.referenceState, 0) hmem hsector x).trans
      (n05_originalCoefficients_reference h01.1.1 h01.2.2.1 x).1
  simpa only [hLa, hcoeff.2.2.1, hcoeff.2.2.2, pow_two, mul_zero, sub_zero] using hdet

/-- All three reference principal entries are forced by the same genuine
quadratic tests. -/
theorem n05_negative_reference_symbol_nonreflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false)
    {x : PolarPoint} (hx : x ∈ referencePhysicalPieceOpen S K m)
    (hθ : x.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    let z := (C.referenceState, 0)
    let ξ := fun y => (K.chart z m y).1
    let φ := fun y => (K.chart z m y).2
    K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) ξ ξ x =
        |planeJacobian (K.chart z m) x| ∧
      K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) ξ φ x = 0 ∧
      K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) φ φ x =
        |planeJacobian (K.chart z m) x| * (-ξ x) := by
  dsimp only
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hnegative := h04.1.referenceNegative
  have hclosed := n05_reference_closed_properties h04
  have hxD : x ∈ annularOpen D := ⟨(hpieces m).2.2 hx.1, mem_univ _⟩
  have hd : deriv D.w x.1 ≠ 0 := (hnegative m hm x.1 hx.1).ne
  have h01 := h.1.1.1
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  obtain ⟨hΨ, hh, hJ, _⟩ :=
    hclosed hmem hsector m x ⟨hx.1.1.le, hx.1.2.le⟩
  obtain ⟨ha, hb, hc⟩ := n05_reference_coefficients_contDiffAt hT hS h.1 hxD hd hθ
  have hAa : ContDiffAt ℝ ∞ n05TricomiCoefficients.a (K.chart (C.referenceState, 0) m x) :=
    contDiffAt_const
  have hAb : ContDiffAt ℝ ∞ n05TricomiCoefficients.b (K.chart (C.referenceState, 0) m x) :=
    contDiffAt_const
  have hAc : ContDiffAt ℝ ∞ n05TricomiCoefficients.c (K.chart (C.referenceState, 0) m x) :=
    contDiffAt_fst.neg
  have hprincipal := n05_principal_coefficients_of_conjugation ha hb hc hAa hAb hAc hh hΨ hJ
    (n05_negative_conjugation_from_N04 h.2.2.2.2.1 hmem hsector hm
      (by simpa only [h04.1.referenceDomain m] using hx))
  have hcoeff := n05_reference_coefficients_nonreflection hT hS h.1 hxD hd hθ
  have hLa : (L.coefficients (C.referenceState, 0)).a x = D.w x.1 :=
    (h.1.2.1 (C.referenceState, 0) hmem hsector x).trans
      (n05_originalCoefficients_reference h01.1.1 h01.2.2.1 x).1
  simpa only [n05PrincipalPair, n05RadialReferenceCoefficients, n05TricomiCoefficients,
    hLa, hcoeff.2.2.1, hcoeff.2.2.2, zero_mul, mul_zero, add_zero, mul_one] using hprincipal

end ContinuousFlexibility.Statements
