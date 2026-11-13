import ContinuousFlexibility.Analysis.N04bActualAtlasInteriorCompletion
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
import ContinuousFlexibility.Analysis.ActualNegativeLengthMaterialBounds
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.LocalMixedProductBounds
import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# Four actual negative principal atoms

The original typed atlas has the proved Airy principal field on its actual
canonical open piece. Reindexing the same negative fields into the whole
reference atlas preserves that field. On the unit strip the four atoms
are therefore `1`, `1`, `0`, and minus the actual optical radius times the
unit radial coordinate. The radius cost is paid at the original half's
stored material sample. No full-half height estimate is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff

/-- This is the proved principal clause for the original actual atlas;
the preliminary completion changes only its divided-difference field. -/
theorem n04bActualTypedAtlas_negative_airy_coefficients
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k : ℕ) (j : ℕ × Bool) (hk : e k = .inl j)
    (p : PolarPoint) (hp : p ∈ canonicalOpen S
      (n04bActualTypedAtlas hT hS hN hfield e) k) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    (K.coefficients z k).a p = 1 ∧ (K.coefficients z k).b p = 0 ∧
      (K.coefficients z k).c p = -p.1 := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hnegative : K.positive k = false := by
    simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_positive,
      hk, n04TypedPiecePositive]
  have hB := n04bActualTypedAtlas_interiorCompletion_partB hT hS hN hfield e
  exact hB.2.2.2.1 z hz hs k hnegative p hp

private def negativeAiryAtom (ρ : ℝ) (v : Atom) (p : PolarPoint) : ℝ :=
  if v = .principalA ∨ v = .principalAInverse then 1
  else if v = .principalB then 0 else -(ρ * p.1)

private theorem negativeAiryAtom_smooth (ρ : ℝ) (v : Atom) :
    ContDiff ℝ ∞ (negativeAiryAtom ρ v) := by
  by_cases hA : v = .principalA ∨ v = .principalAInverse
  · simpa only [negativeAiryAtom, if_pos hA] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : PolarPoint => (1 : ℝ)))
  · by_cases hB : v = .principalB
    · simpa only [negativeAiryAtom, if_neg hA, if_pos hB] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : PolarPoint => (0 : ℝ)))
    · simpa only [negativeAiryAtom, if_neg hA, if_neg hB] using
        ((contDiff_const.mul contDiff_fst).neg :
          ContDiff ℝ ∞ (fun p : PolarPoint => -(ρ * p.1)))

private theorem negativeAiryAtom_mixed_bound (ρ M : ℝ) (hρ : 0 ≤ ρ)
    (hM : 1 ≤ M) (hρM : ρ ≤ M) (v : Atom) {p : PolarPoint}
    (hp : p ∈ unitStrip) (a b : ℕ) :
    |mixedDerivative a b (negativeAiryAtom ρ v) p| ≤ M := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hconstant (c : ℝ) (hc : |c| ≤ M) :
      |mixedDerivative a b (fun _ : PolarPoint => c) p| ≤ M := by
    rw [n08_mixedDerivative_radial (fun _ : ℝ => c)]
    by_cases hb : b = 0
    · rw [if_pos hb, iteratedDeriv_const]
      by_cases ha : a = 0
      · rw [if_pos ha]
        exact hc
      · rw [if_neg ha, abs_zero]
        exact hM0
    · rw [if_neg hb, abs_zero]
      exact hM0
  by_cases hA : v = .principalA ∨ v = .principalAInverse
  · simpa only [negativeAiryAtom, if_pos hA] using
      hconstant 1 (by simpa only [abs_one] using hM)
  · by_cases hB : v = .principalB
    · simpa only [negativeAiryAtom, if_neg hA, if_pos hB] using
        hconstant 0 (by simpa only [abs_zero] using hM0)
    · simp only [negativeAiryAtom, if_neg hA, if_neg hB]
      rw [n08_mixedDerivative_radial (fun r : ℝ => -(ρ * r))]
      by_cases hb : b = 0
      · rw [if_pos hb, iteratedDeriv_fun_neg, iteratedDeriv_const_mul_field]
        change |-(ρ * iteratedDeriv a id p.1)| ≤ M
        rw [abs_neg, abs_mul, abs_of_nonneg hρ, iteratedDeriv_id]
        by_cases ha : a = 0
        · rw [if_pos ha, abs_of_pos hp.1.1]
          exact (mul_le_mul_of_nonneg_left hp.1.2.le hρ).trans
            (by simpa only [mul_one] using hρM)
        · rw [if_neg ha]
          by_cases ha₁ : a = 1
          · simpa only [if_pos ha₁, abs_one, mul_one] using hρM
          · simpa only [if_neg ha₁, abs_zero, mul_zero] using hM0
      · rw [if_neg hb, abs_zero]
        exact hM0

/-- All spatial orders of the four actual negative principal atoms have
one uniform sample cost. The same formula even holds at every valid state;
in particular it supplies their actual reference jets on this same atlas. -/
theorem n04WholeReferenceGauge_negative_principalReferenceJets_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e₀ : ℕ ≃ N04PieceIndex D) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (e : ℕ ≃ N04WholePieceIndex D)
      (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
      (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
      (τ σ : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (Q : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ),
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let U := enlargedMaterialData T
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m, V.positive m = false → ∀ v : Atom,
      (v = .principalA ∨ v = .principalAInverse ∨ v = .principalB ∨ v = .principalC) →
      ContDiffOn ℝ ∞ (atom D U S C L V z m v) unitStrip ∧
      (∀ p ∈ unitStrip, atom D U S C L V z m v (p + (0, Real.pi)) =
        atom D U S C L V z m v p) ∧
      ∀ p ∈ unitStrip, ∀ a b : ℕ,
        |mixedDerivative a b (atom D U S C L V z m v) p| ≤
          B * U.E0 (U.sample (V.cell m)) ^ B := by
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let U := enlargedMaterialData T
  obtain ⟨BN, AN, hBN, hAN, hlength⟩ :=
    n04bActualTypedAtlas_negative_length_material_bounds hT hS hN hfield e₀
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (1 + BN) AN
  refine ⟨B, hB, ?_⟩
  intro e cell ψ χ h₀ τ σ Q N
  dsimp only
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  intro z hz hs m hm v hv
  cases hi : e m with
  | inr i =>
      have hpositive : V.positive m = true := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.true_ne_false (hpositive.symm.trans hm))
  | inl j =>
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hk : e₀ k = .inl j := by
        rcases j with ⟨r, side⟩
        cases side <;> simp only [k, K, n04bActualTypedAtlas,
          n04bTypedAtlasData_cutPair, Bool.false_eq_true, ite_false, ite_true,
          Equiv.apply_symm_apply]
      rcases n04WholeReferenceGaugeAtlasData_negative_fields
        C L K e cell ψ χ h₀ τ σ Q N z m j hi with
        ⟨hl, hr, _, _, _, hsample, _, _, _, _, hcoeff, _⟩
      let ρ := n04bRootCutRadius (C.travel j.1)
      have hρ : 0 < ρ := n04bRootCutRadius_pos (n04b_referenceTravel_pos
        (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 j.1)
      have hlK : K.left k = 0 := by
        simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_left]
      have hrK : K.right k = ρ := by
        simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_right, hk, ρ]
      have hlV : V.left m = 0 := hl.trans hlK
      have hrV : V.right m = ρ := hr.trans hrK
      have hprincipal (p : PolarPoint) (hp : p ∈ canonicalOpen S V m) :
          (V.coefficients z m).a p = 1 ∧ (V.coefficients z m).b p = 0 ∧
            (V.coefficients z m).c p = -p.1 := by
        have hpK : p ∈ canonicalOpen S K k := by
          simpa only [canonicalOpen, hl, hr] using hp
        rw [hcoeff]
        exact n04bActualTypedAtlas_negative_airy_coefficients
          hT hS hN hfield e₀ hz hs k j hk p hpK
      have hEq : EqOn (atom D U S C L V z m v) (negativeAiryAtom ρ v) unitStrip := by
        intro p hp
        have hy : canonicalUnitPoint V m p ∈ canonicalOpen S V m := by
          constructor
          · change V.left m < V.left m + (V.right m - V.left m) * p.1 ∧
              V.left m + (V.right m - V.left m) * p.1 < V.right m
            simp only [hlV, hrV, sub_zero, zero_add]
            exact ⟨mul_pos hρ hp.1.1,
              (mul_lt_mul_of_pos_left hp.1.2 hρ).trans_eq (mul_one ρ)⟩
          · exact mem_univ _
        have hc := hprincipal (canonicalUnitPoint V m p) hy
        have hy₁ : (canonicalUnitPoint V m p).1 = ρ * p.1 := by
          simp only [canonicalUnitPoint, hlV, hrV, sub_zero, zero_add]
        rcases hv with rfl | rfl | rfl | rfl
        · change (V.coefficients z m).a (canonicalUnitPoint V m p) = _
          simpa [negativeAiryAtom] using hc.1
        · change ((V.coefficients z m).a (canonicalUnitPoint V m p))⁻¹ = _
          rw [hc.1]
          simp [negativeAiryAtom]
        · change (V.coefficients z m).b (canonicalUnitPoint V m p) = _
          simpa [negativeAiryAtom] using hc.2.1
        · change (V.coefficients z m).c (canonicalUnitPoint V m p) = _
          rw [hc.2.2, hy₁]
          simp [negativeAiryAtom]
      have hsCore := materialSample_mem_interval hN.1.1.1.1 hT (K.cell k)
      have hE : 0 < T.E0 (T.sample (K.cell k)) := (hT.2.1 _ hsCore).2.2.1
      let t := U.E0 (U.sample (K.cell k))
      have ht : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hsCore
      have htp : 1 ≤ t ^ AN := Real.one_le_rpow ht hAN
      have hmajor : 1 ≤ (1 + BN) * t ^ AN :=
        htp.trans (by nlinarith only [mul_nonneg hBN.le (zero_le_one.trans htp)])
      have hone : 1 ≤ B * t ^ B := hmajor.trans (hpack t ht)
      have hρbound : ρ ≤ B * t ^ B := by
        have h := (hlength k j.1 j.2 hk).2.2.2
        rw [hlK, hrK, sub_zero] at h
        calc
          ρ ≤ BN * T.E0 (T.sample (K.cell k)) ^ AN := h
          _ ≤ BN * t ^ AN := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hE.le
              (le_enlargedMaterialData_E0 T (T.sample (K.cell k))) hAN) hBN.le
          _ ≤ (1 + BN) * t ^ AN := by nlinarith only [htp]
          _ ≤ B * t ^ B := hpack t ht
      refine ⟨(negativeAiryAtom_smooth ρ v).contDiffOn.congr
        (fun p hp => hEq hp), ?_, ?_⟩
      · intro p hp
        have hp' : p + (0, Real.pi) ∈ unitStrip := by
          refine ⟨?_, mem_univ _⟩
          change 0 < p.1 + 0 ∧ p.1 + 0 < 1
          simpa only [add_zero] using hp.1
        calc
          _ = negativeAiryAtom ρ v (p + (0, Real.pi)) := hEq hp'
          _ = negativeAiryAtom ρ v p := by
            simp only [negativeAiryAtom, Prod.add_def, add_zero]
          _ = _ := (hEq hp).symm
      · intro p hp a b
        rw [mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) hEq a b hp,
          hsample]
        exact negativeAiryAtom_mixed_bound ρ (B * t ^ B) hρ.le hone hρbound v hp a b

end ContinuousFlexibility.Analysis
