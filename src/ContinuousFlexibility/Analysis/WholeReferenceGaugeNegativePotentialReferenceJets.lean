import ContinuousFlexibility.Analysis.ActualNegativeReferencePotentialMaterialJets
import ContinuousFlexibility.Analysis.ActualNegativeLengthMaterialBounds
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# The same whole atlas's negative reference potential atom

The negative fields and sample are copied literally from the original
typed atlas. The unit coordinate has the true optical radius as slope;
its positive powers are paid by the independently proved length bound.
Only the material envelope on the right hand side is enlarged here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff BigOperators

/-- Actual negative potential atoms on the same whole reference atlas.
The original optical host may differ from the stored half's sample cell.
The raw optical estimate remains explicit until the retained construction
supplies it; no potential or inverse-jet target is an input. -/
theorem n04WholeReferenceGauge_negative_potentialReferenceJets_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (hK₀ : 0 < K₀) :
    ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧
    ∀ (e : ℕ ≃ N04WholePieceIndex D)
      (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
      (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
      (τ σ : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (Q : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ),
      (∀ m, ∃ j, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        ∀ r ∈ Ioo (C.left m) (C.right m),
          K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
            min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) →
      let K := n04bActualTypedAtlas hT hS hN hfield e₀
      let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
      let U := enlargedMaterialData T
      ∀ m, V.positive m = false → ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b
          (atom D U S C L V (C.referenceState, 0) m .potential) p| ≤
            BM * U.E0 (U.sample (V.cell m)) ^ BM := by
  classical
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let U := enlargedMaterialData T
  obtain ⟨C0, hC0, hfloor, B, hB, hpotential⟩ :=
    n04bActualTypedAtlas_reference_half_potential_material_jets hT hS hN hfield e₀ hK₀
  obtain ⟨BN, AN, hBN, hAN, hlength⟩ :=
    n04bActualTypedAtlas_negative_length_material_bounds hT hS hN hfield e₀
  intro s
  let A : ℝ := 1 + BN + AN + ∑ n : Fin (s + 1), B n.val
  have hsum : 0 ≤ ∑ n : Fin (s + 1), B n.val :=
    Finset.sum_nonneg fun n _ => zero_le_one.trans (hB n.val)
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hBN, hAN, hsum]
  have hBNA : BN ≤ A := by dsimp only [A]; linarith only [hAN, hsum]
  have hANA : AN ≤ A := by dsimp only [A]; linarith only [hBN, hsum]
  have hBA (n : ℕ) (hn : n ≤ s) : B n ≤ A := by
    have hh : B n ≤ ∑ q : Fin (s + 1), B q.val :=
      Finset.single_le_sum (fun q _ => zero_le_one.trans (hB q.val))
        (Finset.mem_univ (⟨n, by omega⟩ : Fin (s + 1)))
    dsimp only [A]
    linarith only [hh, hBN, hAN]
  let coefficient : ℝ := A * C0 ^ A
  let exponent : ℝ := A * ((s + 1 : ℕ) : ℝ)
  have hc : 1 ≤ coefficient := one_le_mul_of_one_le_of_one_le hA
    (Real.one_le_rpow hC0 (zero_le_one.trans hA))
  have hAc : A ≤ coefficient := le_mul_of_one_le_right (zero_le_one.trans hA)
    (Real.one_le_rpow hC0 (zero_le_one.trans hA))
  obtain ⟨BM, hBM, hpack⟩ := coefficientEnvelope_pack (coefficient ^ (s + 1)) exponent
  refine ⟨BM, hBM, ?_⟩
  intro e cell ψ χ h₀ τ σ Q N hoptical
  dsimp only
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  intro m hm p hp a b hab
  cases hi : e m with
  | inr i =>
      have hpositive : V.positive m = true := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hpositive.symm.trans hm).symm)
  | inl j =>
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hk : e₀ k = .inl j := by
        rcases j with ⟨r, side⟩
        cases side <;> simp only [k, K, n04bActualTypedAtlas,
          n04bTypedAtlasData_cutPair, Bool.false_eq_true, ite_false, ite_true,
          Equiv.apply_symm_apply]
      rcases n04WholeReferenceGaugeAtlasData_negative_fields
        C L K e cell ψ χ h₀ τ σ Q N (C.referenceState, 0) m j hi with
        ⟨hl, hr, _, _, _, hsample, _, _, _, _, _, hpot⟩
      let ρ := n04bRootCutRadius (C.travel j.1)
      have hρ : 0 < ρ := n04bRootCutRadius_pos (n04b_referenceTravel_pos
        (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 j.1)
      have hlK : K.left k = 0 := by
        simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_left]
      have hrK : K.right k = ρ := by
        simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_right, hk, ρ]
      have hatom : atom D U S C L V (C.referenceState, 0) m .potential =
          fun q : PolarPoint => K.potential (C.referenceState, 0) k (0 + ρ * q.1, q.2) := by
        funext q
        change V.potential (C.referenceState, 0) m
          (V.left m + (V.right m - V.left m) * q.1, q.2) = _
        rw [hpot, hl, hr, hlK, hrK, sub_zero]
      have hy : (ρ * p.1, p.2) ∈ canonicalOpen S K k := by
        rw [canonicalOpen, hlK, hrK]
        exact ⟨⟨mul_pos hρ hp.1.1,
          (mul_lt_mul_of_pos_left hp.1.2 hρ).trans_eq (mul_one ρ)⟩, mem_univ _⟩
      obtain ⟨host, hhost, hraw⟩ := hoptical j.1
      have hjet := hpotential k j.1 j.2 hk host hhost hraw (ρ * p.1, p.2) hy a b
      let E : ℝ := T.E0 (T.sample (K.cell k))
      let t : ℝ := U.E0 (U.sample (K.cell k))
      let W : ℝ := C0 * E
      have hsCore := materialSample_mem_interval hN.1.1.1.1 hT (K.cell k)
      have hE : 0 < E := (hT.2.1 _ hsCore).2.2.1
      have ht : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hsCore
      have hEt : E ≤ t := le_enlargedMaterialData_E0 T (T.sample (K.cell k))
      have hW : 1 ≤ W := hfloor (K.cell k)
      have hWt : W ≤ C0 * t := mul_le_mul_of_nonneg_left hEt (zero_le_one.trans hC0)
      let M : ℝ := coefficient * t ^ A
      have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hc
        (Real.one_le_rpow ht (zero_le_one.trans hA))
      have hpotentialM : B (a + b) * W ^ (B (a + b)) ≤ M := by
        calc
          _ ≤ A * W ^ A := mul_le_mul (hBA _ hab)
            (Real.rpow_le_rpow_of_exponent_le hW (hBA _ hab))
            (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hA)
          _ ≤ A * (C0 * t) ^ A := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (zero_le_one.trans hW) hWt (zero_le_one.trans hA))
            (zero_le_one.trans hA)
          _ = M := by
            dsimp only [M, coefficient]
            rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
            ring
      have hρM : ρ ≤ M := by
        have hh := (hlength k j.1 j.2 hk).2.2.2
        rw [hlK, hrK, sub_zero] at hh
        calc
          _ ≤ BN * E ^ AN := hh
          _ ≤ BN * t ^ AN := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hE.le hEt hAN) hBN.le
          _ ≤ A * t ^ A := mul_le_mul hBNA
            (Real.rpow_le_rpow_of_exponent_le ht hANA)
            (Real.rpow_nonneg (zero_le_one.trans ht) _) (zero_le_one.trans hA)
          _ ≤ M := mul_le_mul_of_nonneg_right hAc
            (Real.rpow_nonneg (zero_le_one.trans ht) _)
      rw [hatom, n07a_mixedDerivative_radialAffine, zero_add, abs_mul, abs_pow,
        abs_of_pos hρ, hsample]
      calc
        _ ≤ ρ ^ a * M := mul_le_mul_of_nonneg_left (hjet.trans hpotentialM)
          (pow_nonneg hρ.le _)
        _ ≤ M ^ a * M := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hρ.le hρM a) (zero_le_one.trans hM)
        _ = M ^ (a + 1) := (pow_succ M a).symm
        _ ≤ M ^ (s + 1) := pow_le_pow_right₀ hM (by omega)
        _ = coefficient ^ (s + 1) * t ^ exponent := by
          dsimp only [M, exponent]
          rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans ht) A (s + 1)]
        _ ≤ BM * t ^ BM := hpack t ht

end ContinuousFlexibility.Analysis
