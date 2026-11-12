import ContinuousFlexibility.Analysis.CanonicalNegativeMaterialTransport
import ContinuousFlexibility.Analysis.CanonicalPositiveMaterialTransport
import ContinuousFlexibility.Analysis.WholeReferenceGaugeGlobalTransport

/-!
# Material transport for the same global reference-gauged atlas

The closed-negative and open-positive estimates apply to the actual
fields retained by the radius selector. The remaining branch is exactly
the identity. One common constant and exponent precede every state and
component. A fixed scaling of E0, rather than E0 >= 1, combines the powers.

The reference gauge changes neither selected field. The result therefore
includes the qualitative transport for that very atlas and both global
material ratios. The fixed positive parameters and matching certificate
come from the existing actual family; no collar or transport is reselected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeReferenceGauge_global_material_transport
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (buffer : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (hcontrols : N04FixedPositiveFamilyControls buffer 3 κ M H Clog Mσ δ)
    (hcaps : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      (n04PositiveLeft i ≠ D.a → buffer.centerLeft i - n04PositiveLeft i ≤
        Statements.endpointDistance D (n04PositiveLeft i) / 2) ∧
      (n04PositiveRight i ≠ D.b → n04PositiveRight i - buffer.centerRight i ≤
        Statements.endpointDistance D (n04PositiveRight i) / 2))
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (hχψ : ∀ i, Function.LeftInverse (χ i) (ψ i))
    (hh₀ : ∀ i p, h₀ i p ≠ 0) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let τ := n04FixedPositiveTransport K j buffer 3 κ M Mσ
    let σ := n04FixedPositiveInverse K j buffer 3 κ M Mσ
    let Q := n04FixedPositiveHeight K j 3 δ
    (∀ i, τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      (∀ i, WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (j i side) K z)
        (fun side => n04PositiveSourceHeight (j i side) K z)
        (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (buffer.centerLeft i) (buffer.centerRight i)
        (endpointFiberLower 3 (n04PositiveLeft i) (n04PositiveRight i)
          (buffer.centerLeft i) (buffer.centerRight i) (κ i) (Mσ i) * (κ i / 2))
        (Real.exp 2 * H i ^ 2)) →
      let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q buffer.region
      let F := n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id
      let q := n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
        (fun _ => (1 : ℝ))
      WholeCanonicalTransportQualitative (D := D) C V z F q ∧
        ∀ p ∈ annularOpen D,
          T.H (F p).1 / T.H p.1 ≤ B * T.E0 p.1 ^ A ∧
            T.M (F p).1 / T.M p.1 ≤ B * T.E0 p.1 ^ A := by
  classical
  dsimp only
  intro href
  obtain ⟨BN, AN, hBN, hAN, hnegative⟩ :=
    canonicalWholeNegativeTransport_material_ratios hT hS hN hfield e₀
  obtain ⟨BP, AP, hBP, hAP, hpositive⟩ :=
    canonicalWholePositiveTransport_material_ratios hT hS hN hfield e₀
  obtain ⟨E, hE, hscale⟩ := material_E0_uniform_scaled_lower hT hN.1.1.1.1
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  let A : ℝ := AN + AP
  let C₀ : ℝ := BN + BP + 1
  let B : ℝ := C₀ * E ^ A
  have hA : 0 ≤ A := add_nonneg hAN hAP
  have hC₀ : 1 ≤ C₀ := by dsimp only [C₀]; linarith
  have hB : 0 < B :=
    mul_pos (zero_lt_one.trans_le hC₀) (Real.rpow_pos_of_pos hEpos _)
  refine ⟨B, A, hB, hA, ?_⟩
  intro z hz hs hm
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let τ := n04FixedPositiveTransport K j buffer 3 κ M Mσ
  let σ := n04FixedPositiveInverse K j buffer 3 κ M Mσ
  let Q := n04FixedPositiveHeight K j 3 δ
  let F := n04WholeComponentField C (canonicalWholeNegativeTransport C K z) (τ z) id
  let q := n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) (Q z)
    (fun _ => (1 : ℝ))
  have hqual : WholeCanonicalTransportQualitative (D := D) C
      (n04WholeCanonicalAtlasData C L K e cell σ τ Q buffer.region) z F q :=
    n04WholeCanonical_global_relative_transport_qualitative
      hT hS hN hfield e₀ e cell σ τ Q buffer.region j
      buffer.centerLeft buffer.centerRight
      (fun i => endpointFiberLower 3 (n04PositiveLeft i) (n04PositiveRight i)
        (buffer.centerLeft i) (buffer.centerRight i) (κ i) (Mσ i) * (κ i / 2))
      (fun i => Real.exp 2 * H i ^ 2) hz hs hm
      (fun i => ⟨(href i).2.1, (href i).2.2⟩)
  change WholeCanonicalTransportQualitative (D := D) C
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q buffer.region) z F q ∧
    ∀ p ∈ annularOpen D,
      T.H (F p).1 / T.H p.1 ≤ B * T.E0 p.1 ^ A ∧
        T.M (F p).1 / T.M p.1 ≤ B * T.E0 p.1 ^ A
  refine ⟨n04WholeReferenceGaugeAtlasData_global_transport
    C L K e cell ψ χ h₀ τ σ Q buffer.region z F q href hχψ
    (fun i => (hm i).geometry.left_inverse) hh₀ hqual, ?_⟩
  intro p hp
  change T.H (F p).1 / T.H p.1 ≤ B * T.E0 p.1 ^ A ∧
    T.M (F p).1 / T.M p.1 ≤ B * T.E0 p.1 ^ A
  have hpos := hT.2.1 p.1 hp.1
  have hEp : 0 < T.E0 p.1 := hpos.2.2.1
  have hpower {a : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) :
      T.E0 p.1 ^ a ≤ E ^ A * T.E0 p.1 ^ A := by
    have hle : T.E0 p.1 ≤ E * T.E0 p.1 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hE hEp.le
    calc
      _ ≤ (E * T.E0 p.1) ^ a := Real.rpow_le_rpow hEp.le hle ha
      _ ≤ (E * T.E0 p.1) ^ A :=
        Real.rpow_le_rpow_of_exponent_le (hscale p.1 hp.1) haA
      _ = E ^ A * T.E0 p.1 ^ A := Real.mul_rpow hEpos.le hEp.le
  have hdom {b a : ℝ} (hb : 0 ≤ b) (hbC : b ≤ C₀)
      (ha : 0 ≤ a) (haA : a ≤ A) :
      b * T.E0 p.1 ^ a ≤ B * T.E0 p.1 ^ A := by
    calc
      _ ≤ b * (E ^ A * T.E0 p.1 ^ A) :=
        mul_le_mul_of_nonneg_left (hpower ha haA) hb
      _ ≤ C₀ * (E ^ A * T.E0 p.1 ^ A) :=
        mul_le_mul_of_nonneg_right hbC
          (mul_nonneg (Real.rpow_nonneg hEpos.le _) (Real.rpow_nonneg hEp.le _))
      _ = B * T.E0 p.1 ^ A := by dsimp only [B]; ring
  have hNdom : BN * T.E0 p.1 ^ AN ≤ B * T.E0 p.1 ^ A :=
    hdom hBN.le (by dsimp only [C₀]; linarith) hAN (le_add_of_nonneg_right hAP)
  have hPdom : BP * T.E0 p.1 ^ AP ≤ B * T.E0 p.1 ^ A :=
    hdom hBP.le (by dsimp only [C₀]; linarith) hAP (le_add_of_nonneg_left hAN)
  by_cases hn : ∃ m, p.1 ∈ Icc (C.left m) (C.right m)
  · obtain ⟨m, hpm⟩ := hn
    have hF : F p = canonicalWholeNegativeTransport C K z m p :=
      n04WholeComponentField_eq_negative hN.1.1
        (canonicalWholeNegativeTransport C K z) (τ z) id hpm
    rw [hF]
    have hb := hnegative z hz hs m p ⟨hpm, mem_univ _⟩
    exact ⟨hb.1.trans hNdom, hb.2.trans hNdom⟩
  · by_cases hpositivePiece : ∃ i : N04PositiveComponent D.a D.b (deriv D.w),
        p.1 ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i)
    · obtain ⟨i, hpi⟩ := hpositivePiece
      have hG := n04b_profileGeometry_of_through03 hN
      have hf : Continuous (deriv D.w) := hG.2.2.1.1.continuous_deriv (by simp)
      have hF : F p = τ z i p :=
        n04WholeComponentField_eq_positive hf hN.1.1.2.2.2.1
          (canonicalWholeNegativeTransport C K z) (τ z) id hpi
      rw [hF]
      have hcenter : buffer.centerLeft i < buffer.centerRight i :=
        (buffer.ordered i).2.1.trans
          ((buffer.ordered i).2.2.1.trans (buffer.ordered i).2.2.2.1)
      have hκ : 0 < κ i := (hcontrols i).1
      have hMσ : 0 ≤ Mσ i := zero_le_one.trans (hcontrols i).2.2.2.2.2.2.1
      have hb := hpositive 3 i (j i) (buffer.centerLeft i) (buffer.centerRight i)
        (κ i) (κ i) (M i) (Mσ i)
        (endpointFiberLower 3 (n04PositiveLeft i) (n04PositiveRight i)
          (buffer.centerLeft i) (buffer.centerRight i) (κ i) (Mσ i) * (κ i / 2))
        (Real.exp 2 * H i ^ 2) (Q z i)
        (buffer.ordered i).1 hcenter (buffer.ordered i).2.2.2.2
        (hcaps i).1 (hcaps i).2 hκ hMσ z hz hs (hm i) p ⟨hpi, mem_univ _⟩
      exact ⟨hb.1.trans hPdom, hb.2.trans hPdom⟩
    · have hF : F p = p := by
        simp only [F, n04WholeComponentField, dif_neg hn, dif_neg hpositivePiece, id_eq]
      rw [hF]
      have hpow : 1 ≤ E ^ A * T.E0 p.1 ^ A := by
        simpa only [Real.mul_rpow hEpos.le hEp.le] using
          Real.one_le_rpow (hscale p.1 hp.1) hA
      have hone : 1 ≤ B * T.E0 p.1 ^ A := by
        calc
          _ ≤ E ^ A * T.E0 p.1 ^ A := hpow
          _ ≤ C₀ * (E ^ A * T.E0 p.1 ^ A) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hC₀
              (mul_nonneg (Real.rpow_nonneg hEpos.le _) (Real.rpow_nonneg hEp.le _))
          _ = B * T.E0 p.1 ^ A := by dsimp only [B]; ring
      have hHp : T.H p.1 ≠ 0 := hpos.2.1.ne'
      have hMp : T.M p.1 ≠ 0 := (zero_lt_one.trans_le hpos.2.2.2).ne'
      simpa only [div_self hHp, div_self hMp] using And.intro hone hone

end ContinuousFlexibility.Analysis
