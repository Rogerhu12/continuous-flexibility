module

public import ContinuousFlexibility.Analysis.ActualNegativeLengthMaterialBounds
public import ContinuousFlexibility.Analysis.RetainedPositiveComponentMaterialWidth
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeUnitMaterialGeometry
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Four actual length atoms on the same whole reference atlas

Negative halves use their original optical cut and stored sample. Positive
pieces use the actual whole-component width and its genuine midpoint cell;
their canonical interval is exactly `(0,1)`. An explicit material envelope
enlargement packages these value costs. The four actual atoms are constant
in space, so every positive-order mixed derivative is exactly zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff

def canonicalLengthSelector (canonical inverse : Bool) : Atom :=
  if canonical then
    if inverse then .canonicalLengthInverse else .canonicalLength
  else if inverse then .physicalLengthInverse else .physicalLength

theorem canonicalLengthSelector_eq_const
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (canonical inverse : Bool) :
    atom D T S C L K z m (canonicalLengthSelector canonical inverse) =
      fun _ : PolarPoint =>
        let d := if canonical then K.right m - K.left m
          else K.physicalRight m - K.physicalLeft m
        if inverse then d⁻¹ else d := by
  cases canonical <;> cases inverse <;> rfl

private theorem length_constant_mixed_bound (v B : ℝ)
    (hv : |v| ≤ B) (hB : 0 ≤ B) (a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b (fun _ : PolarPoint => v) p| ≤ B := by
  rw [n08_mixedDerivative_radial (fun _ : ℝ => v)]
  by_cases hb : b = 0
  · rw [if_pos hb, iteratedDeriv_const]
    by_cases ha : a = 0
    · rw [if_pos ha]
      exact hv
    · rw [if_neg ha, abs_zero]
      exact hB
  · rw [if_neg hb, abs_zero]
    exact hB

variable {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S₀ K₀ q length) (hS₀ : IsSelectedTail S₀)
  (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
  {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
  (hw : Γ.reference.w = P.pair.profile)
  (hcoordinates : R11aRetainedCoordinates P Γ)
  {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
  (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
  (hfield : N04bFieldRegularity Γ.reference S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex Γ.reference) (e : ℕ ≃ N04WholePieceIndex Γ.reference)
  (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
  (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
  (ψ χ : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
    PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
    PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
      PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
      PolarPoint → ℝ)
  (N : Set ℝ)

include P hS₀ hband hq hΓ hw hcoordinates hcell in
/-- One coefficient precedes every actual piece and all four length values.
Only the coefficient envelope changes; the atlas and all samples are fixed. -/
theorem n04WholeReferenceGauge_length_values_enlargedMaterialData :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let U := enlargedMaterialData T
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ,
      0 < V.physicalRight m - V.physicalLeft m ∧ 0 < V.right m - V.left m ∧
      V.physicalRight m - V.physicalLeft m ≤ B * U.E0 (U.sample (V.cell m)) ^ B ∧
      (V.physicalRight m - V.physicalLeft m)⁻¹ ≤ B * U.E0 (U.sample (V.cell m)) ^ B ∧
      V.right m - V.left m ≤ B * U.E0 (U.sample (V.cell m)) ^ B ∧
      (V.right m - V.left m)⁻¹ ≤ B * U.E0 (U.sample (V.cell m)) ^ B := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let U := enlargedMaterialData T
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  obtain ⟨BN, AN, hBN, hAN, hnegative⟩ :=
    n04bActualTypedAtlas_negative_length_material_bounds hT hS hN hfield e₀
  obtain ⟨BP, AP, hBP, hAP, hpositive⟩ :=
    retainedReference_positive_component_material_width
      P hS₀ hband hq hΓ hw hcoordinates hN.1.1.2.2.2.1 hT
  obtain ⟨CN, hCN, hpackN⟩ := coefficientEnvelope_pack BN AN
  obtain ⟨CP, hCP, hpackP⟩ := coefficientEnvelope_pack BP AP
  let B := 1 + CN + CP
  have hB : 0 < B := by dsimp only [B]; positivity
  have h1B : 1 ≤ B := by dsimp only [B]; linarith only [hCN, hCP]
  have hCNB : CN ≤ B := by dsimp only [B]; linarith only [hCP]
  have hCPB : CP ≤ B := by dsimp only [B]; linarith only [hCN]
  have htransfer (c a d : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) (hd : d ≤ B)
      (hpack : ∀ t : ℝ, 1 ≤ t → c * t ^ a ≤ d * t ^ d) (j : ℕ) :
      c * T.E0 (T.sample j) ^ a ≤ B * U.E0 (U.sample j) ^ B := by
    have hs := materialSample_mem_interval hΓ.2.1 hT j
    have hE : 0 < T.E0 (T.sample j) := (hT.2.1 _ hs).2.2.1
    have hfloor : 1 ≤ U.E0 (U.sample j) := one_le_enlargedMaterialData_E0 hT hs
    calc
      _ ≤ c * U.E0 (U.sample j) ^ a := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hE.le (le_enlargedMaterialData_E0 T (T.sample j)) ha) hc
      _ ≤ d * U.E0 (U.sample j) ^ d := hpack _ hfloor
      _ ≤ _ := mul_le_mul hd (Real.rpow_le_rpow_of_exponent_le hfloor hd)
        (Real.rpow_nonneg (zero_le_one.trans hfloor) _) hB.le
  have hone (j : ℕ) : 1 ≤ B * U.E0 (U.sample j) ^ B := by
    have hs := materialSample_mem_interval hΓ.2.1 hT j
    have hfloor : 1 ≤ U.E0 (U.sample j) := one_le_enlargedMaterialData_E0 hT hs
    have hp : 1 ≤ U.E0 (U.sample j) ^ B := Real.one_le_rpow hfloor hB.le
    exact h1B.trans (le_mul_of_one_le_right hB.le hp)
  obtain ⟨A₀, hA₀, hgeometry⟩ := n04WholeReferenceGauge_unit_material_geometry
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  refine ⟨B, hB, ?_⟩
  intro m
  refine ⟨(hgeometry m).1, ?_⟩
  cases hi : e m with
  | inl j =>
    let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
    have hk : e₀ k = .inl j := by
      have hpair : K.cutPair j.1 =
          (e₀.symm (.inl (j.1, false)), e₀.symm (.inl (j.1, true))) := rfl
      dsimp only [k]
      rw [hpair]
      rcases j with ⟨a, side⟩
      cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        Equiv.apply_symm_apply]
    rcases n04WholeReferenceGaugeAtlasData_negative_fields
      C L K e cell ψ χ h₀ τ σ Q N z₀ m j hi with
      ⟨hl, hr, hpl, hpr, _, hsample, _, _, _, _, _, _⟩
    have hcanonical : K.right k - K.left k = n04bRootCutRadius (C.travel j.1) := by
      simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_right,
        n04bTypedAtlasData_left, hk, sub_zero]
    have hcanonPos : 0 < K.right k - K.left k := by
      rw [hcanonical]
      exact n04bRootCutRadius_pos (n04b_referenceTravel_pos
        (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 j.1)
    have h := hnegative k j.1 j.2 hk
    have hc := htransfer BN AN CN hBN.le hAN hCNB hpackN (K.cell k)
    rw [hl, hr, hpl, hpr, hsample]
    exact ⟨hcanonPos, h.2.1.trans hc, h.1.trans hc,
      h.2.2.2.trans hc, h.2.2.1.trans hc⟩
  | inr i =>
    rcases n04WholeReferenceGaugeAtlasData_positive_fields
      C L K e cell ψ χ h₀ τ σ Q N z₀ m i hi with
      ⟨hl, hr, hpl, hpr, _, hsample, _, _, _, _, _, _⟩
    have h := hpositive i (cell i) (hcell i)
    have hc := htransfer BP AP CP hBP.le hAP hCPB hpackP (cell i)
    rw [hl, hr, hpl, hpr, hsample, sub_zero, inv_one]
    exact ⟨zero_lt_one, h.2.trans hc, h.1.trans hc, hone (cell i), hone (cell i)⟩

include P hS₀ hband hq hΓ hw hcoordinates hcell in
/-- The four actual static length atoms are smooth and periodic, and obey
the required sample bound at every finite spatial order on this same V. -/
theorem n04WholeReferenceGauge_lengthReferenceJets_enlargedMaterialData :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let U := enlargedMaterialData T
    (∀ z m canonical inverse,
      ContDiffOn ℝ ∞ (atom Γ.reference U S C L V z m
        (canonicalLengthSelector canonical inverse)) unitStrip ∧
      ∀ p ∈ unitStrip, atom Γ.reference U S C L V z m
        (canonicalLengthSelector canonical inverse) (p + (0, Real.pi)) =
          atom Γ.reference U S C L V z m (canonicalLengthSelector canonical inverse) p) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z m canonical inverse, ∀ p ∈ unitStrip,
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (atom Γ.reference U S C L V z m
          (canonicalLengthSelector canonical inverse)) p| ≤
            B * U.E0 (U.sample (V.cell m)) ^ B := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let U := enlargedMaterialData T
  obtain ⟨B, hB, hvalues⟩ := n04WholeReferenceGauge_length_values_enlargedMaterialData
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  have hvalues' : ∀ m : ℕ,
      0 < V.physicalRight m - V.physicalLeft m ∧ 0 < V.right m - V.left m ∧
      V.physicalRight m - V.physicalLeft m ≤ B * U.E0 (U.sample (V.cell m)) ^ B ∧
      (V.physicalRight m - V.physicalLeft m)⁻¹ ≤ B * U.E0 (U.sample (V.cell m)) ^ B ∧
      V.right m - V.left m ≤ B * U.E0 (U.sample (V.cell m)) ^ B ∧
      (V.right m - V.left m)⁻¹ ≤ B * U.E0 (U.sample (V.cell m)) ^ B := hvalues
  refine ⟨?_, fun s => ⟨B, hB, ?_⟩⟩
  · intro z m canonical inverse
    rw [canonicalLengthSelector_eq_const]
    exact ⟨contDiffOn_const, fun _ _ => rfl⟩
  · intro z m canonical inverse p hp a b hab
    have hv := hvalues' m
    let d := if canonical then V.right m - V.left m
      else V.physicalRight m - V.physicalLeft m
    have hvalue : |if inverse then d⁻¹ else d| ≤ B * U.E0 (U.sample (V.cell m)) ^ B := by
      cases canonical <;> cases inverse
      · simpa only [d, Bool.false_eq_true, ite_false, abs_of_pos hv.1] using hv.2.2.1
      · simpa only [d, Bool.false_eq_true, ite_false, ite_true,
          abs_of_pos (inv_pos.mpr hv.1)] using hv.2.2.2.1
      · simpa only [d, Bool.false_eq_true, ite_false, ite_true,
          abs_of_pos hv.2.1] using hv.2.2.2.2.1
      · simpa only [d, ite_true, abs_of_pos (inv_pos.mpr hv.2.1)] using hv.2.2.2.2.2
    have hs := materialSample_mem_interval hΓ.2.1 hT (V.cell m)
    have hfloor : 1 ≤ U.E0 (U.sample (V.cell m)) := one_le_enlargedMaterialData_E0 hT hs
    rw [canonicalLengthSelector_eq_const]
    exact length_constant_mixed_bound _ _ hvalue
      (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans hfloor) _)) a b p

end ContinuousFlexibility.Analysis
