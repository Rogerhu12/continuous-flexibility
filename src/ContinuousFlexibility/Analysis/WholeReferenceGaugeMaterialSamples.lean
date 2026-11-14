module

public import ContinuousFlexibility.Analysis.ActualNegativeMaterialSamples
public import ContinuousFlexibility.Analysis.PositiveComponentMaterialDecay
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# Material samples of the same reference-gauged whole atlas

The positive cell map is retained, with only its actual midpoint-membership
property required. Negative labels are the original typed-atlas labels.
One endpoint-coordinate comparison therefore controls the real sample of
every current piece, before the state, component, gauge and physical point.
No point-to-sample reverse coefficient bound on positive pieces is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

/-- The existing midpoint argument works for any cell that actually
contains that midpoint, without choosing a new cell map. -/
private theorem positive_midpoint_sample_endpointX
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ D.cells (cell i)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i r,
      r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) → r ∈ Ioo D.a D.b →
      endpointX 1 (Statements.endpointDistance D (T.sample (cell i))) ≤
        endpointX 1 (Statements.endpointDistance D r) + A := by
  have hf : Continuous (deriv D.w) :=
    hRef.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, hcompare⟩ := hdata
  obtain ⟨B, P, hB, _, hindex⟩ := hcompare
  refine ⟨2 * B + 1, by positivity, ?_⟩
  intro i r hr hrcore
  have hmcore := n04PositiveMidpoint_mem_core hf i
  have hb := n04PositiveComponent_bounds hf i
  let d := Statements.endpointDistance D r
  let dₘ := Statements.endpointDistance D (n04PositiveMidpoint i)
  have hd : 0 < d := lt_min (sub_pos.mpr hrcore.1) (sub_pos.mpr hrcore.2)
  have hdm : 0 < dₘ := lt_min (sub_pos.mpr hmcore.1) (sub_pos.mpr hmcore.2)
  have hdist : d ≤ 2 * dₘ := endpointDistance_le_twice_interval_midpoint hb.1 hb.2.2 hr
  have hquot : d / dₘ ≤ 2 := (div_le_iff₀ hdm).mpr hdist
  have hlog : Real.log d - Real.log dₘ ≤ 1 := by
    rw [← Real.log_div hd.ne' hdm.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hd hdm)
    linarith only [h, hquot]
  have hu : Real.log (1 / dₘ) ≤ Real.log (1 / d) + 1 := by
    rw [Real.log_div one_ne_zero hdm.ne', Real.log_div one_ne_zero hd.ne', Real.log_one]
    linarith only [hlog]
  have hv : Real.log (1 / d) ≤ (Real.sqrt (Real.log (1 / d))) ^ 2 := by
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  have hmX : endpointX 1 dₘ ≤ endpointX 1 d + 1 := by
    change Real.sqrt (Real.log (1 / dₘ)) ≤ Real.sqrt (Real.log (1 / d)) + 1
    exact Real.sqrt_le_iff.mpr ⟨by positivity,
      by nlinarith only [hu, hv, Real.sqrt_nonneg (Real.log (1 / d))]⟩
  have hsIndex := (hindex (cell i) (T.sample (cell i)) (hsample (cell i))).1
  have hmIndex := (hindex (cell i) (n04PositiveMidpoint i) (hcell i)).1
  have hs := (abs_le.mp hsIndex).2
  have hm := (abs_le.mp hmIndex).1
  change endpointX 1 (Statements.endpointDistance D (T.sample (cell i))) ≤
    endpointX 1 d + (2 * B + 1)
  change -B ≤ endpointX 1 dₘ - (D.cellIndex (cell i) : ℝ) at hm
  linarith only [hs, hm, hmX]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (hcell : ∀ i, n04PositiveMidpoint i ∈ D.cells (cell i))
  (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

include hcell in
/-- The actual physical domains give the required core membership and
one-sided comparison with the stored sample, even before restricting states. -/
theorem n04WholeReferenceGauge_sample_endpointX :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z m p, p ∈ physicalPieceOpen S V z m →
      p.1 ∈ Ioo D.a D.b ∧
      endpointX 1 (Statements.endpointDistance D (T.sample (V.cell m))) ≤
        endpointX 1 (Statements.endpointDistance D p.1) + A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  obtain ⟨AN, hAN, hnegative⟩ :=
    n04bActualTypedAtlas_negative_sample_endpointX hT hS hN hfield e₀
  obtain ⟨AP, hAP, hpositive⟩ :=
    positive_midpoint_sample_endpointX hT hN.1.1.1.1 cell hcell
  have hf : Continuous (deriv D.w) :=
    (n04b_profileGeometry_of_through03 hN).2.2.1.1.continuous_deriv (by simp)
  refine ⟨AN + AP, add_nonneg hAN hAP, ?_⟩
  intro z m p hp
  cases hi : e m with
  | inl j =>
    rcases j with ⟨a, side⟩
    let k := if side then (K.cutPair a).2 else (K.cutPair a).1
    have hk : e₀ k = .inl (a, side) := by
      have hpair : K.cutPair a =
          (e₀.symm (.inl (a, false)), e₀.symm (.inl (a, true))) := rfl
      dsimp only [k]
      rw [hpair]
      cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        Equiv.apply_symm_apply]
    rcases n04WholeReferenceGaugeAtlasData_negative_fields
      C L K e cell ψ χ h₀ τ σ Q N z m (a, side) hi with
      ⟨_, _, _, _, hdomain, hsample, _, _, _, _, _, _⟩
    have hpK : p ∈ physicalPieceOpen S K z k := by rwa [hdomain] at hp
    have hpwhole : p ∈ Ioo (C.left a) (C.right a) ×ˢ (univ : Set ℝ) := by
      apply n04b_typed_negative_domain_subset (D := D) (C := C)
        (Γ := n04bActualTravelChart S C L z) (a, side)
      simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen, hk] using hpK
    have hb := hN.1.1.2.2.2.1.1 a
    refine ⟨⟨hb.1.trans hpwhole.1.1, hpwhole.1.2.trans hb.2.2⟩, ?_⟩
    change endpointX 1 (Statements.endpointDistance D (T.sample (V.cell m))) ≤ _
    rw [hsample]
    have h := (abs_le.mp
      (hnegative k a side hk p.1 ⟨hpwhole.1.1.le, hpwhole.1.2.le⟩)).2
    linarith only [h, hAP]
  | inr i =>
    rcases n04WholeReferenceGaugeAtlasData_positive_fields
      C L K e cell ψ χ h₀ τ σ Q N z m i hi with
      ⟨_, _, _, _, hdomain, hsample, _, _, _, _, _, _⟩
    have hpi : p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) := by
      rwa [hdomain] at hp
    have hb := n04PositiveComponent_bounds hf i
    have hcore : p.1 ∈ Ioo D.a D.b :=
      ⟨hb.1.trans_lt hpi.1.1, hpi.1.2.trans_le hb.2.2⟩
    refine ⟨hcore, ?_⟩
    change endpointX 1 (Statements.endpointDistance D (T.sample (V.cell m))) ≤ _
    rw [hsample]
    have h := hpositive i p.1 ⟨hpi.1.1.le, hpi.1.2.le⟩ hcore
    linarith only [h, hAN]

include hcell in
/-- The normalizer and every prescribed sample coefficient power use the
same actual cell, with constants uniform before all states and pieces. -/
theorem n04WholeReferenceGauge_material_sample_comparison (P : ℝ) (hP : 0 ≤ P) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ BH AH BE AE : ℝ, 0 < BH ∧ 0 ≤ AH ∧ 0 < BE ∧ 0 ≤ AE ∧
      ∀ z m p, p ∈ physicalPieceOpen S V z m →
      T.H p.1 / T.H (T.sample (V.cell m)) ≤ BH * T.E0 p.1 ^ AH ∧
        T.E0 (T.sample (V.cell m)) ^ P ≤ BE * T.E0 p.1 ^ AE := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  obtain ⟨A, hA, hpoint⟩ := n04WholeReferenceGauge_sample_endpointX
    hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  obtain ⟨BH, AH, BE, AE, hBH, hAH, hBE, hAE, hbound⟩ :=
    material_oneSided_endpoint_comparison hT hN.1.1.1.1 hP hA
  refine ⟨BH, AH, BE, AE, hBH, hAH, hBE, hAE, ?_⟩
  intro z m p hp
  have h := hpoint z m p hp
  exact hbound p.1 (T.sample (V.cell m)) h.1
    (materialSample_mem_interval hN.1.1.1.1 hT (V.cell m)) h.2

include hcell in
/-- Every strictly smaller positive sample-height exponent absorbs a
fixed physical coefficient cost on all pieces of this same V. -/
theorem n04WholeReferenceGauge_material_sample_height_decay
    (γ β P : ℝ) (hβ : 0 < β) (hβγ : β < γ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ B : ℝ, 0 < B ∧ ∀ z m p, p ∈ physicalPieceOpen S V z m →
      T.H p.1 ^ γ * T.E0 p.1 ^ P ≤ B * T.H (T.sample (V.cell m)) ^ β := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  obtain ⟨A₀, hA₀, hpoint⟩ := n04WholeReferenceGauge_sample_endpointX
    hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  obtain ⟨BH, AH, BE, AE, hBH, hAH, hBE, hAE, hcomparison⟩ :=
    n04WholeReferenceGauge_material_sample_comparison
      hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N 0 (by norm_num)
  obtain ⟨B, hB, hbound⟩ :=
    material_height_residual_of_polynomial_ratio (A := AH) hT hBH hβ hβγ P
  refine ⟨B, hB, ?_⟩
  intro z m p hp
  exact hbound p.1 (T.sample (V.cell m)) (hpoint z m p hp).1
    (materialSample_mem_interval hN.1.1.1.1 hT (V.cell m)) (hcomparison z m p hp).1

end ContinuousFlexibility.Analysis
