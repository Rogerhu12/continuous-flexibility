import ContinuousFlexibility.Analysis.RetainedPositiveIntervalEndpointX
import ContinuousFlexibility.Analysis.ActualNegativeMaterialRatioJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# Uniform physical-unit geometry for the same whole atlas

Each negative half retains its original typed-atlas cell and optical cut.
Each positive whole component uses the given actual midpoint host. The
same retained classification gives a two-sided endpoint-coordinate bound
to these exact samples. All widths are positive and at most the annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry

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
/-- A common bound before every piece and unit point, with no change of
sample, atlas, physical domain, reference gauge or material datum. -/
theorem n04WholeReferenceGauge_unit_material_geometry :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ,
      0 < V.physicalRight m - V.physicalLeft m ∧
      V.physicalRight m - V.physicalLeft m ≤ Γ.reference.b - Γ.reference.a ∧
      ∀ p ∈ unitStrip,
        (physicalUnitPoint V m p).1 ∈ Ioo Γ.reference.a Γ.reference.b ∧
        |endpointX 1 (Statements.endpointDistance Γ.reference (physicalUnitPoint V m p).1) -
          endpointX 1 (Statements.endpointDistance Γ.reference (T.sample (V.cell m)))| ≤ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  obtain ⟨AN, hAN, hnegative⟩ :=
    n04bActualTypedAtlas_negative_sample_endpointX hT hS hN hfield e₀
  obtain ⟨AP, hAP, hpositive⟩ :=
    retainedReference_positive_midpoint_sample_X_bound
      P hS₀ hband hq hΓ hw hcoordinates hN.1.1.2.2.2.1 hT
  refine ⟨max AN AP, hAN.trans (le_max_left _ _), ?_⟩
  intro m
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
      ⟨_, _, hl, hr, _, hsample, _, _, _, _, _, _⟩
    obtain ⟨hc, hwidth, hpoint⟩ :=
      n04bActualTypedAtlas_negative_physicalUnitPoint hT hS hN hfield e₀ k j.1 j.2 hk
    have he : physicalUnitPoint V m = physicalUnitPoint K k := by
      funext p
      simp only [physicalUnitPoint, V, k, hl, hr]
    refine ⟨by rw [hl, hr]; exact hc, by rw [hl, hr]; exact hwidth, ?_⟩
    intro p hp
    rw [he, hsample]
    refine ⟨(hpoint p hp).2, ?_⟩
    have hwhole := (hpoint p hp).1
    have hx := hnegative k j.1 j.2 hk (physicalUnitPoint K k p).1
      ⟨hwhole.1.le, hwhole.2.le⟩
    have hx' :
        |endpointX 1 (Statements.endpointDistance Γ.reference (physicalUnitPoint K k p).1) -
          endpointX 1 (Statements.endpointDistance Γ.reference (T.sample (K.cell k)))| ≤ AN := by
      simpa only [abs_sub_comm] using hx
    exact hx'.trans (le_max_left AN AP)
  | inr i =>
    rcases n04WholeReferenceGaugeAtlasData_positive_fields
      C L K e cell ψ χ h₀ τ σ Q N z₀ m i hi with
      ⟨_, _, hl, hr, _, hsample, _, _, _, _, _, _⟩
    have hf : Continuous (deriv Γ.reference.w) :=
      hΓ.2.1.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
    have hb := n04PositiveComponent_bounds hf i
    have hc : 0 < n04PositiveRight i - n04PositiveLeft i := sub_pos.mpr hb.2.1
    refine ⟨by rw [hl, hr]; exact hc,
      by rw [hl, hr]; linarith only [hb.1, hb.2.2], ?_⟩
    intro p hp
    have hpoint : (physicalUnitPoint V m p).1 ∈
        Ioo (n04PositiveLeft i) (n04PositiveRight i) := by
      have hlow := mul_pos hc hp.1.1
      have hupp := mul_lt_mul_of_pos_left hp.1.2 hc
      change V.physicalLeft m + (V.physicalRight m - V.physicalLeft m) * p.1 ∈ _
      rw [hl, hr]
      constructor <;> nlinarith only [hlow, hupp]
    refine ⟨⟨hb.1.trans_lt hpoint.1, hpoint.2.trans_le hb.2.2⟩, ?_⟩
    rw [hsample]
    exact (hpositive i (cell i) (hcell i) (physicalUnitPoint V m p).1
      ⟨hpoint.1.le, hpoint.2.le⟩).trans (le_max_right AN AP)

end ContinuousFlexibility.Analysis
