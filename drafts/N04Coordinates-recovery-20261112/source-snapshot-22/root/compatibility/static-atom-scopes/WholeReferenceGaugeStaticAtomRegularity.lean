import ContinuousFlexibility.Analysis.CanonicalStaticAtomRegularity
import ContinuousFlexibility.Analysis.ActualNegativeMaterialRatioJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# Static atom regularity on the same actual whole atlas

The existing negative halves and positive components put every physical
unit point inside the material core. Thus all twelve static geometric and
material atoms of the actual reference-gauged atlas are ordinarily smooth
and periodic, before any restriction on states or choice of gauge fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeReferenceGauge_physicalUnitPoint_mem_core :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∀ m, MapsTo (fun p => (physicalUnitPoint V m p).1) unitStrip (Ioo D.a D.b) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  intro m p hp
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
      ⟨_, _, hl, hr, _, _, _, _, _, _, _, _⟩
    have hpoint := (n04bActualTypedAtlas_negative_physicalUnitPoint
      hT hS hN hfield e₀ k j.1 j.2 hk).2.2 p hp
    simpa only [physicalUnitPoint, hl, hr] using hpoint.2
  | inr i =>
    rcases n04WholeReferenceGaugeAtlasData_positive_fields
      C L K e cell ψ χ h₀ τ σ Q N z₀ m i hi with
      ⟨_, _, hl, hr, _, _, _, _, _, _, _, _⟩
    have hf : Continuous (deriv D.w) :=
      (n04b_profileGeometry_of_through03 hN).2.2.1.1.continuous_deriv (by simp)
    have hb := n04PositiveComponent_bounds hf i
    have hd : 0 < n04PositiveRight i - n04PositiveLeft i := sub_pos.mpr hb.2.1
    have hlow := mul_pos hd hp.1.1
    have hupp := mul_lt_mul_of_pos_left hp.1.2 hd
    change V.physicalLeft m + (V.physicalRight m - V.physicalLeft m) * p.1 ∈ _
    rw [hl, hr]
    constructor <;> nlinarith only [hlow, hupp, hb.1, hb.2.2]

theorem n04WholeReferenceGauge_static_atoms_regular :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∀ z m a, CanonicalFixedGeometryAtom a ∨ CanonicalMaterialRatioAtom a →
      ContDiffOn ℝ ∞ (atom D T S C L V z m a) unitStrip ∧
        ∀ p ∈ unitStrip,
          atom D T S C L V z m a (p + (0, Real.pi)) = atom D T S C L V z m a p := by
  dsimp only
  intro z m a ha
  exact ⟨canonical_staticAtom_contDiffOn_of_core hT z m ha
    (n04WholeReferenceGauge_physicalUnitPoint_mem_core
      hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N m),
    fun p _ => canonical_staticAtom_angle_period z m ha p⟩

end ContinuousFlexibility.Analysis
