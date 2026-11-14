module

public import ContinuousFlexibility.Analysis.ActualNegativeEnvelopeRatioJets
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# The actual negative E0 reference ratio atoms

The fixed whole atlas keeps its original negative halves and cell samples.
The explicitly enlarged envelope is evaluated as a new scalar function;
neither its ratios nor their derivatives are identified with the old ones.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff BigOperators

def canonicalE0Atom (inverse : Bool) : Atom :=
  if inverse then .ratioE0Inverse else .ratioE0

theorem canonicalE0Atom_eq_normalizedPower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (inverse : Bool) :
    atom D T S C L K z m (canonicalE0Atom inverse) =
      fun p => materialE0NormalizedPower T (if inverse then -1 else 1)
        (T.sample (K.cell m)) (physicalUnitPoint K m p).1 := by
  cases inverse <;> funext p <;>
    simp only [canonicalE0Atom, atom, materialE0NormalizedPower,
      Bool.false_eq_true, ite_false, ite_true, neg_neg, Real.rpow_one,
      Real.rpow_neg_one, div_eq_mul_inv, mul_comm]

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

private theorem negative_E0_fields (U : MaterialData) (z : AnnularState S × ℝ)
    (m : ℕ) (j : ℕ × Bool) (hi : e m = .inl j) (inverse : Bool) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ k, e₀ k = .inl j ∧ V.cell m = K.cell k ∧
      atom D U S C L V z m (canonicalE0Atom inverse) =
        fun p => materialE0NormalizedPower U (if inverse then -1 else 1)
          (U.sample (K.cell k)) (physicalUnitPoint K k p).1 := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
  have hk : e₀ k = .inl j := by
    have hpair : K.cutPair j.1 =
        (e₀.symm (.inl (j.1, false)), e₀.symm (.inl (j.1, true))) := rfl
    dsimp only [k]
    rw [hpair]
    rcases j with ⟨a, side⟩
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      Equiv.apply_symm_apply]
  have hfields : V.left m = K.left k ∧ V.right m = K.right k ∧
      V.physicalLeft m = K.physicalLeft k ∧ V.physicalRight m = K.physicalRight k ∧
      physicalPieceOpen S V z m = physicalPieceOpen S K z k ∧
      V.cell m = K.cell k ∧ V.positive m = false ∧
      V.chart z m = K.chart z k ∧ V.inverseChart z m = K.inverseChart z k ∧
      V.height z m = K.height z k ∧ V.coefficients z m = K.coefficients z k ∧
      V.potential z m = K.potential z k :=
    n04WholeReferenceGaugeAtlasData_negative_fields C L K e cell ψ χ h₀ τ σ Q N z m j hi
  obtain ⟨_, _, hleft, hright, _, hsample, _, _, _, _, _, _⟩ := hfields
  refine ⟨k, hk, hsample, ?_⟩
  rw [canonicalE0Atom_eq_normalizedPower]
  funext p
  change materialE0NormalizedPower U (if inverse then -1 else 1)
      (U.sample (V.cell m)) (V.physicalLeft m + (V.physicalRight m - V.physicalLeft m) * p.1) =
    materialE0NormalizedPower U (if inverse then -1 else 1)
      (U.sample (K.cell k)) (K.physicalLeft k + (K.physicalRight k - K.physicalLeft k) * p.1)
  simp only [hsample, hleft, hright]

/-- This applies both to the original data and to an explicitly enlarged
datum with the same samples. The atlas is still the original actual V. -/
theorem n04WholeReferenceGauge_negative_E0_jets
    (U : MaterialData) (hU : IsMaterialData D U) (hsample : U.sample = T.sample)
    (inverse : Bool) (a : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ z m j, e m = .inl j →
      ∀ p ∈ unitStrip, ∀ b : ℕ,
        |mixedDerivative a b (atom D U S C L V z m (canonicalE0Atom inverse)) p| ≤
          B * U.E0 (U.sample (V.cell m)) ^ A := by
  dsimp only
  obtain ⟨B, A, hB, hA, hbound⟩ :=
    n04bActualTypedAtlas_negative_envelopeRatio_unit_jets hT hS hN hfield e₀
      U hU hsample (if inverse then -1 else 1) a
  refine ⟨B, A, hB, hA, ?_⟩
  intro z m j hi p hp b
  obtain ⟨k, hk, hcell, he⟩ := negative_E0_fields
    hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N U z m j hi inverse
  rw [he, hcell]
  exact hbound k j.1 j.2 hk p hp b

/-- The new E0 ratios themselves are differentiated. The proven floor of
the explicit enlargement packages all finite orders into a common B. -/
theorem n04WholeReferenceGauge_negative_E0ReferenceJets_enlargedMaterialData :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let T' := enlargedMaterialData T
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z m j, e m = .inl j → ∀ inverse,
      ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b
          (atom D T' S C L V z m (canonicalE0Atom inverse)) p| ≤
            B * T'.E0 (T'.sample (V.cell m)) ^ B := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let T' := enlargedMaterialData T
  have hT' : IsMaterialData D T' := isMaterialData_enlargedMaterialData hN.1.1.1.1 hT
  have hsample : T'.sample = T.sample := rfl
  intro s
  let I := Fin (s + 1) × Bool
  have hfamily (i : I) := n04WholeReferenceGauge_negative_E0_jets
    hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N T' hT' hsample i.2 i.1.val
  choose C₀ A hC₀ hA hjet using hfamily
  choose B hB hpack using fun i : I => coefficientEnvelope_pack (C₀ i) (A i)
  let M : ℝ := 1 + ∑ i : I, B i
  have hsum : 0 ≤ ∑ i : I, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hBM (i : I) : B i ≤ M :=
    (Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨M, hM, ?_⟩
  intro z m j hi inverse p hp a b hab
  let i : I := (⟨a, by omega⟩, inverse)
  let t := T'.E0 (T'.sample (V.cell m))
  have hs := materialSample_mem_interval hN.1.1.1.1 hT (V.cell m)
  have hfloor : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hs
  have hh := hjet i z m j hi p hp b
  calc
    _ ≤ C₀ i * t ^ A i := hh
    _ ≤ B i * t ^ B i := hpack i t hfloor
    _ ≤ M * t ^ M := mul_le_mul (hBM i)
      (Real.rpow_le_rpow_of_exponent_le hfloor (hBM i))
      (Real.rpow_nonneg (zero_le_one.trans hfloor) _) hM.le

end ContinuousFlexibility.Analysis
