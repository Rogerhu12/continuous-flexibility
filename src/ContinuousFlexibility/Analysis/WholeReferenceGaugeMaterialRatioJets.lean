import ContinuousFlexibility.Analysis.ActualNegativeMaterialRatioJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# The four actual negative H/M reference ratio atoms

The same whole atlas retains the old negative physical halves and their
stored samples. Thus its four H/M ratio atoms have genuine spatial jets,
not just zero state differences. The original E0 gives separate constants
and exponents. The explicit existing envelope enlargement packages them
into the single-constant form without changing H, M, samples or the atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff BigOperators

def canonicalHMAtom (useM inverse : Bool) : Atom :=
  if useM then (if inverse then .ratioMInverse else .ratioM)
  else (if inverse then .ratioHInverse else .ratioH)

theorem canonicalHMAtom_eq_normalizedPower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (useM inverse : Bool) :
    atom D T S C L K z m (canonicalHMAtom useM inverse) =
      fun p => materialHMNormalizedPower T useM (if inverse then -1 else 1)
        (T.sample (K.cell m)) (physicalUnitPoint K m p).1 := by
  cases useM <;> cases inverse <;> funext p <;>
    simp only [canonicalHMAtom, atom, materialHMNormalizedPower, materialHMWeight,
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

private theorem negative_HM_fields (z : AnnularState S × ℝ)
    (m : ℕ) (j : ℕ × Bool) (hi : e m = .inl j) (useM inverse : Bool) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ k, e₀ k = .inl j ∧ V.cell m = K.cell k ∧
      atom D T S C L V z m (canonicalHMAtom useM inverse) =
        fun p => materialHMNormalizedPower T useM (if inverse then -1 else 1)
          (T.sample (K.cell k)) (physicalUnitPoint K k p).1 := by
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
  rcases n04WholeReferenceGaugeAtlasData_negative_fields
    C L K e cell ψ χ h₀ τ σ Q N z m j hi with
    ⟨_, _, hleft, hright, _, hsample, _, _, _, _, _, _⟩
  refine ⟨k, hk, hsample, ?_⟩
  rw [canonicalHMAtom_eq_normalizedPower]
  funext p
  change materialHMNormalizedPower T useM (if inverse then -1 else 1)
      (T.sample (V.cell m)) (V.physicalLeft m + (V.physicalRight m - V.physicalLeft m) * p.1) =
    materialHMNormalizedPower T useM (if inverse then -1 else 1)
      (T.sample (K.cell k)) (K.physicalLeft k + (K.physicalRight k - K.physicalLeft k) * p.1)
  simp only [hsample, hleft, hright]

/-- These are the actual functions on the physical unit interval; their
smoothness and period do not use a final geometric jet certificate. -/
theorem n04WholeReferenceGauge_negative_HM_regular :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∀ z m j, e m = .inl j → ∀ useM inverse,
      ContDiffOn ℝ ∞ (atom D T S C L V z m (canonicalHMAtom useM inverse)) unitStrip ∧
      ∀ p ∈ unitStrip,
        atom D T S C L V z m (canonicalHMAtom useM inverse) (p + (0, Real.pi)) =
          atom D T S C L V z m (canonicalHMAtom useM inverse) p := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  intro z m j hi useM inverse
  obtain ⟨k, hk, _, he⟩ := negative_HM_fields
    hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N z m j hi useM inverse
  rw [he]
  let γ : ℝ := if inverse then -1 else 1
  let f := materialHMNormalizedPower T useM γ (T.sample (K.cell k))
  have hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b) :=
    ((materialHMWeight_contDiffOn hT useM).rpow_const_of_ne
      (fun r hr => (materialHMWeight_pos hT useM hr).ne')).mul contDiffOn_const
  have hmap : MapsTo (fun p => (physicalUnitPoint K k p).1) unitStrip (Ioo D.a D.b) := by
    intro p hp
    exact ((n04bActualTypedAtlas_negative_physicalUnitPoint
      hT hS hN hfield e₀ k j.1 j.2 hk).2.2 p hp).2
  have haffine : ContDiff ℝ ∞ (fun p => (physicalUnitPoint K k p).1) :=
    contDiff_const.add (contDiff_const.mul contDiff_fst)
  refine ⟨?_, ?_⟩
  · exact hf.comp haffine.contDiffOn hmap
  · intro p hp
    change f (K.physicalLeft k + (K.physicalRight k - K.physicalLeft k) * (p.1 + 0)) =
      f (K.physicalLeft k + (K.physicalRight k - K.physicalLeft k) * p.1)
    rw [add_zero]

/-- The original material data yield separate uniform coefficient and
exponent bounds for all angular orders at each fixed radial order. -/
theorem n04WholeReferenceGauge_negative_HM_jets
    (useM inverse : Bool) (a : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ z m j, e m = .inl j →
      ∀ p ∈ unitStrip, ∀ b : ℕ,
        |mixedDerivative a b (atom D T S C L V z m (canonicalHMAtom useM inverse)) p| ≤
          B * T.E0 (T.sample (V.cell m)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  obtain ⟨B, A, hB, hA, hbound⟩ :=
    n04bActualTypedAtlas_negative_materialRatio_unit_jets hT hS hN hfield e₀
      useM (if inverse then -1 else 1) a
  refine ⟨B, A, hB, hA, ?_⟩
  intro z m j hi p hp b
  obtain ⟨k, hk, hsample, he⟩ := negative_HM_fields
    hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N z m j hi useM inverse
  rw [he, hsample]
  exact hbound k j.1 j.2 hk p hp b

/-- The explicit previously verified enlargement is the only floor
used here. H, M, every sample and the actual atlas remain the same. -/
theorem n04WholeReferenceGauge_negative_HMReferenceJets_enlargedMaterialData :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let T' := enlargedMaterialData T
    (∀ z m j, e m = .inl j → ∀ useM inverse,
      ContDiffOn ℝ ∞ (atom D T' S C L V z m (canonicalHMAtom useM inverse)) unitStrip ∧
      ∀ p ∈ unitStrip,
        atom D T' S C L V z m (canonicalHMAtom useM inverse) (p + (0, Real.pi)) =
          atom D T' S C L V z m (canonicalHMAtom useM inverse) p) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z m j, e m = .inl j → ∀ useM inverse,
      ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b
          (atom D T' S C L V z m (canonicalHMAtom useM inverse)) p| ≤
            B * T'.E0 (T'.sample (V.cell m)) ^ B := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let T' := enlargedMaterialData T
  have hatom (z : AnnularState S × ℝ) (m : ℕ) (useM inverse : Bool) :
      atom D T' S C L V z m (canonicalHMAtom useM inverse) =
        atom D T S C L V z m (canonicalHMAtom useM inverse) := by
    cases useM <;> cases inverse <;> rfl
  refine ⟨?_, ?_⟩
  · intro z m j hi useM inverse
    rw [hatom]
    exact n04WholeReferenceGauge_negative_HM_regular
      hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N z m j hi useM inverse
  · intro s
    let I := Fin (s + 1) × Bool × Bool
    have hfamily (i : I) := n04WholeReferenceGauge_negative_HM_jets
      hT hS hN hfield e₀ e cell ψ χ h₀ τ σ Q N i.2.1 i.2.2 i.1.val
    choose C₀ A hC₀ hA hjet using hfamily
    choose B hB hpack using fun i : I => coefficientEnvelope_pack (C₀ i) (A i)
    let M : ℝ := 1 + ∑ i : I, B i
    have hsum : 0 ≤ ∑ i : I, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
    have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one hsum
    have hBM (i : I) : B i ≤ M :=
      (Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one)
    refine ⟨M, hM, ?_⟩
    intro z m j hi useM inverse p hp a b hab
    let i : I := (⟨a, by omega⟩, useM, inverse)
    let t := T'.E0 (T'.sample (V.cell m))
    have hs := materialSample_mem_interval hN.1.1.1.1 hT (V.cell m)
    have hEpos : 0 < T.E0 (T.sample (V.cell m)) := (hT.2.1 _ hs).2.2.1
    have hfloor : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hs
    have hpower : T.E0 (T.sample (V.cell m)) ^ A i ≤ t ^ A i :=
      Real.rpow_le_rpow hEpos.le (le_enlargedMaterialData_E0 T _) (hA i)
    rw [hatom]
    have hh := hjet i z m j hi p hp b
    calc
      _ ≤ C₀ i * T.E0 (T.sample (V.cell m)) ^ A i := hh
      _ ≤ C₀ i * t ^ A i := mul_le_mul_of_nonneg_left hpower (hC₀ i)
      _ ≤ B i * t ^ B i := hpack i t hfloor
      _ ≤ M * t ^ M := mul_le_mul (hBM i)
        (Real.rpow_le_rpow_of_exponent_le hfloor (hBM i))
        (Real.rpow_nonneg (zero_le_one.trans hfloor) _) hM.le

end ContinuousFlexibility.Analysis
