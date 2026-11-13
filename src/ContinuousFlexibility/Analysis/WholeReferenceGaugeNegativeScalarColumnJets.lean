import ContinuousFlexibility.Analysis.ActualNegativeReferenceScalarSourceData
import ContinuousFlexibility.Analysis.CanonicalReferenceScalarColumnMaterialJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeAtomTransport
import ContinuousFlexibility.Analysis.CanonicalAuxiliaryAtomPreservation

/-!
# The actual negative scalar columns of the same whole atlas

The old atlas and its sample are fixed before the numerical envelopes.
Its literal inverse/source slices supply both columns. All whole-atlas
and material-enlargement steps are equalities of the actual functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- The same negative left/nu atoms are smooth, periodic and bounded at
every spatial order. Only the material cost is enlarged; the original
atlas, optical host, physical columns and positive family are retained. -/
theorem n04WholeReferenceGauge_negative_scalarColumnReferenceJets_enlargedMaterialData
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
      ∀ m, V.positive m = false → ∀ v : Atom,
        (v = .leftColumn ∨ v = .nuColumn) →
        ContDiffOn ℝ ∞ (atom D U S C L V (C.referenceState, 0) m v) unitStrip ∧
        (∀ p ∈ unitStrip, atom D U S C L V (C.referenceState, 0) m v
          (p + (0, Real.pi)) = atom D U S C L V (C.referenceState, 0) m v p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom D U S C L V (C.referenceState, 0) m v) p| ≤
            BM * U.E0 (U.sample (V.cell m)) ^ BM := by
  classical
  by_cases hoptical : ∀ m, ∃ j, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)
  · let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let U := enlargedMaterialData T
    let piece : ℕ × Bool → ℕ := fun i => e₀.symm (.inl i)
    let X : (ℕ × Bool) → ℝ → ℝ := fun i t =>
      (K.inverseChart (C.referenceState, 0) (piece i)
        (canonicalUnitPoint K (piece i) (t, 0))).1
    let F : (ℕ × Bool) → ℝ → ℝ := fun i t =>
      atom D T S C L K (C.referenceState, 0) (piece i) .sourceFactor (t, 0)
    obtain ⟨C0, hC0, hfloor, hdata, hjets⟩ :=
      n04bActualTypedAtlas_negative_scalarSource_material_data hT hS hN hfield e₀ hK₀ hoptical
    let W : ℕ × Bool → ℝ := fun i => C0 * T.E0 (T.sample (K.cell (piece i)))
    have hW (i : ℕ × Bool) : 1 ≤ W i := hfloor (K.cell (piece i))
    intro s
    obtain ⟨M, hM, hcolumns⟩ := canonicalReferenceScalarColumns_material_jets hS hN W hW X F
      (fun i => (hdata i).1) (fun i => (hdata i).2.1)
      (fun i x hx => (hdata i).2.2.1 x hx) hjets s
    have hcolumnsK := hcolumns K piece (fun i p hp => ((hdata i).2.2.2 p hp).1)
      (fun i p hp => ((hdata i).2.2.2 p hp).2)
    obtain ⟨BM, hBM, hpack⟩ := coefficientEnvelope_pack (M * C0 ^ M) M
    refine ⟨BM, hBM, ?_⟩
    intro e cell ψ χ h₀ τ σ Q N _
    dsimp only
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    intro m hm v hv
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
        have hpiece : k = piece j := e₀.injective (hk.trans (e₀.apply_symm_apply _).symm)
        have hnegative : K.positive k = false := by
          simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_positive, hk,
            n04TypedPiecePositive]
        have hratios : v ≠ .ratioE0 ∧ v ≠ .ratioE0Inverse := by
          rcases hv with rfl | rfl <;> simp
        have hatom : atom D U S C L V (C.referenceState, 0) m v =
            atom D T S C L K (C.referenceState, 0) (piece j) v := by
          have hwhole := n04WholeReferenceGaugeAtlasData_negative_atom U C L K e cell
            ψ χ h₀ τ σ Q N (C.referenceState, 0) m j hi hnegative v
          have hmaterial := canonicalAtom_enlargedMaterialData_of_ne_ratios
            D T S C L K (C.referenceState, 0) k v hratios.1 hratios.2
          simpa only [hpiece] using hwhole.trans hmaterial
        have hsample : V.cell m = K.cell (piece j) := by
          have hh : V.cell m = K.cell k := (n04WholeReferenceGaugeAtlasData_negative_fields
            C L K e cell ψ χ h₀ τ σ Q N (C.referenceState, 0) m j hi).2.2.2.2.2.1
          rw [hpiece] at hh
          exact hh
        have hactual := hcolumnsK j v hv
        rw [← hatom] at hactual
        refine ⟨hactual.1, hactual.2.1, ?_⟩
        intro p hp a b hab
        rw [hsample]
        let t : ℝ := U.E0 (U.sample (K.cell (piece j)))
        have hs := materialSample_mem_interval hN.1.1.1.1 hT (K.cell (piece j))
        have ht : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hs
        have hWt : W j ≤ C0 * t := mul_le_mul_of_nonneg_left
          (le_enlargedMaterialData_E0 T (T.sample (K.cell (piece j))))
          (zero_le_one.trans hC0)
        calc
          _ ≤ M * W j ^ M := hactual.2.2 p hp a b hab
          _ ≤ M * (C0 * t) ^ M := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (zero_le_one.trans (hW j)) hWt (zero_le_one.trans hM))
            (zero_le_one.trans hM)
          _ = (M * C0 ^ M) * t ^ M := by
            rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
            ring
          _ ≤ BM * t ^ BM := hpack t ht
  · intro s
    refine ⟨1, zero_lt_one, ?_⟩
    intro e cell ψ χ h₀ τ σ Q N hopt
    exact (hoptical hopt).elim

end ContinuousFlexibility.Analysis
