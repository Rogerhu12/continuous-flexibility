import ContinuousFlexibility.Analysis.FixedPositiveReferenceScalarSourceData
import ContinuousFlexibility.Analysis.CanonicalReferenceScalarColumnMaterialJets

/-!
# The two scalar columns of the same positive reference family

The literal inverse and source factor are supplied by the already fixed
coordinate and height. The column envelope precedes the whole atlas and
its enumeration; no reference family, cutoff or sample is selected here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- The actual left and nu columns use the same fixed positive family
and the original material sample. Only numerical bounds depend on the
spatial order. -/
theorem n04WholeReferenceGauge_positive_scalarColumnReferenceJets_fixedFamily
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {C0 : ℝ} (hC0 : 1 ≤ C0) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j))
    (hE0 : ∀ j, 1 ≤ T.E0 (T.sample j))
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    {B : ℝ} (hB : 1 ≤ B)
    (hwidth : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      n04PositiveRight i - n04PositiveLeft i ≤ B * (C0 * T.E0 (T.sample (cell i))) ^ B ∧
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ B * (C0 * T.E0 (T.sample (cell i))) ^ B)
    (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv (k + 1) (Y i) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A ∧
        |iteratedDeriv k (H i) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A ∧
        |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
        A * (C0 * T.E0 (T.sample (cell i))) ^ A) :
    ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧ ∀ (K : CanonicalData S)
      (e : ℕ ≃ N04WholePieceIndex D)
      (τ σ : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (Q : (AnnularState S × ℝ) →
        N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ),
      (∀ i, τ (C.referenceState, 0) i = id ∧
        σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1)) →
      let V := n04WholeReferenceGaugeAtlasData C L K e cell
        (fun i => positiveReferenceCylinderChart (Y i))
        (fun i => positiveReferenceCylinderInverse (Y i))
        (fun i p => H i p.1) τ σ Q N
      ∀ m, V.positive m = true → ∀ v : Atom,
        (v = .leftColumn ∨ v = .nuColumn) →
        ContDiffOn ℝ ∞ (atom D T S C L V (C.referenceState, 0) m v) unitStrip ∧
        (∀ p ∈ unitStrip, atom D T S C L V (C.referenceState, 0) m v
          (p + (0, Real.pi)) = atom D T S C L V (C.referenceState, 0) m v p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom D T S C L V (C.referenceState, 0) m v) p| ≤
            BM * T.E0 (T.sample (V.cell m)) ^ BM := by
  classical
  let W : N04PositiveComponent D.a D.b (deriv D.w) → ℝ :=
    fun i => C0 * T.E0 (T.sample (cell i))
  let X : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ :=
    fun i => Function.invFun (Y i)
  let F : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ :=
    fun i => positiveReferenceGeometryScalar
      (n04PositiveLeft i) (n04PositiveRight i) (Y i) (H i) .sourceFactor
  have hW (i) : 1 ≤ W i := hfloor (cell i)
  have hD := n04b_profileGeometry_of_through03 hN
  obtain ⟨hdata, hscalar⟩ := fixedPositiveReference_scalarSource_material_data
    (hD.2.2.1.1.continuous_deriv (by simp)) W hW hB hwidth Y H hgeometry hjets
  intro s
  obtain ⟨M, hM, hcolumns⟩ := canonicalReferenceScalarColumns_material_jets hS hN W hW X F
    (fun i => (hdata i).1.contDiffOn) (fun i => (hdata i).2.1.contDiffOn)
    (fun i x hx => (hdata i).2.2 x hx) hscalar s
  obtain ⟨BM, hBM, hpack⟩ := coefficientEnvelope_pack (M * C0 ^ M) M
  refine ⟨BM, hBM, ?_⟩
  intro K e τ σ Q N href
  let ψ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint :=
    fun i => positiveReferenceCylinderChart (Y i)
  let χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint :=
    fun i => positiveReferenceCylinderInverse (Y i)
  let h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ :=
    fun i p => H i p.1
  let V : CanonicalData S := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let piece : N04PositiveComponent D.a D.b (deriv D.w) → ℕ :=
    fun i => e.symm (.inr i)
  have hident (i) :
      (∀ p ∈ unitStrip, V.inverseChart (C.referenceState, 0) (piece i)
        (canonicalUnitPoint V (piece i) p) = (X i p.1, p.2)) ∧
      (∀ p ∈ unitStrip, atom D T S C L V (C.referenceState, 0)
        (piece i) .sourceFactor p = F i p.1) ∧ V.cell (piece i) = cell i := by
    have hi : e (piece i) = .inr i := e.apply_symm_apply (.inr i)
    obtain ⟨hl, hr, hpl, hpr, _, hsample, _, hF, hG, hH, _, _⟩ :=
      n04WholeReferenceGaugeAtlasData_positive_fields C L K e cell ψ χ h₀ τ σ Q N
        (C.referenceState, 0) (piece i) i hi
    have he := wholePositiveReferenceGauge_reference (ψ i) (χ i) (h₀ i)
      (href i).1 (href i).2.1 (href i).2.2
    have hsource := positiveReferenceGeometry_actual_atom_eq (D := D) (T := T)
      C L V (C.referenceState, 0) (piece i) (hgeometry i) hl hr hpl hpr
      (hF.trans he.1) (hG.trans he.2.1) (hH.trans he.2.2) .sourceFactor (by simp)
    refine ⟨?_, ?_, hsample⟩
    · intro p hp
      have hunit : canonicalUnitPoint V (piece i) p = p := by
        have hl' : V.left (piece i) = 0 := hl
        have hr' : V.right (piece i) = 1 := hr
        change (V.left (piece i) +
          (V.right (piece i) - V.left (piece i)) * p.1, p.2) = p
        simp only [hl', hr', sub_zero, one_mul, zero_add, Prod.mk.eta]
      rw [hunit]
      exact congrFun (hG.trans he.2.1) p
    · intro p hp
      exact congrFun hsource p
  dsimp only
  intro m hm v hv
  cases hi : e m with
  | inl j =>
      have hnegative : V.positive m = false := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hnegative.symm.trans hm))
  | inr i =>
      have hpiece : piece i = m := e.injective (by
        simp only [piece, Equiv.apply_symm_apply, hi])
      have hactual := hcolumns V piece (fun i => (hident i).1)
        (fun i => (hident i).2.1) i v hv
      have hsample : V.cell m = cell i := by
        simpa only [hpiece] using (hident i).2.2
      have hresult :
          ContDiffOn ℝ ∞ (atom D T S C L V (C.referenceState, 0) m v) unitStrip ∧
          (∀ p ∈ unitStrip, atom D T S C L V (C.referenceState, 0) m v
            (p + (0, Real.pi)) = atom D T S C L V (C.referenceState, 0) m v p) ∧
          ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
            |mixedDerivative a b (atom D T S C L V (C.referenceState, 0) m v) p| ≤
              M * W i ^ M := by
        simpa only [hpiece] using hactual
      refine ⟨hresult.1, hresult.2.1, ?_⟩
      intro p hp a b hab
      rw [hsample]
      have ht : 1 ≤ T.E0 (T.sample (cell i)) := hE0 (cell i)
      calc
        _ ≤ M * W i ^ M := hresult.2.2 p hp a b hab
        _ = (M * C0 ^ M) * T.E0 (T.sample (cell i)) ^ M := by
          dsimp only [W]
          rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
          ring
        _ ≤ BM * T.E0 (T.sample (cell i)) ^ BM := hpack _ ht

end ContinuousFlexibility.Analysis
