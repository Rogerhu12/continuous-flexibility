import ContinuousFlexibility.Analysis.CanonicalReferenceScalarColumnIdentities

/-!
# Uniform jets of the two actual scalar reference columns

The inverse and source-factor scalar families are fixed before the jet
order. Their material estimates and true physical range supply a common
bound for both physical columns. The numerical constant is selected
before any atlas, enumeration or field-identification proof is supplied.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- The actual left and nu source atoms inherit all mixed reference
jets from the same scalar inverse and source factor. Only numerical
constants are merged; the atlas and physical data remain unchanged. -/
theorem canonicalReferenceScalarColumns_material_jets
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (X F : ι → ℝ → ℝ)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) (Ioo (0 : ℝ) 1))
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (Ioo (0 : ℝ) 1))
    (hrange : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → X i x ∈ radialCore D)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i x,
      x ∈ Ioo (0 : ℝ) 1 → ∀ k, k ≤ N →
        |iteratedDeriv k (F i) x| ≤ A * W i ^ A ∧
        (1 ≤ k → |iteratedDeriv k (X i) x| ≤ A * W i ^ A)) :
    ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ (K : CanonicalData S) (piece : ι → ℕ),
      (∀ i p, p ∈ unitStrip →
        K.inverseChart (C.referenceState, 0) (piece i)
          (canonicalUnitPoint K (piece i) p) = (X i p.1, p.2)) →
      (∀ i p, p ∈ unitStrip →
        atom D T S C L K (C.referenceState, 0) (piece i) .sourceFactor p = F i p.1) →
      ∀ i v, v = .leftColumn ∨ v = .nuColumn →
        ContDiffOn ℝ ∞ (atom D T S C L K (C.referenceState, 0) (piece i) v) unitStrip ∧
        (∀ p ∈ unitStrip,
          atom D T S C L K (C.referenceState, 0) (piece i) v (p + (0, Real.pi)) =
            atom D T S C L K (C.referenceState, 0) (piece i) v p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom D T S C L K (C.referenceState, 0) (piece i) v) p| ≤
            B * W i ^ B := by
  intro s
  let V : Atom → ι → PolarPoint → ℝ := fun v i p =>
    F i p.1 * referenceScalarColumnRadial D S v (X i p.1) *
      referenceScalarColumnAngular v p.2
  have hsingle (v : Atom) (hv : v = .leftColumn ∨ v = .nuColumn) :
      ∃ M : ℝ, 1 ≤ M ∧ ∀ i,
        ContDiffOn ℝ ∞ (V v i) unitStrip ∧
        (∀ p ∈ unitStrip, V v i (p + (0, Real.pi)) = V v i p) ∧
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (V v i) p| ≤ M * W i ^ M := by
    have hregular := referenceScalarColumn_regular hS hN.1.1 v hv
    exact fixedReferenceScalarSource_material_jets W hW X F D.a D.b hX hF
      (fun i x hx => ⟨(hrange i x hx).1.le, (hrange i x hx).2.le⟩) hjets
      (referenceScalarColumnRadial D S v) (referenceScalarColumnAngular v)
      hregular.1 hregular.2.1 hregular.2.2 s
  obtain ⟨BL, hBL, hleft⟩ := hsingle .leftColumn (Or.inl rfl)
  obtain ⟨BN, hBN, hnu⟩ := hsingle .nuColumn (Or.inr rfl)
  let B : ℝ := BL + BN
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hBL, hBN]
  have hLB : BL ≤ B := le_add_of_nonneg_right (zero_le_one.trans hBN)
  have hNB : BN ≤ B := le_add_of_nonneg_left (zero_le_one.trans hBL)
  have hcost {M : ℝ} (hMB : M ≤ B) (i : ι) :
      M * W i ^ M ≤ B * W i ^ B :=
    mul_le_mul hMB (Real.rpow_le_rpow_of_exponent_le (hW i) hMB)
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) (zero_le_one.trans hB)
  refine ⟨B, hB, ?_⟩
  intro K piece hinverse hfactor i v hv
  have hmodel : ContDiffOn ℝ ∞ (V v i) unitStrip ∧
      (∀ p ∈ unitStrip, V v i (p + (0, Real.pi)) = V v i p) ∧
      ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (V v i) p| ≤ B * W i ^ B := by
    rcases hv with rfl | rfl
    · refine ⟨(hleft i).1, (hleft i).2.1, ?_⟩
      intro p hp a b hab
      exact ((hleft i).2.2 p hp a b hab).trans (hcost hLB i)
    · refine ⟨(hnu i).1, (hnu i).2.1, ?_⟩
      intro p hp a b hab
      exact ((hnu i).2.2 p hp a b hab).trans (hcost hNB i)
  have heq : EqOn (atom D T S C L K (C.referenceState, 0) (piece i) v)
      (V v i) unitStrip :=
    referenceScalarColumn_actual_eqOn hS hN K (piece i) (X i) (F i)
      (hinverse i) (hrange i) (hfactor i) v hv
  refine ⟨hmodel.1.congr (fun p hp => heq hp), ?_, ?_⟩
  · intro p hp
    have hp' : p + (0, Real.pi) ∈ unitStrip := by
      refine ⟨?_, mem_univ _⟩
      simpa only [Prod.fst_add, add_zero] using hp.1
    rw [heq hp', heq hp]
    exact hmodel.2.1 p hp
  · intro p hp a b hab
    rw [mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) heq a b hp]
    exact hmodel.2.2 p hp a b hab

end ContinuousFlexibility.Analysis
