module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
public import ContinuousFlexibility.Analysis.RetainedPositiveComponentMaterialWidth
public import ContinuousFlexibility.Analysis.WholeReferenceGaugePositiveGeometryJets
public import ContinuousFlexibility.Analysis.CanonicalAuxiliaryAtomPreservation

/-!
# Reference geometry bounds for the same positive family

The retained positive widths and the supplied all-order reference
certificate give the eight geometry atoms at their original samples.
The numerical bound is uniform in the auxiliary column. No current
geometry certificate is used to produce these reference bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

theorem n04PositiveGeometry_component_width_cost
    (W : N04RealizationStart) (X : N04RealizationChoice W) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      n04PositiveRight i - n04PositiveLeft i ≤ B * W.T.E0 (W.T.sample (X.cell i)) ^ B ∧
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ B * W.T.E0 (W.T.sample (X.cell i)) ^ B := by
  let widthData := ContinuousFlexibility.Radial.retainedReference_positive_component_material_width
    W.P W.metadata.selected W.metadata.first_two one_pos W.realizes W.hw W.coordinates
    W.through03.1.1.2.2.2.1 W.hT
  let C : ℝ := widthData.choose
  let A : ℝ := widthData.choose_spec.choose
  have hwidth := widthData.choose_spec.choose_spec
  let B : ℝ := max 1 (max C A)
  have hB : 1 ≤ B := le_max_left _ _
  have hCB : C ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hAB : A ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB, fun i => ?_⟩
  have hi := hwidth.2.2 i (X.cell i) (X.cell_mem i)
  have hE : 1 ≤ W.T.E0 (W.T.sample (X.cell i)) := W.floor _
  have hcost : C * W.T.E0 (W.T.sample (X.cell i)) ^ A ≤
      B * W.T.E0 (W.T.sample (X.cell i)) ^ B :=
    mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le hE hAB)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  exact ⟨hi.2.trans hcost, hi.1.trans hcost⟩

private theorem positiveGeometry_reference_atom_cases (a : Atom) (ha : atomIsGeometry a) :
    a = .chartRadial ∨ a = .chartAngleDefect ∨ a = .inverseRadial ∨
      a = .inverseAngleDefect ∨ a = .height ∨ a = .heightInverse ∨
      a = .jacobian ∨ a = .jacobianInverse ∨ a = .sourceFactor ∨ a = .sourceFactorInverse := by
  cases a <;> simp_all [atomIsGeometry]

private theorem positiveGeometry_reference_atom_exclusions (a : Atom) (ha : atomIsGeometry a) :
    a ≠ .auxiliaryColumn ∧ a ≠ .ratioE0 ∧ a ≠ .ratioE0Inverse := by
  cases a <;> simp_all [atomIsGeometry]

namespace N04RealizationGauge

theorem positiveGeometry_reference_atom_jets
    (G : N04RealizationGauge) {base : ℕ} {ε : ℝ} (hA : G.Admissible base ε)
    (hmaterial : N04PositiveReferenceMaterialBounds G.W.T G.X.cell G.Y G.H) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      ∀ m, G.Pos η m → ∀ a : Atom, atomIsGeometry a →
        ContDiffOn ℝ ∞ (G.atomRef η a m) unitStrip ∧
        (∀ q ∈ unitStrip, G.atomRef η a m (q + (0, Real.pi)) = G.atomRef η a m q) ∧
        ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
          |mixedDerivative i j (G.atomRef η a m) q| ≤
            B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  let C0 : ℝ := hmaterial.choose
  have hC0 : 1 ≤ C0 := hmaterial.choose_spec.1
  have hfloor := hmaterial.choose_spec.2.1
  have hjets := hmaterial.choose_spec.2.2
  let widthData := n04PositiveGeometry_component_width_cost G.W G.X
  let B : ℝ := widthData.choose
  have hB : 1 ≤ B := widthData.choose_spec.1
  have hwidth (i) :
      n04PositiveRight i - n04PositiveLeft i ≤
          B * (C0 * G.W.T.E0 (G.W.T.sample (G.X.cell i))) ^ B ∧
      (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤
          B * (C0 * G.W.T.E0 (G.W.T.sample (G.X.cell i))) ^ B := by
    have he : 0 ≤ G.W.T.E0 (G.W.T.sample (G.X.cell i)) :=
      zero_le_one.trans (G.W.floor _)
    have hcost := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow he (le_mul_of_one_le_left he hC0) (zero_le_one.trans hB))
      (zero_le_one.trans hB)
    exact ⟨(widthData.choose_spec.2 i).1.trans hcost,
      (widthData.choose_spec.2 i).2.trans hcost⟩
  have hreference := n04WholeReferenceGauge_positive_geometryReferenceJets_fixedFamily
    (D := G.W.D) (T := G.W.T) (S := G.W.S)
    G.W.C G.W.L hC0 hfloor (fun j => G.W.floor _) G.X.cell hB hwidth G.Y G.H
    (fun i => (hA.2.2.2.1 i).1) hjets
  intro s
  let orderData := hreference s
  let M : ℝ := orderData.choose
  have hM : 0 < M := orderData.choose_spec.1
  refine ⟨M, hM, fun η m hm a ha => ?_⟩
  have hraw := orderData.choose_spec.2 (G.W.A G.X.e₀) G.e G.τ G.σ G.Q G.N
    hA.2.2.2.2.1 m hm a (positiveGeometry_reference_atom_cases a ha)
  have hex := positiveGeometry_reference_atom_exclusions a ha
  have he : G.atomRef η a m =
      atom G.W.D G.W.T G.W.S G.W.C G.W.L
        (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
        (G.W.C.referenceState, 0) m a :=
    canonicalAtom_auxiliaryReplacement_enlarged_of_ne G.W.D G.W.T G.W.S G.W.C G.W.L
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
      η (G.W.C.referenceState, 0) m a hex.1 hex.2.1 hex.2.2
  refine ⟨hraw.1.congr (fun q _ => congrFun he q), ?_, ?_⟩
  · intro q hq
    exact (congrFun he _).trans ((hraw.2.1 q hq).trans (congrFun he q).symm)
  · intro q hq i j hij
    have hjet := congrArg (fun f : PolarPoint → ℝ => mixedDerivative i j f q) he
    have hbound := (congrArg abs hjet).trans_le (hraw.2.2 q hq i j hij)
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans (G.W.floor _))
        (le_enlargedMaterialData_E0 G.W.T _) hM.le) hM.le)

end N04RealizationGauge

end ContinuousFlexibility.Analysis
