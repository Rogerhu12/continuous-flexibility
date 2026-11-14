import ContinuousFlexibility.Analysis.N03RecoveredCoefficientField
import ContinuousFlexibility.Analysis.CoefficientProbeRecoveryBounds
import ContinuousFlexibility.Analysis.FiniteProbeRecoveryBounds
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Actual corrected coefficient jets on the fixed negative components

The four height probes are fixed before the state. Their genuine source
jets control the removable sine quotients with loss two. The recovered
field agrees as a whole germ with the stored corrected coefficients at
every point of the fixed negative component, including the cut axes.
Consequently the bound concerns actual mixed derivatives of the stored
coefficient differences, on one common low-order state neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n03CoefficientCorrectionJet (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (a b : ℕ) (z : AnnularState S × ℝ) (p : PolarPoint) : ℝ :=
  |mixedDerivative a b (fun q => (L.coefficients z).b q - (originalCoefficients D S C z).b q) p| +
    |mixedDerivative a b (fun q => (L.coefficients z).c q - (originalCoefficients D S C z).c q) p|

private theorem coefficientCorrectionJet_finite_recovery_family
    {Z : Type*} {D : ReferenceData} {V : Set Z}
    {A P : Z → SymmetricCoefficients} {E : Z → Fin 4 → PolarPoint → ℝ}
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (l u : ℝ) (a b : ℕ)
    (hregular : ∀ z ∈ V, ∀ k, CoefficientProbeFieldRegularity D (E z k))
    (haxis : ∀ z ∈ V, ∀ r ∈ Ioo l u,
      (coefficientErrorCrossNumerator χ (E z 0) (E z 1) (E z 2) (r, 0) = 0 ∧
        coefficientErrorCrossNumerator χ (E z 0) (E z 1) (E z 2) (r, Real.pi / 2) = 0) ∧
      (coefficientErrorSquareNumerator χ (E z 1) (E z 3) (r, 0) = 0 ∧
        coefficientErrorSquareNumerator χ (E z 1) (E z 3) (r, Real.pi / 2) = 0))
    (hsame : ∀ z ∈ V, ∀ q ∈ Ioo l u ×ˢ (univ : Set ℝ),
      let Q := coefficientProbeRecoveredCoefficients (A z)
        (coefficientErrorCrossNumerator χ (E z 0) (E z 1) (E z 2))
        (coefficientErrorSquareNumerator χ (E z 1) (E z 3))
      Q.b q = (P z).b q ∧ Q.c q = (P z).c q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ V,
      ∀ p ∈ Ioo l u ×ˢ (univ : Set ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ i j : ℕ, i + j ≤ a + b + 2 → ∀ θ : ℝ, ∀ k : Fin 4,
        |mixedDerivative i j (E z k) (p.1, θ)| ≤ M) →
      |mixedDerivative a b (fun q => (P z).b q - (A z).b q) p| +
        |mixedDerivative a b (fun q => (P z).c q - (A z).c q) p| ≤ B * M := by
  obtain ⟨B, hB0, hrec⟩ := exists_coefficientProbeRecovery_mixed_constant
    hχ (K := Icc l u) isCompact_Icc a b
  refine ⟨B, hB0, ?_⟩
  intro z hz p hp M hM hraw
  let Q := coefficientProbeRecoveredCoefficients (A z)
    (coefficientErrorCrossNumerator χ (E z 0) (E z 1) (E z 2))
    (coefficientErrorSquareNumerator χ (E z 1) (E z 3))
  have he : ∀ᶠ q in 𝓝 p, Q.b q = (P z).b q ∧ Q.c q = (P z).c q := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hsame z hz q hq
  have hbjet := mixedDerivative_eq_of_germ
    (he.mono fun q h => congrArg (fun t : ℝ => t - (A z).b q) h.1) a b
  have hcjet := mixedDerivative_eq_of_germ
    (he.mono fun q h => congrArg (fun t : ℝ => t - (A z).c q) h.2) a b
  rw [← hbjet, ← hcjet]
  exact hrec (D := D) (A z) (E z 0) (E z 1) (E z 2) (E z 3)
    (hregular z hz 0) (hregular z hz 1) (hregular z hz 2) (hregular z hz 3)
    isOpen_Ioo (fun r hr => (haxis z hz r hr).1) (fun r hr => (haxis z hz r hr).2)
    p hp.1 (Ioo_subset_Icc_self hp.1) M hM
    (fun i j hij θ => ⟨hraw i j hij θ 0, hraw i j hij θ 1,
      hraw i j hij θ 2, hraw i j hij θ 3⟩)

private theorem n03CoefficientCorrectionJet_finite_recovery
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (m a b : ℕ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hone : ∀ r ∈ Ioo (C.left m) (C.right m), χ r = 1)
    (η : Fin 4 → HeightPair S)
    (hη : heightPairField S (η 0) = radialLinearProbe χ ∧
      heightPairField S (η 1) = radialCosineProbe χ ∧
      heightPairField S (η 2) = (fun p => radialLinearProbe χ p * radialCosineProbe χ p) ∧
      heightPairField S (η 3) = (fun p => radialCosineProbe χ p * radialCosineProbe χ p)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v ∈ sectorNeighborhood S base ε ε,
      ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ i j : ℕ, i + j ≤ a + b + 2 → ∀ θ : ℝ, ∀ k : Fin 4,
        |mixedDerivative i j (decodedCorrectionError S L (liftSectorParameter S C v)
          (R.residual (liftSectorParameter S C v)) (η k)) (p.1, θ)| ≤ M) →
      n03CoefficientCorrectionJet D S C L a b (liftSectorParameter S C v) p ≤ B * M := by
  let z (v : StateDirections S × ℝ) := liftSectorParameter S C v
  let A (v : StateDirections S × ℝ) := originalCoefficients D S C (z v)
  let P (v : StateDirections S × ℝ) := L.coefficients (z v)
  let E (v : StateDirections S × ℝ) (k : Fin 4) :=
    decodedCorrectionError S L (z v) (R.residual (z v)) (η k)
  have hz (v : StateDirections S × ℝ) (hv : v ∈ sectorNeighborhood S base ε ε) :
      z v ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood hv le_rfl
  have hs (v : StateDirections S × ℝ) : stateSector S (z v).1 :=
    hN01.2.2.1.liftSectorParameter_sector v
  refine coefficientCorrectionJet_finite_recovery_family
    (Z := StateDirections S × ℝ) (D := D) (V := sectorNeighborhood S base ε ε)
    (A := A) (P := P) (E := E) hχ (C.left m) (C.right m) a b ?_ ?_ ?_
  · intro v hv k
    exact decodedCorrectionError_fieldRegularity hT hS L (z v) (R.residual (z v)) (η k)
  · intro v hv r hr
    exact n03CoefficientProbe_axis_values hS hT hN01 hN03 hA hB (hz v hv) (hs v) m
      hχ hone hη.1 hη.2.1 hη.2.2.1 hη.2.2.2 hN02 hr
  · intro v hv q hq
    have hh := n03ProbeRecoveredCoefficients_eq_stored
      hS hT hN01 hN02 hN03 hA hB (hz v hv) (hs v) m hχ hone
      hη.1 hη.2.1 hη.2.2.1 hη.2.2.2 hq
    exact ⟨hh.2.1, hh.2.2⟩

def N03CorrectedCoefficientBoundAtOrder
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base : ℕ) (ε : ℝ)
    (low : ℕ) (δ : ℝ) (loss m a b : ℕ) (B : ℝ) : Prop :=
  ∀ v ∈ sectorNeighborhood S base ε ε,
    pairGrading (sectorGrading S) realGrading low v < δ →
    ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      n03CoefficientCorrectionJet D S C L a b (liftSectorParameter S C v) p ≤
        B * (1 + pairGrading (sectorGrading S) realGrading (a + b + loss) v)

/-- No component-dependent state radius is chosen. The four actual
height probes and each component constant are allowed to depend on the
component, while the low order, radius and loss precede all components. -/
theorem n03_correctedCoefficient_fixed_loss_of_probes
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hone : ∀ m r, r ∈ Ioo (C.left m) (C.right m) → χ m r = 1)
    (η : ℕ → Fin 4 → HeightPair S)
    (hη : ∀ m, heightPairField S (η m 0) = radialLinearProbe (χ m) ∧
      heightPairField S (η m 1) = radialCosineProbe (χ m) ∧
      heightPairField S (η m 2) = (fun p => radialLinearProbe (χ m) p * radialCosineProbe (χ m) p) ∧
      heightPairField S (η m 3) = (fun p => radialCosineProbe (χ m) p * radialCosineProbe (χ m) p)) :
    ∃ outLoss low : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ m a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      N03CorrectedCoefficientBoundAtOrder D S C L base ε low δ outLoss m a b B := by
  have hmaterial := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hmaterial
  obtain ⟨W, hW, hweight, _, _⟩ := henv 1 (3 / 4 : ℝ) (by norm_num)
  have hw : ∀ x ∈ annularOpen D, 0 ≤ T.H x.1 ^ (3 / 4 : ℝ) ∧
      0 ≤ T.M x.1 ∧ T.H x.1 ^ (3 / 4 : ℝ) * T.M x.1 ≤ W := by
    intro x hx
    exact ⟨(Real.rpow_pos_of_pos (hT.2.1 _ hx.1).2.1 _).le,
      zero_le_one.trans (hT.2.1 _ hx.1).2.2.2,
      by simpa only [Real.rpow_one] using hweight x.1 hx.1⟩
  exact fixed_loss_bound_of_finiteProbe_recovery
    (Z := StateDirections S × ℝ) (F := HeightPair S) (I := ℕ) (ι := Fin 4)
    (U := sectorNeighborhood S base ε ε) (Ω := annularOpen D)
    (p := fun n v => pairGrading (sectorGrading S) realGrading n v)
    (t := fun n η => heightPairGrading S n η)
    (jet := fun a b v η x => |mixedDerivative a b (decodedCorrectionError S L
      (liftSectorParameter S C v) (R.residual (liftSectorParameter S C v)) η) x|)
    (value := fun _ a b v x => n03CoefficientCorrectionJet D S C L a b
      (liftSectorParameter S C v) x)
    (H := fun x => T.H x.1 ^ (3 / 4 : ℝ)) (M := fun x => T.M x.1) (η := η)
    (V := fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl))
    (heightPairGrading_monotone S)
    (fun n v => apply_nonneg (pairGrading (sectorGrading S) realGrading n) v)
    (fun n η => apply_nonneg (heightPairGrading S n) η) hW.le hw
    (fun m x hx θ => ⟨⟨(hN01.2.2.2.1.1 m).1.trans hx.1.1,
      hx.1.2.trans (hN01.2.2.2.1.1 m).2.2⟩, mem_univ θ⟩)
    (n03Error_actualResidual_mixed_bound
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (base := base) (ε := ε) hT hS hN01.2.1 hN02 hN03)
    (fun m a b => n03CoefficientCorrectionJet_finite_recovery
      hS hT hN01 hN02 hN03 hA hB m a b (hχ m) (hone m) (η m) (hη m))

end ContinuousFlexibility.Analysis
