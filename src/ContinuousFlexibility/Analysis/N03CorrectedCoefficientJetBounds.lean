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
  obtain ⟨B, hB0, hrec⟩ := exists_coefficientProbeRecovery_mixed_constant
    hχ (K := Icc (C.left m) (C.right m)) isCompact_Icc a b
  refine ⟨B, hB0, ?_⟩
  intro v hv p hp M hM hraw
  let z := liftSectorParameter S C v
  have hz : z ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood hv le_rfl
  have hs : stateSector S z.1 := hN01.2.2.1.liftSectorParameter_sector v
  let A := originalCoefficients D S C z
  let Bfield := n03ProbeRecoveredCoefficients D S C R L χ (η 0) (η 1) (η 2) (η 3) z
  have he : ∀ᶠ q in 𝓝 p, Bfield.b q = (L.coefficients z).b q ∧
      Bfield.c q = (L.coefficients z).c q := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have hh := n03ProbeRecoveredCoefficients_eq_stored
      hS hT hN01 hN02 hN03 hA hB hz hs m hχ hone hη.1 hη.2.1 hη.2.2.1 hη.2.2.2 hq
    exact ⟨hh.2.1, hh.2.2⟩
  have hbjet := mixedDerivative_eq_of_germ
    (he.mono fun q h => congrArg (fun t : ℝ => t - A.b q) h.1) a b
  have hcjet := mixedDerivative_eq_of_germ
    (he.mono fun q h => congrArg (fun t : ℝ => t - A.c q) h.2) a b
  have hzaxis (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :=
    n03CoefficientProbe_axis_values hS hT hN01 hN03 hA hB hz hs m hχ hone
      hη.1 hη.2.1 hη.2.2.1 hη.2.2.2 hN02 hr
  change |mixedDerivative a b (fun q => (L.coefficients z).b q - A.b q) p| +
    |mixedDerivative a b (fun q => (L.coefficients z).c q - A.c q) p| ≤ B * M
  rw [← hbjet, ← hcjet]
  exact hrec (D := D) A
    (decodedCorrectionError S L z (R.residual z) (η 0))
    (decodedCorrectionError S L z (R.residual z) (η 1))
    (decodedCorrectionError S L z (R.residual z) (η 2))
    (decodedCorrectionError S L z (R.residual z) (η 3))
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) (η 0))
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) (η 1))
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) (η 2))
    (decodedCorrectionError_fieldRegularity hT hS L z (R.residual z) (η 3))
    isOpen_Ioo (fun r hr => (hzaxis r hr).1) (fun r hr => (hzaxis r hr).2)
    p hp.1 (Ioo_subset_Icc_self hp.1) M hM
    (fun i j hij θ => ⟨hraw i j hij θ 0, hraw i j hij θ 1,
      hraw i j hij θ 2, hraw i j hij θ 3⟩)

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
