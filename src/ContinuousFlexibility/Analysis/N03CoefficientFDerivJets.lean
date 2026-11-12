import ContinuousFlexibility.Analysis.N03TotalCoefficientJets
import ContinuousFlexibility.Analysis.CylinderMixedJets
import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations

/-!
# Ordinary jets of the actual corrected coefficients

The actual mixed jets on a whole negative component determine every
ordinary Fréchet jet. The finite coordinate expansion only contributes
the numerical factor 2^n. It changes neither the state neighborhood nor
the derivative loss of the corrected-coefficient estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N03CoefficientOrdinaryJetBounds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ i : Fin 3, ∀ q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ (canonicalCoefficientComponent i (L.coefficients z)) q ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss B
        (z - (C.referenceState, 0)) (canonicalCoefficientComponent i (L.coefficients z)) q

theorem n03_totalCoefficient_commonNeighborhood_fderiv_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m)) :
    ∃ outLoss base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        N03CoefficientOrdinaryJetBounds S C L base' outLoss ε' m B := by
  obtain ⟨outLoss, base', ε', hbase, hε', hε, hraw⟩ :=
    n03_totalCoefficient_commonNeighborhood_fixed_loss
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
      (base := base) (loss := loss) (ε := ε)
      hS hT hN01 hN02 hN03 hA hB hfield j hcell
  refine ⟨outLoss, base', ε', hbase, hε', hε, ?_⟩
  intro m
  choose A hApos hbound using hraw m
  refine ⟨fun n => (2 : ℝ) ^ n * A n,
    fun n => mul_pos (pow_pos (by norm_num) n) (zero_lt_one.trans_le (hApos n)), ?_⟩
  intro z hz hs i q hq
  have hzold := stateNeighborhood_mono S C hbase hε hz
  have hends := hN01.2.2.2.1.1 m
  have hqAnn : q ∈ annularOpen D :=
    ⟨⟨hends.1.trans hq.1.1, hq.1.2.trans hends.2.2⟩, mem_univ _⟩
  have hregular := hfield.smooth_coefficients z hzold hs
  have hi : ContDiffOn ℝ ∞ (canonicalCoefficientComponent i (L.coefficients z)) (annularOpen D) := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hregular.1
    · exact hregular.2.1
    · exact hregular.2.2
  have hOpen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  refine ⟨hi.contDiffAt (hOpen.mem_nhds hqAnn), ?_⟩
  intro n
  have hn := norm_iteratedFDeriv_le_of_mixedDerivative hOpen hi n hqAnn
    (mul_nonneg (zero_le_one.trans (hApos n))
      (add_nonneg zero_le_one (apply_nonneg _ _)))
    (fun a b hab => by
      simpa only [Real.norm_eq_abs] using hbound n z hz hs i a b hab.le q hq)
  simpa only [mul_assoc] using hn

end ContinuousFlexibility.Analysis
