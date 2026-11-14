module

public import ContinuousFlexibility.Analysis.N03TotalCoefficientJets
public import ContinuousFlexibility.Analysis.N03NegativeInteriorValues
public import ContinuousFlexibility.Analysis.NegativeCharacteristicMaterialJets
public import ContinuousFlexibility.Analysis.CanonicalStateInterpolation
public import ContinuousFlexibility.Analysis.CanonicalVariationBounds

/-!
# Actual characteristic jets on every fixed compact negative interior

The genuine corrected coefficient bounds and reference denominators
feed the scalar characteristic functions. One low state ball controls
the order-zero coefficient values. The same neighborhood and derivative
loss then work for every component, every fixed compact interior, every
spatial order, and both characteristic signs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N03NegativeInteriorJetBounds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ)
    (J : Set ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ q : PolarPoint, q.1 ∈ J →
      (∀ plus : Bool, ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n (negativeCharacteristicField plus (L.coefficients z)) q‖ ≤
          B n * (1 + pairGrading (stateGrading S) realGrading (n + loss)
            (z - (C.referenceState, 0)))) ∧
      ∀ plus : Bool, ∀ a b : ℕ,
        |mixedDerivative a b (negativeCharacteristicField plus (L.coefficients z)) q| ≤
          B (a + b) * (1 + pairGrading (stateGrading S) realGrading (a + b + loss)
            (z - (C.referenceState, 0)))

/-- Every order is estimated on the actual stored field. Compact
reference lower bounds and all numerical sequences are chosen before
the state; no prospective flow derivative is assumed. -/
theorem n03_negativeCharacteristic_commonNeighborhood_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (χ : ℕ → ℝ → ℝ)
    (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
    (hgap : N04ReturnReferenceDiscriminantBound D S C χ base ε)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m)) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∀ J : Set ℝ, IsCompact J → J ⊆ Ioo (C.left m) (C.right m) →
        ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
          N03NegativeInteriorJetBounds S C L newBase outLoss ε' J B := by
  obtain ⟨rawLoss, rawBase, η, hb, hη, hηε, hraw⟩ :=
    n03_totalCoefficient_commonNeighborhood_fixed_loss
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
      (base := base) (loss := loss) (ε := ε)
      hS hT hN01 hN02 hN03 hA hB hfield j hcell
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hspeed⟩ := negativeCharacteristic_fixed_loss_bound hp hI rawLoss
  let newBase := max rawBase low
  let ε' : ℝ := min η (1 / 2)
  have hε' : 0 < ε' := lt_min hη (by norm_num)
  have hsmall : ε' ≤ η := min_le_left _ _
  have hhalf : ε' ≤ 1 / 2 := min_le_right _ _
  have hU : stateNeighborhood S C newBase ε' ⊆ stateNeighborhood S C rawBase η :=
    stateNeighborhood_mono S C (le_max_left _ _) hsmall
  have hUold : stateNeighborhood S C newBase ε' ⊆ stateNeighborhood S C base ε :=
    hU.trans (stateNeighborhood_mono S C hb hηε)
  have hlow (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C newBase ε') :
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 := by
    have hz' := stateNeighborhood_mono S C (le_max_right rawBase low) le_rfl hz
    exact (pairGrading_displacement_le_two_mul_radius hz').trans (by linarith)
  refine ⟨newBase, outLoss, ε', hb.trans (le_max_left _ _), hε', hsmall.trans hηε, ?_⟩
  intro m J hJ hJN
  obtain ⟨l, κ, hl, hκ, hvalues⟩ := n03_exists_negativeInterior_value_bounds
    hN01 hN03 χ hcoeff hgap m hJ hJN
  choose A hA hAbound using hraw m
  obtain ⟨B, hB, hcontrol⟩ := hspeed l κ hl hκ A hA
  refine ⟨B, hB, ?_⟩
  intro z hz hs q hq
  have hqN : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨hJN hq, mem_univ _⟩
  have hends := hN01.2.2.2.1.1 m
  have hqAnn : q ∈ annularOpen D :=
    ⟨⟨hends.1.trans hqN.1.1, hqN.1.2.trans hends.2.2⟩, mem_univ _⟩
  have hC : ∀ i : Fin 3,
      ContDiffOn ℝ ∞ (canonicalCoefficientComponent i (L.coefficients z)) (annularOpen D) := by
    intro i
    have hh := hfield.smooth_coefficients z (hUold hz) hs
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  have hden := hvalues z (hUold hz) hs q hq
  exact hcontrol (z - (C.referenceState, 0)) (hlow z hz)
    (annularOpen D) (isOpen_Ioo.prod isOpen_univ) (L.coefficients z) hC
    q hqAnn hden.1 hden.2
    (fun n i a b hab => hAbound n z (hU hz) hs i a b hab.le q hqN)

end ContinuousFlexibility.Analysis
