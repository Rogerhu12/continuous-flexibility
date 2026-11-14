module

public import ContinuousFlexibility.Analysis.N03NegativeInteriorJets
public import ContinuousFlexibility.Analysis.InteriorSpeedLocalization
public import ContinuousFlexibility.Analysis.N04bActualCharacteristics

/-!
# Quantified actual flows on every fixed negative interior

A radial clamp is fixed before the state and preserves the original
speed on a neighborhood of the whole visited interval. Both signs have
actual forward and inverse flows, with one common state neighborhood
and derivative loss. Every spatial estimate follows from the actual
corrected coefficients; no flow derivative tower is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N03NegativeInteriorFlowBounds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε a b ρ Λ : ℝ)
    (hab : a ≤ b) (hρ : 0 < ρ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ plus : Bool, ∃ Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      InteriorFlowPairBounds (pairGrading (stateGrading S) realGrading) loss B
        (z - (C.referenceState, 0)) Λ a b
        (interiorLocalizedSpeed hab hρ (negativeCharacteristicField plus (L.coefficients z)))
        Θ Ψ

theorem n03_negativeInteriorFlows_commonNeighborhood_fixed_loss
    (hFlow : N04FlowJetsTarget)
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
      ∀ m : ℕ, ∀ a b : ℝ, C.left m < a → a ≤ b → b < C.right m →
        ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
          C.left m < a - 2 * ρ ∧ b + 2 * ρ < C.right m ∧
        ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
          ∀ hab : a ≤ b, N03NegativeInteriorFlowBounds S C L newBase outLoss ε'
            a b ρ Λ hab hρ B := by
  obtain ⟨speedBase, speedLoss, η, hb, hη, hηε, hspeed⟩ :=
    n03_negativeCharacteristic_commonNeighborhood_fixed_loss
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
      (base := base) (loss := loss) (ε := ε)
      hS hT hN01 hN02 hN03 hA hB hfield χ hcoeff hgap j hcell
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hfactory⟩ :=
    exists_interiorScalarFlowPair_fixed_loss hFlow p hp hI speedLoss
  let newBase := max speedBase low
  let ε' : ℝ := min η (1 / 2)
  have hε' : 0 < ε' := lt_min hη (by norm_num)
  have hsmall : ε' ≤ η := min_le_left _ _
  have hhalf : ε' ≤ 1 / 2 := min_le_right _ _
  have hU : stateNeighborhood S C newBase ε' ⊆ stateNeighborhood S C speedBase η :=
    stateNeighborhood_mono S C (le_max_left _ _) hsmall
  have hUold : stateNeighborhood S C newBase ε' ⊆ stateNeighborhood S C base ε :=
    hU.trans (stateNeighborhood_mono S C hb hηε)
  have hlow (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C newBase ε') :
      p low (z - (C.referenceState, 0)) ≤ 1 := by
    have hz' := stateNeighborhood_mono S C (le_max_right speedBase low) le_rfl hz
    exact (pairGrading_displacement_le_two_mul_radius hz').trans (by linarith)
  refine ⟨newBase, outLoss, ε', hb.trans (le_max_left _ _), hε', hsmall.trans hηε, ?_⟩
  intro m a b ha hab hb'
  let ρ : ℝ := min ((a - C.left m) / 4) ((C.right m - b) / 4)
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρa : ρ ≤ (a - C.left m) / 4 := min_le_left _ _
  have hρb : ρ ≤ (C.right m - b) / 4 := min_le_right _ _
  have hlo : C.left m < a - 2 * ρ := by linarith
  have hhi : b + 2 * ρ < C.right m := by linarith
  have hJN : Icc a b ⊆ Ioo (C.left m) (C.right m) :=
    fun r hr => ⟨ha.trans_le hr.1, hr.2.trans_lt hb'⟩
  obtain ⟨A, hApos, hjet⟩ := hspeed m (Icc a b) isCompact_Icc hJN
  let A' : ℕ → ℝ := fun n => 1 + A n
  have hA' (n : ℕ) : 1 ≤ A' n := le_add_of_nonneg_right (hApos n).le
  obtain ⟨Λ, hΛ, B, hBpos, hflows⟩ := hfactory A' hA' a b hab
  refine ⟨ρ, hρ, hlo, hhi, Λ, hΛ, B, hBpos, ?_⟩
  intro hab' z hz hs plus
  let f := negativeCharacteristicField plus (L.coefficients z)
  have houter : Ioo (a - 2 * ρ) (b + 2 * ρ) ⊆ Ioo (C.left m) (C.right m) :=
    fun r hr => ⟨hlo.trans hr.1, hr.2.trans hhi⟩
  have h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε :=
    ⟨⟨hN01, hN02⟩, hN03⟩
  have hf : ContDiffOn ℝ ∞ f
      (Ioo (a - 2 * ρ) (b + 2 * ρ) ×ˢ (univ : Set ℝ)) := by
    intro q hq
    have hh := n04b_corrected_characteristics_contDiffAt h03 hfield (hUold hz) hs m
      ⟨houter hq.1, mem_univ _⟩
    cases plus with
    | false => exact hh.2.2.1.contDiffWithinAt
    | true => exact hh.2.2.2.contDiffWithinAt
  have hper : ∀ r ∈ Ioo (a - 2 * ρ) (b + 2 * ρ),
      Function.Periodic (fun θ => f (r, θ)) Real.pi := by
    intro r hr
    have hn := houter hr
    have hend := hN01.2.2.2.1.1 m
    have hh := hfield.periodic_coefficients z (hUold hz) hs r
      ⟨hend.1.trans hn.1, hn.2.trans hend.2.2⟩
    have hdv := n04b_characteristic_periodic (L.coefficients z) r Real.pi hh.1 hh.2.1 hh.2.2
    cases plus with
    | false => exact hdv.1.sub hdv.2
    | true => exact hdv.1.add hdv.2
  have hraw : InteriorSpeedJetBounds p speedLoss A' (z - (C.referenceState, 0)) a b f := by
    intro n r hr θ
    exact ((hjet z (hU hz) hs (r, θ) hr).1 plus n).trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one)
        (add_nonneg zero_le_one (apply_nonneg _ _)))
  exact hflows (z - (C.referenceState, 0)) (hlow z hz)
    (interiorLocalizedSpeed hab' hρ f)
    (contDiff_interiorLocalizedSpeed hab' hρ hf)
    (interiorLocalizedSpeed_periodic hab' hρ hper)
    (interiorLocalizedSpeed_jetBounds hab' hρ hraw)

end ContinuousFlexibility.Analysis
