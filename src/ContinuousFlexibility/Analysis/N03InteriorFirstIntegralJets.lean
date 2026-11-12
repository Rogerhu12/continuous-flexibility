import ContinuousFlexibility.Analysis.N03LeftRootSectionIdentification
import ContinuousFlexibility.Analysis.N03InteriorFirstIntegralIdentification
import ContinuousFlexibility.Analysis.InteriorRootLabelMaterialJets
import ContinuousFlexibility.Analysis.N01ControlledRootInput

/-!
# Actual all-order first-integral jets from the controlled root section

The same controlled root input supplies the two section labels. The
already constructed actual interior inverse flows transport them to
every interior point. One low order and derivative loss are fixed
before the component, section, interval, or numerical constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N03InteriorFirstIntegralMaterialBounds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (a b : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ plus : Bool, ∀ q : PolarPoint, q.1 ∈ Ioo a b →
      ContDiffAt ℝ ∞ (canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)) q ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss B
        (z - (C.referenceState, 0))
        (fun y => canonicalGluedAiryIntegral S K z m (if plus then -1 else 1) y - y.2) q

theorem n03_interiorFirstIntegral_material_propagation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hE : N02Properties D T S C E base ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (rootLoss flowLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ m : ℕ, ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
      ∀ R : ℝ, ∀ hR : 0 < R, ∀ κ δ Λ η x b ρ Γ : ℝ,
        0 < δ → η ≤ 1 → x ∈ Ioc (0 : ℝ) η →
        C.left m + δ * x < b → b < C.right m → ∀ hρ : 0 < ρ,
      ∀ A F : ℕ → ℝ, (∀ n, 0 < A n) → (∀ n, 0 < F n) →
      ∀ flowBase : ℕ, ∀ εFlow : ℝ, base ≤ flowBase → εFlow ≤ ε →
        (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
          RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) (C.left m) 1 R) →
        N01ControlledRootInputFamily D S C base rootLoss ε m false g hR κ δ Λ A →
        N03FixedRootFlowIdentification D S C L base ε m false g hR δ η →
        (∀ hab : C.left m + δ * x ≤ b,
          N03NegativeInteriorFlowBounds S C L flowBase flowLoss εFlow
            (C.left m + δ * x) b ρ Γ hab hρ F) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        N03InteriorFirstIntegralMaterialBounds S C K (max flowBase low) outLoss
          (min εFlow (1 / 2 : ℝ)) m (C.left m + δ * x) b B := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hpropagate⟩ := interiorRootLabel_fixed_loss_bound hp hI rootLoss flowLoss
  refine ⟨low, outLoss, ?_⟩
  intro m g hg R hR κ δ Λ η x b ρ Γ hδ hη hx hab hb hρ A F hApos hFpos
    flowBase εFlow hbase hε hstrip hinput hfixed hflows
  let a := C.left m + δ * x
  have ha : C.left m < a := lt_add_of_pos_right _ (mul_pos hδ hx.1)
  have hax : a ∈ Ioo (C.left m) (C.right m) := ⟨ha, hab.trans hb⟩
  have hxone : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hη⟩
  obtain ⟨B, hBpos, hbound⟩ := hpropagate A F hApos hFpos a b hab
  refine ⟨B, hBpos, ?_⟩
  intro z hz hs plus q hq
  have hzflow : z ∈ stateNeighborhood S C flowBase εFlow :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hbase hε hzflow
  have hzlow : z ∈ stateNeighborhood S C low (min εFlow (1 / 2 : ℝ)) :=
    stateNeighborhood_mono S C (le_max_right _ _) le_rfl hz
  have hlow : p low (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have he : min εFlow (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  obtain ⟨_hcontrol, Θ₀, hΘ₀, hG, hperiod, _hzero, _hlower, hrootjets⟩ :=
    hinput z hzold hs
  let G := rootScaledInverseCoordinate Θ₀ (n01RootLabel S C z m false) (Real.sqrt δ)
  have hmatch := hfixed z hzold hs Θ₀ hΘ₀
  obtain ⟨Θ, Ψ, hΘ, _hΨeq, hinverse, _hΘjets, hΨjets⟩ :=
    hflows hab.le z hzflow hs plus
  let ζ : ℝ := (if plus then 1 else -1) * x ^ (3 / 2 : ℝ)
  have hpow : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.1.le _
  have hpowone : x ^ (3 / 2 : ℝ) ≤ 1 :=
    (Real.rpow_le_self_of_le_one hxone.1 hxone.2 (by norm_num)).trans hxone.2
  have hζ : ζ ∈ Icc (-1 : ℝ) 1 := by
    cases plus <;> simp only [ζ, Bool.false_eq_true, ↓reduceIte, neg_one_mul, one_mul]
    · exact ⟨neg_le_neg hpowone, (neg_nonpos.mpr hpow).trans zero_le_one⟩
    · exact ⟨(by linarith only [hpow]), hpowone⟩
  let U := canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)
  have he : EqOn U (fun y => rootCircleSample G x ζ
      (interiorEndpointPullback Ψ a b y)) (Ioo a b ×ˢ (univ : Set ℝ)) := by
    intro y hy
    have htransport := canonicalGluedAiryIntegral_eq_interiorFlowInverse
      hS hT hN hE hL hA hB hzold hs m ha hab hb hρ plus hΘ
      (fun v θ => (hinverse v θ).1) (Ioo_subset_Icc_self hy.1) y.2
    have hsection := n03_leftRoot_firstIntegrals_eq_controlled_samples
      hS hT hN hE hL hA hB hzold hs m hg hR (hstrip z hzold hs)
      hΘ₀ hmatch hx hax (interiorEndpointPullback Ψ a b y)
    cases plus with
    | false =>
        exact htransport.trans (by
          simpa only [G, ζ, Bool.false_eq_true, ↓reduceIte, neg_one_mul] using hsection.1)
    | true =>
        exact htransport.trans (by simpa only [G, ζ, ↓reduceIte, one_mul] using hsection.2)
  exact hbound (z - (C.referenceState, 0)) hlow G hG hperiod hrootjets Γ Ψ hΨjets
    x hxone ζ hζ U (Ioo a b ×ˢ (univ : Set ℝ)) (isOpen_Ioo.prod isOpen_univ)
    (fun y hy => Ioo_subset_Icc_self hy.1) he q ⟨hq, mem_univ _⟩

end ContinuousFlexibility.Analysis
