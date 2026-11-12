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

private def InteriorFirstIntegralInputs
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (rootLoss flowLoss : ℕ) (A F : ℕ → ℝ)
    (z : E) (a b Γ x : ℝ) (U : Bool → PolarPoint → ℝ) : Prop :=
  ∃ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G ∧
    (∀ r ζ θ, G (r, ζ, θ + Real.pi) = G (r, ζ, θ) + Real.pi) ∧
    (∀ s : ℕ, CSBound s
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G
        (A s * (1 + p (s + rootLoss) z))) ∧
    ∀ plus : Bool, ∃ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowJetBounds p flowLoss F z 1 Γ Ψ ∧
      EqOn (U plus) (fun y => rootCircleSample G x
        ((if plus then 1 else -1) * x ^ (3 / 2 : ℝ))
          (interiorEndpointPullback Ψ a b y)) (Ioo a b ×ˢ (univ : Set ℝ))

private theorem interiorFirstIntegral_family_propagation
    {E : Type} [AddCommGroup E] [Module ℝ E] {Z : Type*}
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (rootLoss flowLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A F : ℕ → ℝ,
      (∀ n, 0 < A n) → (∀ n, 0 < F n) →
      ∀ a b : ℝ, a < b → ∀ Γ x : ℝ, x ∈ Icc (0 : ℝ) 1 →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        ∀ shift : Z → E, ∀ V : Set Z, ∀ U : Z → Bool → PolarPoint → ℝ,
          (∀ z ∈ V, p low (shift z) ≤ 1) →
          (∀ z ∈ V, InteriorFirstIntegralInputs p rootLoss flowLoss A F
            (shift z) a b Γ x (U z)) →
          ∀ z ∈ V, ∀ plus : Bool, ∀ q : PolarPoint, q.1 ∈ Ioo a b →
            ContDiffAt ℝ ∞ (U z plus) q ∧
              PointwiseMaterialJetBound p outLoss B (shift z)
                (fun y => U z plus y - y.2) q := by
  obtain ⟨low, outLoss, hpropagate⟩ :=
    interiorRootLabel_fixed_loss_bound hp hI rootLoss flowLoss
  refine ⟨low, outLoss, ?_⟩
  intro A F hA hF a b hab Γ x hx
  obtain ⟨B, hB, hbound⟩ := hpropagate A F hA hF a b hab
  refine ⟨B, hB, ?_⟩
  intro shift V U hlow hinput z hz plus q hq
  obtain ⟨G, hG, hperiod, hrootjets, hflows⟩ := hinput z hz
  obtain ⟨Ψ, hΨjets, he⟩ := hflows plus
  let ζ : ℝ := (if plus then 1 else -1) * x ^ (3 / 2 : ℝ)
  have hpow : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.1 _
  have hpowone : x ^ (3 / 2 : ℝ) ≤ 1 :=
    (Real.rpow_le_self_of_le_one hx.1 hx.2 (by norm_num)).trans hx.2
  have hζ : ζ ∈ Icc (-1 : ℝ) 1 := by
    cases plus <;> simp only [ζ, Bool.false_eq_true, ↓reduceIte, neg_one_mul, one_mul]
    · exact ⟨neg_le_neg hpowone, (neg_nonpos.mpr hpow).trans zero_le_one⟩
    · exact ⟨(by linarith only [hpow]), hpowone⟩
  exact hbound (shift z) (hlow z hz) G hG hperiod hrootjets Γ Ψ hΨjets
    x hx ζ hζ (U z plus) (Ioo a b ×ˢ (univ : Set ℝ))
    (isOpen_Ioo.prod isOpen_univ) (fun y hy => Ioo_subset_Icc_self hy.1)
    he q ⟨hq, mem_univ _⟩

private theorem n03_interiorFirstIntegral_actual_inputs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss rootLoss flowLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hE : N02Properties D T S C E base ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {R κ δ Λ η x b ρ Γ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hx : x ∈ Ioc (0 : ℝ) η) (hab : C.left m + δ * x < b)
    (hb : b < C.right m) (hρ : 0 < ρ) {A F : ℕ → ℝ}
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (C.left m) 1 R)
    (hinput : N01ControlledRootInputAtState D S C m false g hR κ δ Λ rootLoss A z)
    (hfixed : N03FixedRootFlowIdentification D S C L base ε m false g hR δ η)
    (hflows : ∀ plus : Bool, ∃ Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      InteriorFlowPairBounds (pairGrading (stateGrading S) realGrading) flowLoss F
        (z - (C.referenceState, 0)) Γ (C.left m + δ * x) b
        (interiorLocalizedSpeed hab.le hρ
          (negativeCharacteristicField plus (L.coefficients z))) Θ Ψ) :
    InteriorFirstIntegralInputs (pairGrading (stateGrading S) realGrading)
      rootLoss flowLoss A F (z - (C.referenceState, 0))
      (C.left m + δ * x) b Γ x
      (fun plus => canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)) := by
  let a := C.left m + δ * x
  have ha : C.left m < a := lt_add_of_pos_right _ (mul_pos hδ hx.1)
  have hax : a ∈ Ioo (C.left m) (C.right m) := ⟨ha, hab.trans hb⟩
  obtain ⟨_hcontrol, Θ₀, hΘ₀, hG, hperiod, _hzero, _hlower, hrootjets⟩ := hinput
  let G := rootScaledInverseCoordinate Θ₀ (n01RootLabel S C z m false) (Real.sqrt δ)
  have hmatch := hfixed z hz hs Θ₀ hΘ₀
  refine ⟨G, hG, hperiod, hrootjets, ?_⟩
  intro plus
  obtain ⟨Θ, Ψ, hΘ, _hΨeq, hinverse, _hΘjets, hΨjets⟩ := hflows plus
  refine ⟨Ψ, hΨjets, ?_⟩
  intro y hy
  have htransport := canonicalGluedAiryIntegral_eq_interiorFlowInverse
    hS hT hN hE hL hA hB hz hs m ha hab hb hρ plus hΘ
    (fun v θ => (hinverse v θ).1) (Ioo_subset_Icc_self hy.1) y.2
  have hsection := n03_leftRoot_firstIntegrals_eq_controlled_samples
    hS hT hN hE hL hA hB hz hs m hg hR hstrip hΘ₀ hmatch hx hax
    (interiorEndpointPullback Ψ a b y)
  cases plus with
  | false =>
      exact htransport.trans (by
        simpa only [G, Bool.false_eq_true, ↓reduceIte, neg_one_mul] using hsection.1)
  | true =>
      exact htransport.trans (by simpa only [G, ↓reduceIte, one_mul] using hsection.2)

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
  obtain ⟨low, outLoss, hpropagate⟩ :=
    interiorFirstIntegral_family_propagation (Z := AnnularState S × ℝ)
      p hp hI rootLoss flowLoss
  refine ⟨low, outLoss, ?_⟩
  intro m g hg R hR κ δ Λ η x b ρ Γ hδ hη hx hab hb hρ A F hApos hFpos
    flowBase εFlow hbase hε hstrip hinput hfixed hflows
  let a := C.left m + δ * x
  have hxone : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hη⟩
  obtain ⟨B, hBpos, hbound⟩ := hpropagate A F hApos hFpos a b hab Γ x hxone
  let V : Set (AnnularState S × ℝ) :=
    {z | z ∈ stateNeighborhood S C (max flowBase low) (min εFlow (1 / 2 : ℝ)) ∧
      stateSector S z.1}
  have hzflow (z : AnnularState S × ℝ) (hz : z ∈ V) :
      z ∈ stateNeighborhood S C flowBase εFlow :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz.1
  have hzold (z : AnnularState S × ℝ) (hz : z ∈ V) :
      z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hbase hε (hzflow z hz)
  have hlow (z : AnnularState S × ℝ) (hz : z ∈ V) :
      p low (z - (C.referenceState, 0)) ≤ 1 := by
    have hzlow : z ∈ stateNeighborhood S C low (min εFlow (1 / 2 : ℝ)) :=
      stateNeighborhood_mono S C (le_max_right _ _) le_rfl hz.1
    exact (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have he : min εFlow (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hdata (z : AnnularState S × ℝ) (hz : z ∈ V) :
      InteriorFirstIntegralInputs p rootLoss flowLoss A F
        (z - (C.referenceState, 0)) a b Γ x
        (fun plus => canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)) :=
    n03_interiorFirstIntegral_actual_inputs hS hT hN hE hL hA hB
      (hzold z hz) hz.2 m hg hR hδ hx hab hb hρ (hstrip z (hzold z hz) hz.2)
      (hinput z (hzold z hz) hz.2) hfixed (hflows hab.le z (hzflow z hz) hz.2)
  refine ⟨B, hBpos, ?_⟩
  intro z hz hs
  exact hbound (fun z => z - (C.referenceState, 0)) V
    (fun z plus => canonicalGluedAiryIntegral S K z m (if plus then -1 else 1))
    hlow hdata z ⟨hz, hs⟩

end ContinuousFlexibility.Analysis
