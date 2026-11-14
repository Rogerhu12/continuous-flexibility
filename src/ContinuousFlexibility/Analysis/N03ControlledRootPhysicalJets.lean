import ContinuousFlexibility.Analysis.N01ControlledRootModel
import ContinuousFlexibility.Analysis.N03UniformRootBandGeometry
import ContinuousFlexibility.Analysis.N03FixedRootOrdinaryJets
import ContinuousFlexibility.Analysis.RootPhysicalJetTransfer

/-!
# Actual stored root fields on a uniform physical collar

The fixed correction cutoff first supplies an uncorrected collar. The
same quantitatively controlled flow determines a smaller collar in the
correct moving half. Its ordinary model jets transfer to the actual
stored chart, height and inverse height at every angle, including the
root. The original scale and flow are retained. All low orders and
losses precede the component, and all collar constants precede states.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def N03RootPhysicalFieldFamily
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base loss : ℕ) (ε : ℝ)
    (m : ℕ) (rightEnd : Bool) (w κJ : ℝ) (B : ℕ → ℝ) : Prop :=
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ x ∈ Icc (0 : ℝ) w, ∀ θ : ℝ,
      let q : PolarPoint := (r + σ * x, θ)
      q ∈ physicalPieceClosed S K z i ∧
        (0 < x → q ∈ physicalPieceOpen S K z i) ∧
        κJ ≤ |planeJacobian (K.chart z i) q| ∧
        RootPhysicalFieldJetBound (pairGrading (stateGrading S) realGrading)
          loss B (z - (C.referenceState, 0)) (K.chart z i) (K.height z i) q

private theorem rootFirstJet_le_twice {A t : ℝ} (hA : 0 ≤ A) (ht : t ≤ 1) :
    A * (1 + t) ≤ 2 * A := by
  have he := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) ht) hA
  nlinarith only [he]

private def RootBandPhysicalGeometry
    (r σ δ ρ : ℝ) (Ω Ωc : Set PolarPoint)
    (F M : PolarPoint → PolarPoint) (H h : PolarPoint → ℝ) : Prop :=
  ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ →
    rootProfileShift r (σ * δ) q ∈ Ωc ∧
      (0 < q.1 → rootProfileShift r (σ * δ) q ∈ Ω) ∧
      ContDiffAt ℝ ∞ F (rootProfileShift r (σ * δ) q) ∧
      ContDiffAt ℝ ∞ H (rootProfileShift r (σ * δ) q) ∧
      0 < H (rootProfileShift r (σ * δ) q) ∧
      (∀ n : ℕ, iteratedFDeriv ℝ n (fun y => F (rootProfileShift r (σ * δ) y)) q =
        iteratedFDeriv ℝ n M q) ∧
      ∀ a : ℝ, ∀ n : ℕ,
        iteratedFDeriv ℝ n (fun y => H (rootProfileShift r (σ * δ) y) ^ a) q =
          iteratedFDeriv ℝ n (fun y => h y ^ a) q

private theorem n03_rootBand_physicalGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} {R δ ρ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρR : δ * ρ ≤ R / 4)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hband : ControlledRootBandChartAgreement C K z m rightEnd δ ρ Θ)
    (hcoeffOn : ∀ x ∈ Ioc (0 : ℝ) ρ, ∀ θ : ℝ,
      let p : PolarPoint := (n01ComponentRoot C m rightEnd +
        n01ComponentRootOrientation rightEnd * (δ * x), θ)
      (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
      (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
      (L.coefficients z).c p = (originalCoefficients D S C z).c p)
    (hG : ContDiff ℝ ∞
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)))
    (hperiod : ∀ x ζ θ,
      rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
          (x, ζ, θ + Real.pi) =
        rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
          (x, ζ, θ) + Real.pi)
    (hvalues : ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ →
      ContDiffAt ℝ ∞ (rootScaledDividedDiscriminant D S C z g
        (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) δ) q ∧
      0 < rootScaledDividedDiscriminant D S C z g
        (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) δ q ∧
      0 < extendedRootOddCoefficient
        (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)) q) :
    RootBandPhysicalGeometry (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) δ ρ
      (physicalPieceOpen S K z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1))
      (physicalPieceClosed S K z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1))
      (K.chart z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1))
      (extendedRootEvenOddChart
        (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)))
      (K.height z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1))
      (rootDividedHeight δ (rootScaledDividedDiscriminant D S C z g
        (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) δ)
        (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ))) := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  dsimp only [RootBandPhysicalGeometry]
  intro q hq
  have hopen (hqp : 0 < q.1) :
      rootProfileShift r (σ * δ) q ∈ physicalPieceOpen S K z i := by
    simpa only [rootProfileShift, mul_assoc] using (hband q.1 ⟨hqp, hq.2⟩ q.2).1
  have hclosed : rootProfileShift r (σ * δ) q ∈ physicalPieceClosed S K z i := by
    by_cases hzero : q.1 = 0
    · simpa only [rootProfileShift, r, i, n01ComponentRoot, hzero, mul_zero, add_zero] using
        (canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m rightEnd q.2).1
    · exact subset_closure (hopen (lt_of_le_of_ne hq.1 (Ne.symm hzero)))
  have hregular := (hA.boundary z hz hs i).2.2.2.2.1
    (rootProfileShift r (σ * δ) q) hclosed
  have hident := n03_fixedRoot_chart_height_ordinaryJets hS hT hN hL hA hB
    hz hs m rightEnd hR hδ hρ hρR hstrip Θ hband hcoeffOn hG hperiod hq
    (hvalues q hq).1 (hvalues q hq).2.1 (hvalues q hq).2.2
  refine ⟨hclosed, hopen, hregular.1, hregular.2.1, hregular.2.2.2, ?_, ?_⟩
  · intro n
    simpa only [rootProfileShift, mul_assoc] using hident.2.2.1 n
  · intro a n
    simpa only [rootProfileShift, mul_assoc] using hident.2.2.2 a n

private theorem rootBandPhysical_fields_of_model
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {B : ℕ → ℝ} {z : E}
    {r σ δ ρ J₀ : ℝ} {Ω Ωc : Set PolarPoint}
    {F : PolarPoint → PolarPoint} {H V : PolarPoint → ℝ}
    {G : ℝ × ℝ × ℝ → ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hδ : 0 < δ) (hB : ∀ n, 0 < B n)
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi)
    (hVperiod : ∀ x θ, V (x, θ + Real.pi) = V (x, θ))
    (hvalues : ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ →
      ContDiffAt ℝ ∞ V q ∧ 0 < V q ∧ 0 < extendedRootOddCoefficient G q ∧
        J₀ ≤ planeJacobian (extendedRootEvenOddChart G) q)
    (hjets : ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ → q.2 ∈ Icc (-Real.pi) Real.pi →
      RootDividedModelJetBound p loss B z δ V G q)
    (hgeometry : RootBandPhysicalGeometry r σ δ ρ Ω Ωc F
      (extendedRootEvenOddChart G) H (rootDividedHeight δ V G)) :
    ∀ x ∈ Icc (0 : ℝ) (δ * ρ), ∀ θ : ℝ,
      (r + σ * x, θ) ∈ Ωc ∧ (0 < x → (r + σ * x, θ) ∈ Ω) ∧
      J₀ / δ ≤ |planeJacobian F (r + σ * x, θ)| ∧
      RootPhysicalFieldJetBound p loss (rootAffineJetEnvelope (σ * δ) B) z
        F H (r + σ * x, θ) := by
  have hσne : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hscaleNe : σ * δ ≠ 0 := mul_ne_zero hσne hδ.ne'
  have hscaleAbs : |σ * δ| = δ := by
    rcases hσ with h | h <;> rw [h] <;> simp only [one_mul, neg_one_mul, abs_neg,
      abs_of_pos hδ]
  intro x hx θ
  let q : PolarPoint := (x / δ, θ)
  have hq : q.1 ∈ Icc (0 : ℝ) ρ :=
    ⟨div_nonneg hx.1 hδ.le,
      (div_le_iff₀ hδ).mpr (by simpa only [mul_comm ρ δ] using hx.2)⟩
  have hpoint : rootProfileShift r (σ * δ) q = (r + σ * x, θ) := by
    ext <;> simp only [q, rootProfileShift] <;> field_simp [hδ.ne'] <;> ring
  have hmodel : RootPhysicalFieldJetBound p loss B z
      (extendedRootEvenOddChart G) (rootDividedHeight δ V G) q :=
    rootDividedModel_jetBound_allAngles hδ hG hperiod hVperiod
      (fun η => ⟨(hvalues (q.1, η) hq).1, (hvalues (q.1, η) hq).2.1,
        (hvalues (q.1, η) hq).2.2.1⟩)
      (fun η hη => hjets (q.1, η) hq hη) q.2
  obtain ⟨hclosed, hopen, hF, hH, hHpos, hFjet, hHjet⟩ := hgeometry q hq
  have htransfer := rootPhysicalFields_of_scaled_jet_model
    (E := E) (p := p) (loss := loss) (B := B) (z := z)
    r (σ * δ) hscaleNe (fun n => (hB n).le)
    hF hH hHpos hmodel hFjet hHjet (hvalues q hq).2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hpoint] using hclosed
  · intro hxp
    simpa only [hpoint] using hopen (div_pos hxp hδ)
  · simpa only [hpoint, hscaleAbs] using htransfer.2
  · simpa only [hpoint] using htransfer.1

private theorem n03_rootBand_fields_of_model_at_state
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss flowLoss outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} {R δ ρ Λ J₀ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρR : δ * ρ ≤ R / 4) {A B : ℕ → ℝ}
    (hApos : ∀ n, 0 < A n) (hBpos : ∀ n, 0 < B n)
    (hsmall : pairGrading (stateGrading S) realGrading (1 + flowLoss)
      (z - (C.referenceState, 0)) ≤ 1)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    (hband : ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ →
      CSBound 1 (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
        (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ))
        (2 * A 1) → ControlledRootBandChartAgreement C K z m rightEnd δ ρ Θ)
    (hcoeffOn : ∀ x ∈ Ioc (0 : ℝ) ρ, ∀ θ : ℝ,
      let p : PolarPoint := (n01ComponentRoot C m rightEnd +
        n01ComponentRootOrientation rightEnd * (δ * x), θ)
      (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
      (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
      (L.coefficients z).c p = (originalCoefficients D S C z).c p)
    (hmodel : N01ControlledRootModelAtState D S C m rightEnd g hR δ ρ Λ J₀
      flowLoss outLoss A B z) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
    ∀ x ∈ Icc (0 : ℝ) (δ * ρ), ∀ θ : ℝ,
      (r + σ * x, θ) ∈ physicalPieceClosed S K z i ∧
      (0 < x → (r + σ * x, θ) ∈ physicalPieceOpen S K z i) ∧
      J₀ / δ ≤ |planeJacobian (K.chart z i) (r + σ * x, θ)| ∧
      RootPhysicalFieldJetBound (pairGrading (stateGrading S) realGrading)
        outLoss (rootAffineJetEnvelope (σ * δ) B) (z - (C.referenceState, 0))
        (K.chart z i) (K.height z i) (r + σ * x, θ) := by
  obtain ⟨_hcontrol, Θ, hΘ, hG, hperiod, hCS, hvalues, hjets⟩ := hmodel
  have hCS1 : CSBound 1
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
      (rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ))
      (2 * A 1) :=
    (hCS 1).mono_bound (rootFirstJet_le_twice (hApos 1).le hsmall)
  have hgeometry := n03_rootBand_physicalGeometry hS hT hN hL hA hB hz hs m rightEnd
    hR hδ hρ hρR hstrip Θ (hband Θ hΘ hCS1) hcoeffOn hG hperiod
    (fun q hq => ⟨(hvalues q hq).1, (hvalues q hq).2.1, (hvalues q hq).2.2.1⟩)
  exact rootBandPhysical_fields_of_model
    (E := AnnularState S × ℝ) (p := pairGrading (stateGrading S) realGrading)
    (loss := outLoss) (B := B) (z := z - (C.referenceState, 0))
    (n01ComponentRootOrientation_eq rightEnd) hδ hBpos hG hperiod
    (rootScaledDividedDiscriminant_period_add hS C z g
      (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd) δ)
    hvalues hjets hgeometry

/-- Every quantity in the conclusion is a field of the existing K.
The supplied flow input is the previously proved actual N01 factory
output; no canonical or inverse-field estimate is assumed. -/
theorem n03_fixedCutoff_controlledRoot_physicalJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hE : N02Properties D T S C E base ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (χ : ℕ → ℝ → ℝ)
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
    (flowLoss : ℕ) :
    ∃ low outLoss : ℕ, outLoss ≤ low ∧
      ∀ m : ℕ, ∀ rightEnd : Bool, ∀ g : ℝ → ℝ,
      ∀ R : ℝ, ∀ hR : 0 < R, ContDiff ℝ ∞ g →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) R) →
      ∀ κ δ Λ : ℝ, 0 < κ → 0 < δ → δ ≤ 1 → δ ≤ R / 4 →
      ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      N01ControlledRootInputFamily D S C base flowLoss ε m rightEnd g hR κ δ Λ A →
      ∃ w κJ : ℝ, ∃ B : ℕ → ℝ,
        0 < w ∧ w < C.right m - C.left m ∧ w ≤ R / 4 ∧
        w / δ ≤ 1 ∧
        0 < κJ ∧ (∀ n, 0 < B n) ∧
        N03FixedRootFlowIdentification D S C L base ε m rightEnd g hR δ (w / δ) ∧
        N03RootPhysicalFieldFamily D S C K (max base low) outLoss
          (min ε (1 / 2 : ℝ)) m rightEnd w κJ B := by
  obtain ⟨lowM, outLoss, hmodel⟩ :=
    n01_controlledRootInput_uniform_model hS hT hN hflow flowLoss
  let low := max lowM (max (1 + flowLoss) outLoss)
  have hflowLow : 1 + flowLoss ≤ low :=
    (le_max_left _ _).trans (le_max_right _ _)
  have houtLow : outLoss ≤ low :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨low, outLoss, houtLow, ?_⟩
  intro m rightEnd g R hR hg hstrip κ δ Λ hκ hδ hδone hδR A hApos hinput
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let i := if rightEnd then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨ηF, hηF, hηFone, hηFwidth, _hηFR, hfixed⟩ :=
    n03_exists_fixed_rootFlow_identification hS hT hN hL χ hend hcoeff
      m rightEnd hg hR hδ hδR hstrip
  obtain ⟨ηG, hηG, hηGF, hgeometry⟩ := n03_exists_uniform_rootBand_geometry
    hS hT hN hE hL hA hB m rightEnd hg hR hδ hηF hηFone.le hηFwidth
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hApos 1).le) hstrip hfixed
  obtain ⟨ρC, hρC, _hρCδ, _hρCwidth, _hcut, hcoeffBand⟩ :=
    n01_exists_fixedCutoff_root_collar hN χ hend m rightEnd hδ
  let η := min ηG (ρC / δ)
  have hη : 0 < η := lt_min hηG (div_pos hρC hδ)
  have hηone : η ≤ 1 := (min_le_left _ _).trans (hηGF.trans hηFone.le)
  obtain ⟨ρ, J₀, B, hρ, hρη, hρR, hJ₀, hBpos, hmodels⟩ :=
    hmodel m rightEnd g R hR hg hstrip κ δ Λ η hκ hδ hδone hη hηone A hApos hinput
  have hρG : ρ ≤ ηG := hρη.trans (min_le_left _ _)
  have hρCscale : δ * ρ ≤ ρC := by
    have he := (le_div_iff₀ hδ).mp (hρη.trans (min_le_right _ _))
    simpa only [mul_comm ρ δ] using he
  let w := δ * ρ
  let κJ := J₀ / δ
  let Bout := rootAffineJetEnvelope (σ * δ) B
  have hwδ : w / δ = ρ := by
    dsimp only [w]
    field_simp [hδ.ne']
  have hwδone : w / δ ≤ 1 := by
    rw [hwδ]
    exact hρη.trans hηone
  have hfixedW : N03FixedRootFlowIdentification D S C L base ε
      m rightEnd g hR δ (w / δ) := by
    intro z hz hs Θ hΘ
    dsimp only [RootStoredFlowAgreementOn]
    intro ι x hx
    exact hfixed z hz hs Θ hΘ ι x
      ⟨hx.1, hx.2.trans (by simpa only [hwδ] using hρG.trans hηGF)⟩
  have hw : 0 < w := mul_pos hδ hρ
  have hwwidth : w < C.right m - C.left m :=
    (mul_le_mul_of_nonneg_left (hρG.trans hηGF) hδ.le).trans_lt hηFwidth
  refine ⟨w, κJ, Bout, hw, hwwidth, hρR, hwδone, div_pos hJ₀ hδ,
    rootAffineJetEnvelope_pos hBpos (σ * δ), hfixedW, ?_⟩
  dsimp only [N03RootPhysicalFieldFamily]
  intro z hz hs
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz
  have hzmodel : z ∈ stateNeighborhood S C (max base lowM) (min ε (1 / 2 : ℝ)) :=
    stateNeighborhood_mono S C (max_le_max le_rfl (le_max_left _ _)) le_rfl hz
  have hzsmall : z ∈ stateNeighborhood S C (1 + flowLoss) (min ε (1 / 2 : ℝ)) :=
    stateNeighborhood_mono S C (hflowLow.trans (le_max_right _ _)) le_rfl hz
  have hsmall : pairGrading (stateGrading S) realGrading (1 + flowLoss)
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzsmall).trans (by
      have he : min ε (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hcoeffOn (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) ρ) (θ : ℝ) :
      let p : PolarPoint := (r + σ * (δ * x), θ)
      (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
      (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
      (L.coefficients z).c p = (originalCoefficients D S C z).c p := by
    let p : PolarPoint := (r + σ * (δ * x), θ)
    have he := hcoeffBand z θ (δ * x)
      ⟨(mul_pos hδ hx.1).le, (mul_le_mul_of_nonneg_left hx.2 hδ.le).trans hρCscale⟩
    exact ⟨(congrArg (fun F => (F z).a p) hcoeff).trans he.1,
      (congrArg (fun F => (F z).b p) hcoeff).trans he.2.1,
      (congrArg (fun F => (F z).c p) hcoeff).trans he.2.2⟩
  exact n03_rootBand_fields_of_model_at_state hS hT hN hL hA hB hzold hs m rightEnd
    hR hδ hρ hρR hApos hBpos hsmall (hstrip z hzold hs)
    (fun Θ hΘ hCS1 x hx θ =>
      hgeometry z hzold hs Θ hΘ hCS1 x ⟨hx.1, hx.2.trans hρG⟩ θ)
    hcoeffOn (hmodels z hzmodel hs)

end ContinuousFlexibility.Analysis
