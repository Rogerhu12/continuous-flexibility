import ContinuousFlexibility.Analysis.N03ControlledRootUnitIdentification
import ContinuousFlexibility.Analysis.N01RootChartAxisMaterialJets
import ContinuousFlexibility.Analysis.N01RootDividedHeightMaterialJets
import ContinuousFlexibility.Analysis.RootUnitPhysicalJetTransfer
import ContinuousFlexibility.Analysis.N04FlowJetsProof

/-!
# Material root jets of the original stored negative atlas

The existing N01 factory is chosen on one smaller common neighborhood,
with the original D/T/S/C/E/L/K retained. Its chosen scales and first-jet
constants only establish the actual N03 identification band. Unit-model
material jets pass through that identity and the inward orientation of
norm one. The explicit optical lower condition is still required on the
same component and actual containing cell.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem physicalRoot_two_material_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {a b V W : ℝ} {n l m : ℕ} (ha : 0 ≤ a) (hab : 2 * a ≤ b)
    (hV : 1 ≤ V) (hVW : V ≤ W) (hlm : l ≤ m) (z : E) :
    2 * (a * V ^ a) * (1 + p (n + l) z) ≤
      b * W ^ b * (1 + p (n + m) z) := by
  have hab' : a ≤ b := by linarith only [ha, hab]
  have hb : 0 ≤ b := ha.trans hab'
  have hW : 1 ≤ W := hV.trans hVW
  have hpower : V ^ a ≤ W ^ b :=
    (Real.rpow_le_rpow (zero_le_one.trans hV) hVW ha).trans
      (Real.rpow_le_rpow_of_exponent_le hW hab')
  calc
    _ = (2 * a) * V ^ a * (1 + p (n + l) z) := by ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul hab hpower (Real.rpow_nonneg (zero_le_one.trans hV) _) hb)
      (add_le_add le_rfl (hp (Nat.add_le_add_left hlm n) z))
      (add_nonneg zero_le_one (apply_nonneg _ _))
      (mul_nonneg hb (Real.rpow_nonneg (zero_le_one.trans hW) _))

/-- The final envelope comparison for an arbitrary graded state space. All
grading manipulations happen here, away from the actual state spaces. -/
private theorem endpoint_jet_le_generic {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (x : E)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : PolarPoint → Y}
    {q q' : PolarPoint} (hq : q' = q) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {Aenv : ℕ → ℝ} {n l m : ℕ} {a b V W : ℝ}
    (hb : ‖iteratedFDeriv ℝ n f q'‖ ≤ rootAffineJetEnvelope σ Aenv n * (1 + p (n + l) x))
    (hAenv : Aenv n = a * V ^ a) (ha : 0 ≤ a) (hab : 2 * a ≤ b) (hV : 1 ≤ V)
    (hVW : V ≤ W) (hlm : l ≤ m) :
    ‖iteratedFDeriv ℝ n f q‖ ≤ b * W ^ b * (1 + p (n + m) x) := by
  subst hq
  simp only [rootAffineJetEnvelope_unit hσ, hAenv] at hb
  exact hb.trans (physicalRoot_two_material_mono hp ha hab hV hVW hlm x)

/-- Positive chart jets and every real height power have material bounds
at both actual roots, with a common neighborhood and derivative loss.
All material constants precede the component, actual host and state. -/
theorem n04b_actual_root_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε K₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hK : 0 < K₀) :
    ∃ C0 : ℝ, ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ γ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ side : Bool, ∀ θ : ℝ,
        let r := n01ComponentRoot C m side
        let i := if side then (K.cutPair m).2 else (K.cutPair m).1
        (r, θ) ∈ physicalPieceClosed S K z i ∧ 0 < K.height z i (r, θ) ∧
          (∀ n : ℕ, 1 ≤ n →
            ‖iteratedFDeriv ℝ n (K.chart z i) (r, θ)‖ ≤
              B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
                (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
                  (z - (C.referenceState, 0)))) ∧
          ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun p => K.height z i p ^ γ) (r, θ)‖ ≤
            B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
              (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
                (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  refine (n01_exists_common_root_inputs n04FlowJetsTarget_proof hS hT hN.1.1).elim ?_
  intro rootBase hR1
  refine hR1.elim ?_
  intro flowLoss hR2
  refine hR2.elim ?_
  intro η hR3
  have hb := hR3.1
  have hη := hR3.2.1
  have hηε := hR3.2.2.1
  have hflow := hR3.2.2.2.1
  have hinputs := hR3.2.2.2.2
  have hsub := stateNeighborhood_mono S C hb hηε
  have hN' := nonlinearPropertiesThrough03_restrict hT hN hb le_rfl hη hηε
  have hA' := n04PartA_restrict hA hb hηε
  have hB' := n04PartB_restrict hB hb hηε
  have hfield' : N04bFieldRegularity D S C L rootBase η :=
    { smooth_coefficients := fun z hz => hfield.smooth_coefficients z (hsub hz)
      periodic_coefficients := fun z hz => hfield.periodic_coefficients z (hsub hz)
      positive_a := fun z hz => hfield.positive_a z (hsub hz)
      reference_flow := hfield.reference_flow
      negative_discriminant := fun z hz => hfield.negative_discriminant z (hsub hz) }
  refine (n01_rootChart_unit_positive_material_jets_of_component_optical
    hS hT hN'.1.1 hflow hK).elim ?_
  intro CF hF1
  refine hF1.elim ?_
  intro lowF hF2
  refine hF2.elim ?_
  intro lossF hF3
  have hCF := hF3.1
  have hfloorF := hF3.2.1
  refine hF3.2.2.elim ?_
  intro BF hBFc
  have hBF := hBFc.1
  have hchart := hBFc.2
  refine (n01_rootDividedHeight_unit_rpow_material_jets_of_component_optical
    hS hT hN'.1.1 hflow hK).elim ?_
  intro CH hH1
  refine hH1.elim ?_
  intro lowH hH2
  refine hH2.elim ?_
  intro lossH hH3
  have hCH := hH3.1
  have hfloorH := hH3.2.1
  have hheights := hH3.2.2
  let C0 : ℝ := max CF CH
  let low : ℕ := max lowF lowH
  let outLoss : ℕ := max lossF lossH
  let newBase : ℕ := max rootBase (max low outLoss)
  let ε' : ℝ := min η (1 / 2)
  have hC0 : 1 ≤ C0 := hCF.trans (le_max_left _ _)
  have hE (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT j)).2.2.1
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorF j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le)
  refine ⟨C0, newBase, outLoss, ε', hC0, hfloor,
    hb.trans (le_max_left _ _),
    (le_max_right low outLoss).trans (le_max_right rootBase (max low outLoss)),
    lt_min hη (by norm_num), (min_le_left _ _).trans hηε, ?_⟩
  intro γ
  refine (hheights γ).elim ?_
  intro BH hBHh
  have hBH := hBHh.1
  have hheight := hBHh.2
  let B : ℕ → ℝ := fun n => 2 * (1 + BF n + BH n)
  have hBpos (n : ℕ) : 0 < B n :=
    mul_pos (by norm_num) (add_pos (add_pos zero_lt_one (hBF n)) (hBH n))
  have hFB (n : ℕ) : 2 * BF n ≤ B n := by dsimp only [B]; linarith only [hBH n]
  have hHB (n : ℕ) : 2 * BH n ≤ B n := by dsimp only [B]; linarith only [hBF n]
  refine ⟨B, hBpos, ?_⟩
  intro z hz hs m j hhost hoptical side θ
  have hzroot : z ∈ stateNeighborhood S C rootBase η :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz
  have hzlow : z ∈ stateNeighborhood S C low ε' :=
    stateNeighborhood_mono S C
      ((le_max_left low outLoss).trans (le_max_right rootBase (max low outLoss))) le_rfl hz
  have hlow : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have he : ε' ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hzF := (hp (le_max_left lowF lowH) _).trans hlow
  have hzH := (hp (le_max_right lowF lowH) _).trans hlow
  refine (hinputs m side).elim ?_
  intro g hI1
  refine hI1.elim ?_
  intro R hI2
  refine hI2.elim ?_
  intro hR hI3
  refine hI3.elim ?_
  intro κ hI4
  have hg := hI4.1
  have hκ := hI4.2.2.1
  have hfactor := hI4.2.2.2.1
  have hgeometry := hI4.2.2.2.2.1
  have hflows := hI4.2.2.2.2.2
  refine (hflows 1 zero_lt_one).elim ?_
  intro δ hD1
  refine hD1.elim ?_
  intro A hD2
  have hδ := hD2.1
  have hApos := hD2.2.2.2.1
  have hfamily := hD2.2.2.2.2
  have hstrip := (hgeometry.1 z hzroot hs).1
  refine (n03_controlledRootInput_unit_identification
    hS hT hN' hfield' hA' hB' hzroot hs m side hg hR hκ hδ hApos hstrip
    (hfamily z hzroot hs)).elim ?_
  intro Θ hΘi
  have hΘ := hΘi.1
  have hident := hΘi.2
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
    (n01RootLabel S C z m side)
  let V := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  let AF : ℕ → ℝ := fun n => BF n * (CF * T.E0 (T.sample j)) ^ (BF n)
  let AH : ℕ → ℝ := fun n => BH n * (CH * T.E0 (T.sample j)) ^ (BH n)
  have hAF (n : ℕ) : 0 ≤ AF n :=
    mul_nonneg (hBF n).le (Real.rpow_nonneg (zero_le_one.trans (hfloorF j)) _)
  have hAH (n : ℕ) : 0 ≤ AH n :=
    mul_nonneg (hBH n).le (Real.rpow_nonneg (zero_le_one.trans (hfloorH j)) _)
  have hWf : CF * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le
  have hWh : CH * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (hE j).le
  have hσ : σ = 1 ∨ σ = -1 := n01ComponentRootOrientation_eq side
  have hσne : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hpoint : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hidθ := hident θ
  have hclosed := hidθ.1
  have hFregular := hidθ.2.1
  have hHregular := hidθ.2.2.1
  have hHpos := hidθ.2.2.2.1
  have hFjet := hidθ.2.2.2.2.1
  have hHjet := hidθ.2.2.2.2.2
  have hFbound (n : ℕ) (hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n (fun p => K.chart z i (rootProfileShift r σ p)) (0, θ)‖ ≤
        AF n * (1 + pairGrading (stateGrading S) realGrading (n + lossF)
          (z - (C.referenceState, 0))) := by
    calc
      _ = ‖iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ)‖ :=
        congrArg norm (hFjet n)
      _ ≤ _ := hchart z hzroot hs hzF m j hhost hoptical side g hg hfactor R hR hstrip
        δ hδ.ne' Θ hΘ θ n hn
  have hHbound : PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
      lossH AH (z - (C.referenceState, 0))
      (fun p => K.height z i (rootProfileShift r σ p) ^ γ) (0, θ) := by
    intro n
    calc
      _ = ‖iteratedFDeriv ℝ n (fun p => rootDividedHeight 1 V G p ^ γ) (0, θ)‖ :=
        congrArg norm (hHjet γ n)
      _ ≤ _ := hheight z hzroot hs hzH m j hhost hoptical side g hg hfactor R hR hstrip
        δ hδ.ne' Θ hΘ θ n
  have hHpow : ContDiffAt ℝ ∞
      (fun p => K.height z i (rootProfileShift r σ p) ^ γ) (0, θ) :=
    hHregular.rpow_const_of_ne (by
      show K.height z i (rootProfileShift r σ (0, θ)) ≠ 0
      rw [hpoint]
      exact hHpos.ne')
  have hFphysical := rootProfile_unscale_positiveJets r σ hσne hAF hFregular hFbound
  sorry

end ContinuousFlexibility.Analysis
