import ContinuousFlexibility.Analysis.N01CorrectionCoefficientSmoothJets
import ContinuousFlexibility.Analysis.N01FlowRadialSamplePrefactor
import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope
import ContinuousFlexibility.Analysis.MaterialCoordinateJetBudget

/-!
# Flat strip estimates for the actual correction coefficients

The positive sample-height factor absorbs every fixed power of the
actual containing cell. Its exponent may depend on the spatial order;
the material loss remains zero. The same raw coefficient jets are then
patched by their proved vanishing off the cutoff strips and pulled back
to the material coordinate without changing their derivative budget.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.control_actual_cell_flat_radialE_bounded
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.H (T.sample m) ^ γ * radialE (D.cellIndex j) ^ Q ≤ K := by
  obtain ⟨A, hA, hradial⟩ := hN.control_actual_cell_radialE_rpow_le_M hS hT hQ
  obtain ⟨B, hB, hflat⟩ := materialSample_H_M_envelope hT hN.1.1 hγ 1
  refine ⟨A * B, mul_pos hA hB, fun m j hj => ?_⟩
  have hH : 0 ≤ T.H (T.sample m) ^ γ := Real.rpow_nonneg (by
    obtain ⟨_, hgeom⟩ := hN.1.1
    exact (hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)).2.1.le) _
  have hflat' : T.H (T.sample m) ^ γ * T.M (T.sample m) ≤ B := by
    simpa only [Real.rpow_one] using hflat m
  calc
    _ ≤ T.H (T.sample m) ^ γ * (A * T.M (T.sample m)) :=
      mul_le_mul_of_nonneg_left (hradial m j hj) hH
    _ = A * (T.H (T.sample m) ^ γ * T.M (T.sample m)) := by ring
    _ ≤ A * B := mul_le_mul_of_nonneg_left hflat' hA.le

/-- Bounds on the actual strips, with one retained flat label factor.
The spatial exponent is permitted to vary with the output order. -/
def StripCoefficientFlatOneHighBound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ × ℝ))
    (U : Set E) (l h F W : ℕ → ℝ) (n low loss : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
    ∀ m x, x ∈ U → p low x ≤ R → ∀ v : Fin n → E,
    ∀ a b : ℕ, a + b ≤ k → ∀ q : PolarPoint, q.1 ∈ Ioo (l m) (h m) →
      |mixedDerivative a b (fun y => (A n x v y).1) q| ≤
        K * F m * W m ^ Q * oneHighVariationWeight p low (k + loss) x v ∧
      |mixedDerivative a b (fun y => (A n x v y).2) q| ≤
        K * F m * W m ^ Q * oneHighVariationWeight p low (k + loss) x v

private theorem coefficientFlat_material_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ × ℝ))
    (J : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (U : Set E) (l h F W : ℕ → ℝ) (Z : PolarPoint → Prop)
    (n B L : ℕ)
    (hJ : ∀ x ∈ U, ∀ v : Fin n → E, (J n x v).val = A n x v)
    (hcover : ∀ q ∈ annularOpen D, (∃ m, q.1 ∈ Ioo (l m) (h m)) ∨ Z q)
    (hzero : ∀ q, Z q → ∀ x ∈ U, ∀ v : Fin n → E, ∀ a b : ℕ,
      mixedDerivative a b (fun y => (A n x v y).1) q = 0 ∧
      mixedDerivative a b (fun y => (A n x v y).2) q = 0)
    (hflat : ∀ Q : ℝ, 0 ≤ Q → ∃ K : ℝ, 0 ≤ K ∧ ∀ m, F m * W m ^ Q ≤ K)
    (hb : StripCoefficientFlatOneHighBound p A U l h F W n B L)
    (r : ℝ) (hr : 0 ≤ r) :
    CoefficientMaterialOneHighBound (T := T) p J n B L 0
      (U ∩ {x | p B x ≤ r}) := by
  refine coefficientMaterialOneHighBound_of_ordinary
    (E := E) (D := D) (T := T) hT p J n B L 0 (U ∩ {x | p B x ≤ r}) ?_
  intro k
  obtain ⟨C, Q, hC, hQ, hstrip⟩ := hb r hr k
  obtain ⟨K, hK, hscale⟩ := hflat Q hQ
  refine ⟨C * K, mul_nonneg hC hK, fun x hx v a b habk q hq => ?_⟩
  have heq := hJ x hx.1 v
  have hfst := congrArg (fun f : PolarPoint → ℝ × ℝ =>
    mixedDerivative a b (fun y => (f y).1) q) heq
  have hsnd := congrArg (fun f : PolarPoint → ℝ × ℝ =>
    mixedDerivative a b (fun y => (f y).2) q) heq
  simp only [hfst, hsnd, pow_zero, mul_one]
  have hW : 0 ≤ oneHighVariationWeight p B (k + L) x v :=
    multilinearTameSize_nonneg _ _ _ (add_nonneg zero_le_one (apply_nonneg _ _)) v
  rcases hcover q hq with ⟨m, hm⟩ | hz
  · have hvalue := hstrip m x hx.1 hx.2 v a b habk q hm
    have hupper : C * F m * W m ^ Q * oneHighVariationWeight p B (k + L) x v ≤
        C * K * oneHighVariationWeight p B (k + L) x v := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hscale m) hC) hW
      simpa only [mul_assoc] using hh
    exact ⟨hvalue.1.trans hupper, hvalue.2.trans hupper⟩
  · have hvalue := hzero q hz x hx.1 v a b
    constructor
    · simpa only [hvalue.1, abs_zero] using
        (mul_nonneg (mul_nonneg hC hK) hW)
    · simpa only [hvalue.2, abs_zero] using
        (mul_nonneg (mul_nonneg hC hK) hW)

private theorem coefficientFlat_local_bounds_of_ball_bounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData}
    (p : ℕ → Seminorm ℝ E)
    (J : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (U : Set E) (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ n, ∃ B L, P n B L)
    (hbound : ∀ n B L, P n B L → ∀ r : ℝ, 0 ≤ r →
      CoefficientMaterialOneHighBound (T := T) p J n B L 0
        (U ∩ {x | p B x ≤ r})) :
    LocalCoefficientMaterialTameBounds (T := T) (U := U) p J := by
  intro n x₀ hx₀
  obtain ⟨B, L, hBL⟩ := hP n
  refine ⟨B, L, 0, 1, zero_lt_one, ?_⟩
  have hball := hbound n B L hBL (p B x₀ + 1)
    (add_nonneg (apply_nonneg _ _) zero_le_one)
  intro k
  obtain ⟨K, hK, hKb⟩ := hball k
  refine ⟨K, hK, fun x hx v a b hab q => hKb x ⟨hx.1, ?_⟩ v a b hab q⟩
  calc
    p B x ≤ p B (x - x₀) + p B x₀ := by
      simpa only [sub_add_cancel] using map_add_le_add (p B) (x - x₀) x₀
    _ ≤ 1 + p B x₀ := add_le_add hx.2.le (le_refl _)
    _ = p B x₀ + 1 := add_comm _ _

local instance n01CorrectionCoefficientFlatBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {R : ReturnEquationData S}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
  (hdisc : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m p, p.1 ∈ Ioo (C.left m) (C.right m) → deriv (χ m) p.1 ≠ 0 →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripSupport : ∀ m, tsupport (deriv (χ m)) ⊆ Ioo (l m) (h m))
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

include hχ hsupp hend hl hh hstripSupport hstripDisc

theorem N01Properties.returnCorrectionSmoothCoefficientJets_material_bound_of_flat_strips
    (p : ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S))
    (n B L : ℕ)
    (hb : StripCoefficientFlatOneHighBound p
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc)
      (sectorNeighborhood S base ε ε ×ˢ univ) l h
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => radialE (D.cellIndex (j m))) n B L)
    (r : ℝ) (hr : 0 ≤ r) :
    CoefficientMaterialOneHighBound (T := T) p
      (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
        hχ hsupp hend l h hl hh hstripSupport hstripDisc)
      n B L 0 ((sectorNeighborhood S base ε ε ×ˢ univ) ∩ {x | p B x ≤ r}) := by
  let A : ∀ k : ℕ, ((StateDirections S × ℝ) × CircleSpace S) →
      MultilinearMap ℝ (fun _ : Fin k => (StateDirections S × ℝ) × CircleSpace S)
        (PolarPoint → ℝ × ℝ) :=
    hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
  let J : ∀ k : ℕ, ((StateDirections S × ℝ) × CircleSpace S) →
      MultilinearMap ℝ (fun _ : Fin k => (StateDirections S × ℝ) × CircleSpace S)
        (annularSmoothCoefficientSpace D) :=
    hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc
  have hflat (Q : ℝ) (hQ : 0 ≤ Q) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m,
        T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ Q ≤ K := by
    have data := hN.control_actual_cell_flat_radialE_bounded hS hT
      (by norm_num : (0 : ℝ) < 3 / 4) hQ
    exact ⟨data.choose, data.choose_spec.1.le,
      fun m => data.choose_spec.2 m (j m) (hcell m)⟩
  refine coefficientFlat_material_bound
    (E := (StateDirections S × ℝ) × CircleSpace S) (D := D) (T := T) hT
    p A J (sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) l h
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => radialE (D.cellIndex (j m)))
    (fun q => ∀ᶠ r in 𝓝 q.1, ∀ m, deriv (χ m) r = 0) n B L
    (fun x hx v => hN.returnCorrectionSmoothCoefficientJets_apply hS hT hR j hcell
      χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc n x hx v)
    (fun q hq => hN.cutoffStrip_or_eventually_zero χ hsupp hend l h hstripSupport hq.1)
    ?_ hflat hb r hr
  intro q hzero x hx v a b
  have hf0 := hN.returnCorrectionCoefficientScalarJets_component_mixed_zero
    hS hT hR j hcell χ hχrange hcutoff hdisc
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (p := q) hzero a b n x hx v
  have hs0 := hN.returnCorrectionCoefficientScalarJets_component_mixed_zero
    hS hT hR j hcell χ hχrange hcutoff hdisc
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (p := q) hzero a b n x hx v
  simpa only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using
    And.intro hf0 hs0

/-- The local tame interface for the same smooth coefficient jets. The
material exponent is zero, and the low order and loss precede every
spatial order. -/
theorem N01Properties.returnCorrectionSmoothCoefficientJets_local_bounds_of_flat_strips
    (p : ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S))
    (hb : ∀ n : ℕ, ∃ B L : ℕ, StripCoefficientFlatOneHighBound p
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc)
      (sectorNeighborhood S base ε ε ×ˢ univ) l h
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => radialE (D.cellIndex (j m))) n B L) :
    LocalCoefficientMaterialTameBounds (T := T)
      (U := sectorNeighborhood S base ε ε ×ˢ univ) p
      (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
        hχ hsupp hend l h hl hh hstripSupport hstripDisc) := by
  let A : ∀ k : ℕ, ((StateDirections S × ℝ) × CircleSpace S) →
      MultilinearMap ℝ (fun _ : Fin k => (StateDirections S × ℝ) × CircleSpace S)
        (PolarPoint → ℝ × ℝ) :=
    hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
  let J : ∀ k : ℕ, ((StateDirections S × ℝ) × CircleSpace S) →
      MultilinearMap ℝ (fun _ : Fin k => (StateDirections S × ℝ) × CircleSpace S)
        (annularSmoothCoefficientSpace D) :=
    hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc
  exact coefficientFlat_local_bounds_of_ball_bounds
    (E := (StateDirections S × ℝ) × CircleSpace S) (D := D) (T := T) p J
    (sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
    (fun n B L => StripCoefficientFlatOneHighBound p A
      (sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) l h
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => radialE (D.cellIndex (j m))) n B L)
    hb (fun n B L hn r hr =>
      hN.returnCorrectionSmoothCoefficientJets_material_bound_of_flat_strips
        hS hT hR j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh
        hstripSupport hstripDisc p n B L hn r hr)

end ContinuousFlexibility.Statements
