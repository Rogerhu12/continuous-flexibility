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

set_option diagnostics true in
/-- Patch the same strip jets and their proved zero values, then apply the
ordinary-to-material bound without specializing the parameter space. -/
private theorem correctionCoefficient_material_bound_of_flat_data
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E)
    (Araw : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ × ℝ))
    (Asmooth : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    {U : Set E} (l h F W : ℕ → ℝ) (n B L : ℕ)
    (Z : PolarPoint → Prop)
    (hrestrict : ∀ x, x ∈ U → ∀ v : Fin n → E,
      (Asmooth n x v).val = Araw n x v)
    (hflat : ∀ Q : ℝ, 0 ≤ Q → ∃ K : ℝ, 0 < K ∧ ∀ m, F m * W m ^ Q ≤ K)
    (hsplit : ∀ q ∈ annularOpen D, (∃ m, q.1 ∈ Ioo (l m) (h m)) ∨ Z q)
    (hvanish : ∀ q, Z q → ∀ a b : ℕ, ∀ x ∈ U, ∀ v : Fin n → E,
      mixedDerivative a b (fun y => (Araw n x v y).1) q = 0 ∧
      mixedDerivative a b (fun y => (Araw n x v y).2) q = 0)
    (hb : StripCoefficientFlatOneHighBound p Araw U l h F W n B L)
    (r : ℝ) (hr : 0 ≤ r) :
    CoefficientMaterialOneHighBound (T := T) p Asmooth n B L 0
      (U ∩ {x | p B x ≤ r}) := by
  run_tac Lean.logInfo "N02N03 FlatBounds: material-assembly"
  refine coefficientMaterialOneHighBound_of_ordinary
    (E := E) (D := D) (T := T) hT p Asmooth n B L 0
    (U ∩ {x | p B x ≤ r}) ?_
  intro k
  obtain ⟨A, Q, hA, hQ, hab⟩ := hb r hr k
  obtain ⟨K, hK, hflat⟩ := hflat Q hQ
  run_tac Lean.logInfo "N02N03 FlatBounds: material-envelope"
  refine ⟨A * K, mul_nonneg hA hK.le, fun x hx v a b habk q hq => ?_⟩
  have heq := hrestrict x hx.1 v
  have hfst := congrArg (fun f : PolarPoint → ℝ × ℝ =>
    mixedDerivative a b (fun y => (f y).1) q) heq
  have hsnd := congrArg (fun f : PolarPoint → ℝ × ℝ =>
    mixedDerivative a b (fun y => (f y).2) q) heq
  rw [hfst, hsnd, pow_zero, mul_one]
  have hW : 0 ≤ oneHighVariationWeight p B (k + L) x v :=
    multilinearTameSize_nonneg _ _ _ (add_nonneg zero_le_one (apply_nonneg _ _)) v
  rcases hsplit q hq with ⟨m, hm⟩ | hzero
  · have hvalue := hab m x hx.1 hx.2 v a b habk q hm
    have hupper : A * F m * W m ^ Q * oneHighVariationWeight p B (k + L) x v ≤
        A * K * oneHighVariationWeight p B (k + L) x v := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hflat m) hA) hW
      simpa only [mul_assoc] using hh
    exact ⟨hvalue.1.trans hupper, hvalue.2.trans hupper⟩
  · obtain ⟨hf0, hs0⟩ := hvanish q hzero a b x hx.1 v
    constructor
    · simpa only [hf0, abs_zero] using
        (mul_nonneg (mul_nonneg hA hK.le) hW)
    · simpa only [hs0, abs_zero] using
        (mul_nonneg (mul_nonneg hA hK.le) hW)

set_option diagnostics true in
/-- Assemble the original unit low-order neighborhoods from the same order
witnesses and absolute sublevel bounds. -/
private theorem correctionCoefficient_local_bounds_of_sublevels
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} {U : Set E}
    (p : ℕ → Seminorm ℝ E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (P : ℕ → ℕ → ℕ → Prop)
    (hb : ∀ n : ℕ, ∃ B L : ℕ, P n B L)
    (hmaterial : ∀ n B L, P n B L → ∀ r : ℝ, 0 ≤ r →
      CoefficientMaterialOneHighBound (T := T) p A n B L 0
        (U ∩ {x | p B x ≤ r})) :
    LocalCoefficientMaterialTameBounds (T := T) (U := U) p A := by
  run_tac Lean.logInfo "N02N03 FlatBounds: local-assembly"
  intro n x₀ hx₀
  obtain ⟨B, L, hb⟩ := hb n
  refine ⟨B, L, 0, 1, zero_lt_one, ?_⟩
  have hbound := hmaterial n B L hb (p B x₀ + 1)
    (add_nonneg (apply_nonneg _ _) zero_le_one)
  intro k
  obtain ⟨K, hK, hKb⟩ := hbound k
  refine ⟨K, hK, fun x hx v a b hab q => hKb x ⟨hx.1, ?_⟩ v a b hab q⟩
  have htriangle := map_add_le_add (p B) (x - x₀) x₀
  rw [sub_add_cancel] at htriangle
  have hnear : p B (x - x₀) < 1 := hx.2
  show p B x ≤ p B x₀ + 1
  linarith only [htriangle, hnear]

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

set_option diagnostics true in
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
  run_tac Lean.logInfo "N02N03 FlatBounds: material-provider"
  let E : Type := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let Araw : ∀ i : ℕ, E → MultilinearMap ℝ (fun _ : Fin i => E) (PolarPoint → ℝ × ℝ) :=
    hN.returnCorrectionCoefficientScalarJets
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR j hcell χ hχrange hcutoff hdisc
  let Asmooth : ∀ i : ℕ, E → MultilinearMap ℝ (fun _ : Fin i => E)
      (annularSmoothCoefficientSpace D) :=
    hN.returnCorrectionSmoothCoefficientJets
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc
  exact correctionCoefficient_material_bound_of_flat_data
    (E := E) (D := D) (T := T) (U := U) hT p Araw Asmooth l h
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => radialE (D.cellIndex (j m))) n B L
    (fun q => ∀ᶠ s in 𝓝 q.1, ∀ m, deriv (χ m) s = 0)
    (fun x hx v => hN.returnCorrectionSmoothCoefficientJets_apply
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc n x hx v)
    (fun Q hQ => by
      obtain ⟨K, hK, hflat⟩ := hN.control_actual_cell_flat_radialE_bounded
        (D := D) (T := T) (S := S) (C := C)
        (base := base) (loss := loss) (ε := ε) (γ := 3 / 4) (Q := Q)
        hS hT (by norm_num : (0 : ℝ) < 3 / 4) hQ
      exact ⟨K, hK, fun m => hflat m (j m) (hcell m)⟩)
    (fun q hq => hN.cutoffStrip_or_eventually_zero
      (D := D) (T := T) (S := S) (C := C)
      (base := base) (loss := loss) (ε := ε)
      χ hsupp hend l h hstripSupport (r := q.1) hq.1)
    (fun q hzero a b x hx v => by
      have hf0 := hN.returnCorrectionCoefficientScalarJets_component_mixed_zero
        (D := D) (T := T) (S := S) (C := C) (R := R)
        (base := base) (loss := loss) (ε := ε)
        hS hT hR j hcell χ hχrange hcutoff hdisc
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (p := q) hzero a b n x hx v
      have hs0 := hN.returnCorrectionCoefficientScalarJets_component_mixed_zero
        (D := D) (T := T) (S := S) (C := C) (R := R)
        (base := base) (loss := loss) (ε := ε)
        hS hT hR j hcell χ hχrange hcutoff hdisc
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (p := q) hzero a b n x hx v
      simp only [ContinuousLinearMap.coe_fst'] at hf0
      simp only [ContinuousLinearMap.coe_snd'] at hs0
      exact ⟨hf0, hs0⟩)
    hb r hr

set_option diagnostics true in
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
  run_tac Lean.logInfo "N02N03 FlatBounds: local-provider"
  let E : Type := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let Araw : ∀ i : ℕ, E → MultilinearMap ℝ (fun _ : Fin i => E) (PolarPoint → ℝ × ℝ) :=
    hN.returnCorrectionCoefficientScalarJets
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR j hcell χ hχrange hcutoff hdisc
  let Asmooth : ∀ i : ℕ, E → MultilinearMap ℝ (fun _ : Fin i => E)
      (annularSmoothCoefficientSpace D) :=
    hN.returnCorrectionSmoothCoefficientJets
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc
  exact correctionCoefficient_local_bounds_of_sublevels
    (E := E) (D := D) (T := T) (U := U) p Asmooth
    (fun n B L => StripCoefficientFlatOneHighBound p Araw U l h
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => radialE (D.cellIndex (j m))) n B L)
    hb
    (fun n B L hb r hr =>
      hN.returnCorrectionSmoothCoefficientJets_material_bound_of_flat_strips
        (D := D) (T := T) (S := S) (C := C) (R := R)
        (base := base) (loss := loss) (ε := ε)
        hS hT hR j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh
        hstripSupport hstripDisc p n B L hb r hr)

end ContinuousFlexibility.Statements
