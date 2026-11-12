import ContinuousFlexibility.Analysis.N01CorrectionCoefficientFlatBounds
import ContinuousFlexibility.Analysis.FlatMixedDiagonalRealization
import ContinuousFlexibility.Analysis.ActualRadialCellComparison

/-!
# Transferring actual joint coefficient estimates to the source family

The genuine joint towers on each buffered strip equal the parameter
jets selected for the original global coefficient field. Polarization,
the fixed finite maximum for the two components, and the flat strip
estimate therefore control the same smooth coefficient family used by
the source operator.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientTameTransferStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private theorem correctionCoefficient_flat_bound_of_joint_data
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (l h : ℕ → ℝ) {f : ℕ → E × PolarPoint → ℝ × ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m))
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (W F : ℕ → ℝ) (hW : ∀ m, 1 ≤ W m) (hF : ∀ m, 0 ≤ F m)
    (hV : ∀ m, IsOpen (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)))
    (hc : ∀ m, Convex ℝ (U ×ˢ (Ioo (l m) (h m) ×ˢ (univ : Set ℝ))))
    (Araw : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ × ℝ))
    (hjoint : ∀ (m : ℕ) (Q : (ℝ × ℝ) →L[ℝ] ℝ) (n : ℕ) (x : E), x ∈ U →
      ∀ (v : Fin n → E) (q : PolarPoint), q ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ) →
        Q (Araw n x v q) =
          (solveSmoothDirectionsPostcomp (J m) Q).D n (x, q) (fun i => (v i, 0)))
    (hfst : HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp (J m) (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    (hsnd : HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp (J m) (ContinuousLinearMap.snd ℝ ℝ ℝ))) :
    ∀ n : ℕ, ∃ B L : ℕ, StripCoefficientFlatOneHighBound p Araw U l h F W n B L := by
  intro n
  obtain ⟨B₀, L₀, hb₀⟩ := hfst n
  obtain ⟨B₁, L₁, hb₁⟩ := hsnd n
  let B := max B₀ B₁
  let L := max L₀ L₁
  have h₀ := hb₀.mono hp (fun m => zero_le_one.trans (hW m)) hF
    (le_max_left B₀ B₁) (le_max_left L₀ L₁)
  have h₁ := hb₁.mono hp (fun m => zero_le_one.trans (hW m)) hF
    (le_max_right B₀ B₁) (le_max_right L₀ L₁)
  refine ⟨B, L, fun r hr s => ?_⟩
  obtain ⟨A, P, hA, hP, hAb⟩ := h₀.mixed_oneHigh hW hF hV hc r hr s
  obtain ⟨A', P', hA', hP', hA'b⟩ := h₁.mixed_oneHigh hW hF hV hc r hr s
  refine ⟨A + A', P + P', add_nonneg hA hA', add_nonneg hP hP', ?_⟩
  intro m x hx hxB v a b hab q hq
  have hq' : q ∈ Ioo (l m) (h m) ×ˢ (univ : Set ℝ) := ⟨hq, mem_univ _⟩
  have heq (Q : (ℝ × ℝ) →L[ℝ] ℝ) :
      mixedDerivative a b (fun y => Q (Araw n x v y)) q =
        mixedDerivative a b (fun y =>
          (solveSmoothDirectionsPostcomp (J m) Q).D
            n (x, y) (fun i => (v i, 0))) q :=
    mixedDerivative_congr_on_open (hV m)
      (fun y hy => hjoint m Q n x hx v y hy) a b hq'
  have hsize : 0 ≤ oneHighVariationWeight p B (s + L) x v :=
    multilinearTameSize_nonneg _ _ _ (add_nonneg zero_le_one (apply_nonneg _ _)) v
  have hupper {A₀ P₀ : ℝ} (hA₀ : A₀ ≤ A + A') (hP₀ : P₀ ≤ P + P') :
      A₀ * F m * W m ^ P₀ * oneHighVariationWeight p B (s + L) x v ≤
        (A + A') * F m * W m ^ (P + P') * oneHighVariationWeight p B (s + L) x v :=
    mul_le_mul_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_right hA₀ (hF m))
      (Real.rpow_le_rpow_of_exponent_le (hW m) hP₀)
      (Real.rpow_nonneg (zero_le_one.trans (hW m)) _)
      (mul_nonneg (add_nonneg hA hA') (hF m))) hsize
  exact ⟨(congrArg (fun t : ℝ => |t|) (heq (ContinuousLinearMap.fst ℝ ℝ ℝ))).trans_le
      ((hAb m x hx hxB q hq' v a b hab).trans
        (hupper (le_add_of_nonneg_right hA') (le_add_of_nonneg_right hP'))),
    (congrArg (fun t : ℝ => |t|) (heq (ContinuousLinearMap.snd ℝ ℝ ℝ))).trans_le
      ((hA'b m x hx hxB q hq' v a b hab).trans
        (hupper (le_add_of_nonneg_left hA) (le_add_of_nonneg_left hP)))⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
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
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

theorem N01Properties.returnCorrectionCoefficientScalarJets_flat_bound_of_joint_growth
    (p : ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S)) (hp : Monotone p)
    (hfst : HasFlatMixedTameGrowth p (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    (hsnd : HasFlatMixedTameGrowth p (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.snd ℝ ℝ ℝ))) :
    ∀ n : ℕ, ∃ B L : ℕ, StripCoefficientFlatOneHighBound p
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc)
      (sectorNeighborhood S base ε ε ×ˢ univ) l h
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => radialE (D.cellIndex (j m))) n B L := by
  let E : Type := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let f : ℕ → E × PolarPoint → ℝ × ℝ := fun _ x =>
    returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1.1) x.2 x.1.2
  let J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m) := fun m =>
    hN.returnCorrectionCoefficient_parameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR χ hχ hχrange m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
      (fun z hz q hq => hstripDisc z hz m q hq)
  let Araw : ∀ k : ℕ, E → MultilinearMap ℝ (fun _ : Fin k => E) (PolarPoint → ℝ × ℝ) :=
    fun k y => hN.returnCorrectionCoefficientScalarJets
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR j hcell χ hχrange hcutoff hdisc k y
  have hW (m : ℕ) : 1 ≤ radialE (D.cellIndex (j m)) := one_le_radialE_of_nat _
  have hF (m : ℕ) : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    (Real.rpow_pos_of_pos ((material_circle_sample_weights_pos hT hN.1.1).2 m) _).le
  have hV (m : ℕ) : IsOpen (Ioo (l m) (h m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo (l m) (h m) ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  exact correctionCoefficient_flat_bound_of_joint_data
    (E := E) (U := U) (f := f) l h J p hp
    (fun m => radialE (D.cellIndex (j m)))
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) hW hF hV hc Araw
    (fun m Q k x hx v q hq => hN.returnCorrectionCoefficientScalarJets_eq_joint_on_strip
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hR j hcell χ hχrange hcutoff hdisc hχ m (l m) (h m) (hl m) (hh m)
      (fun z hz y hy => hstripDisc z hz m y hy) Q k x hx v (p := q) hq)
    hfst hsnd

end ContinuousFlexibility.Statements
