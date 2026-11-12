import ContinuousFlexibility.Analysis.N01OriginalCoefficientSpatialJets
import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope
import ContinuousFlexibility.Analysis.N01CoefficientJointTower
import ContinuousFlexibility.Analysis.JointJetSpatialRegularity

/-!
# Fixed-loss bounds for every actual original coefficient mixed jet

The positive sample height in the original N01 estimate absorbs its
sample exponential factor. Thus all component labels and physical points
share one numerical constant at each order. The low order and derivative
loss remain the original N01 orders. At parameter order zero the actual
reference jets are restored; positive orders are exactly the increment
jets and retain their homogeneous one-high bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01OriginalCoefficientTameBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

private theorem originalCoefficient_oneHigh_nonneg
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B H : ℕ) {n : ℕ} (x : E) (v : Fin n → E) :
    0 ≤ oneHighVariationWeight p B H x v :=
  multilinearTameSize_nonneg (p B) (p H) n
    (add_nonneg zero_le_one (apply_nonneg _ _)) v

private theorem originalCoefficient_oneHigh_zero_ge_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B H : ℕ) (x : E) (v : Fin 0 → E) :
    1 ≤ oneHighVariationWeight p B H x v := by
  simp only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
    mul_one, add_zero]
  exact le_add_of_nonneg_right (apply_nonneg (p H) x)

private theorem originalCoefficient_abs_weighted_bound
    {u B H E₀ A W : ℝ} (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hweight : H * E₀ ≤ A) (hb : |u| ≤ B * H * E₀ * W) :
    |u| ≤ (B * A) * W := by
  calc
    |u| ≤ B * H * E₀ * W := hb
    _ = (B * W) * (H * E₀) := by ring
    _ ≤ (B * W) * A := mul_le_mul_of_nonneg_left hweight (mul_nonneg hB hW)
    _ = (B * A) * W := by ring

private theorem originalCoefficient_abs_add_bound
    {u v A B W : ℝ} (hB : 0 ≤ B) (hW : 1 ≤ W)
    (hu : |u| ≤ A * W) (hv : |v| ≤ B) :
    |u + v| ≤ (A + B) * W :=
  (abs_add_le u v).trans
    ((add_le_add hu (hv.trans (le_mul_of_one_le_right hB hW))).trans_eq
      (add_mul A B W).symm)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)

include hN in
theorem N01Properties.reference_coefficient_mixed_uniform_bound (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin 3) (a b : ℕ), a + b ≤ s →
      ∀ p ∈ annularOpen D,
        |mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p| ≤ K := by
  classical
  have hraw (k : Fin 3 × Fin (s + 1) × Fin (s + 1)) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ annularOpen D,
        |mixedDerivative k.2.1 k.2.2
          (originalCoefficientEntry D S C k.1 (C.referenceState, 0)) p| ≤ A :=
    (hN.reference_coefficient_smooth_jets k.1).2 k.2.1 k.2.2
  choose A hA hbound using hraw
  refine ⟨∑ k, A k, Finset.sum_nonneg (fun k _ => hA k), ?_⟩
  intro i a b hab p hp
  let k : Fin 3 × Fin (s + 1) × Fin (s + 1) :=
    (i, ⟨a, by omega⟩, ⟨b, by omega⟩)
  exact (hbound k p hp).trans
    (Finset.single_le_sum (f := A) (fun j _ => hA j) (Finset.mem_univ k))

theorem N01Properties.sectorCoefficientTower_uniform_oneHigh
    (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j i a b p (hab : a + b ≤ s) (hp : p.1 ∈ D.cells j),
      ∀ x ∈ sectorNeighborhood S base ε ε, ∀ v : Fin n → StateDirections S × ℝ,
        |(hN.sectorCoefficientTower j i a b p hp).D n x v| ≤
          K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) x v := by
  let data := N01Properties.sectorCoefficientTower_bound
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε) hN n s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  let weightData := materialSample_H_E0_envelope (D := D) (T := T) hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  let A : ℝ := weightData.choose
  have hA : 0 < A := weightData.choose_spec.1
  refine ⟨B * A, mul_nonneg hB.le hA.le, ?_⟩
  intro j i a b p hab hp x hx v
  have hW : 0 ≤ oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
      base (s + loss) x v :=
    originalCoefficient_oneHigh_nonneg (pairGrading (sectorGrading S) realGrading)
      base (s + loss) x v
  have hb : |(hN.sectorCoefficientTower j i a b p hp).D n x v| ≤
      B * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
        oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          base (s + loss) x v :=
    data.choose_spec.2 j i a b p hab hp x hx v
  exact originalCoefficient_abs_weighted_bound hB.le hW (weightData.choose_spec.2 j) hb

theorem N01Properties.originalComponentCoefficientScalarJet_uniform_oneHigh
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
        (i : Fin 3) (a b : ℕ), a + b ≤ s →
      ∀ x ∈ sectorNeighborhood S base ε ε, ∀ v : Fin n → StateDirections S × ℝ,
      ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
        |mixedDerivative a b
          (hN.originalComponentCoefficientScalarJet m j hcell i n x v) p| ≤
          K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) x v := by
  cases n with
  | zero =>
      let incData := N01Properties.sectorCoefficientTower_uniform_oneHigh
        (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
        hN hT 0 s
      let A : ℝ := incData.choose
      have hA : 0 ≤ A := incData.choose_spec.1
      let refData := N01Properties.reference_coefficient_mixed_uniform_bound
        (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε) hN s
      let B : ℝ := refData.choose
      have hB : 0 ≤ B := refData.choose_spec.1
      refine ⟨A + B, add_nonneg hA hB, ?_⟩
      intro m j hcell i a b hab x hx v p hp
      let J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun y => coefficientFamily D S C i a b p (liftSectorParameter S C y)) :=
        hN.sectorCoefficientTower j i a b p (hcell hp.1)
      have hv : v = (Fin.elim0 : Fin 0 → StateDirections S × ℝ) := Subsingleton.elim _ _
      have hpoint : J.D 0 x v =
          coefficientFamily D S C i a b p (liftSectorParameter S C x) :=
        (congrArg (fun w : Fin 0 → StateDirections S × ℝ => J.D 0 x w) hv).trans
          (J.zero x hx)
      have hinc : |coefficientFamily D S C i a b p (liftSectorParameter S C x)| ≤
          A * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) x v :=
        (congrArg abs hpoint).symm.trans_le
          (incData.choose_spec.2 j i a b p hab (hcell hp.1) x hx v)
      have hpD : p ∈ annularOpen D := hN.negativeComponent_subset_annularOpen m hp
      have hW : 1 ≤ oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          base (s + loss) x v :=
        originalCoefficient_oneHigh_zero_ge_one (pairGrading (sectorGrading S) realGrading)
          base (s + loss) x v
      have heq : mixedDerivative a b
          (hN.originalComponentCoefficientScalarJet m j hcell i 0 x v) p =
          coefficientFamily D S C i a b p (liftSectorParameter S C x) +
            mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p :=
        hN.originalComponentCoefficientScalarJet_mixedDerivative_zero
          hS hT m j hcell i a b x hx v hp
      exact (congrArg abs heq).trans_le (originalCoefficient_abs_add_bound hB hW hinc
        (refData.choose_spec.2 i a b hab p hpD))
  | succ n =>
      let data := N01Properties.sectorCoefficientTower_uniform_oneHigh
        (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
        hN hT (n + 1) s
      let K : ℝ := data.choose
      refine ⟨K, data.choose_spec.1, ?_⟩
      intro m j hcell i a b hab x hx v p hp
      have heq : mixedDerivative a b
          (hN.originalComponentCoefficientScalarJet m j hcell i (n + 1) x v) p =
          (hN.sectorCoefficientTower j i a b p (hcell hp.1)).D (n + 1) x v :=
        hN.originalComponentCoefficientScalarJet_mixedDerivative_positive
          hS hT m j hcell i a b n hp x hx v
      exact (congrArg abs heq).trans_le
        (data.choose_spec.2 j i a b p hab (hcell hp.1) x hx v)

theorem N01Properties.originalCoefficient_parameterSpatialTower_parameterJet
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ)
    (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ)
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    hN.originalComponentCoefficientScalarJet m j hcell i n x v p =
      (hN.originalCoefficient_parameterSpatialTower hS hT m j hcell i).D
        n (x, p) (fun k => (v k, 0)) := by
  let J := hN.originalCoefficient_parameterSpatialTower hS hT m j hcell i
  let K := (hN.originalCoefficientSectorTower j i p (hcell hp.1)).congrOn
    (g := fun y => originalCoefficientEntry D S C i (liftSectorParameter S C y) p)
    (by intro y hy; simp only [originalCoefficientEntry, ite_apply])
  have hlocal := localScalarJet_of_mem
    (fun q (hq : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) =>
      hN.originalCoefficientSectorTower j i q (hcell hq.1)) n x v hp
  exact hlocal.trans (J.pointTower_eq_jointJet
    (sectorNeighborhood_isOpen S base ε ε) p hp K n x hx v)

/-- The same fixed-loss estimate expressed on the actual joint tower,
for use in the square-root and reciprocal chain rules. -/
theorem N01Properties.originalCoefficient_joint_mixed_uniform_oneHigh
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
        (i : Fin 3) (a b : ℕ), a + b ≤ s →
      ∀ x ∈ sectorNeighborhood S base ε ε, ∀ v : Fin n → StateDirections S × ℝ,
      ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
        |mixedDerivative a b
          (fun q => (hN.originalCoefficient_parameterSpatialTower hS hT m j hcell i).D
            n (x, q) (fun k => (v k, 0))) p| ≤
          K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) x v := by
  let data := N01Properties.originalComponentCoefficientScalarJet_uniform_oneHigh
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT n s
  let K : ℝ := data.choose
  refine ⟨K, data.choose_spec.1, ?_⟩
  intro m j hcell i a b hab x hx v p hp
  let f : PolarPoint → ℝ := hN.originalComponentCoefficientScalarJet m j hcell i n x v
  let g : PolarPoint → ℝ := fun q =>
    (hN.originalCoefficient_parameterSpatialTower hS hT m j hcell i).D
      n (x, q) (fun k => (v k, 0))
  have hfg : EqOn f g (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    fun q hq => hN.originalCoefficient_parameterSpatialTower_parameterJet
      hS hT m j hcell i n x hx v hq
  have heq : mixedDerivative a b f p = mixedDerivative a b g p :=
    mixedDerivative_congr_on_open (f := f) (g := g)
      (isOpen_Ioo.prod isOpen_univ) hfg a b hp
  have hb : |mixedDerivative a b f p| ≤
      K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
        base (s + loss) x v :=
    data.choose_spec.2 m j hcell i a b hab x hx v p hp
  exact (congrArg abs heq).symm.trans_le hb

end ContinuousFlexibility.Statements
