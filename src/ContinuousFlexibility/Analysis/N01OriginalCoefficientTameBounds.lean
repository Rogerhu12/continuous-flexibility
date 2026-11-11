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

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01OriginalCoefficientTameBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)

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
  let data := hN.sectorCoefficientTower_bound n s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  obtain ⟨A, hA, hweight⟩ := materialSample_H_E0_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  refine ⟨B * A, mul_nonneg hB.le hA.le, ?_⟩
  intro j i a b p hab hp x hx v
  have hW : 0 ≤ oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
      base (s + loss) x v :=
    multilinearTameSize_nonneg _ _ _ (add_nonneg zero_le_one (apply_nonneg _ _)) v
  have hb := data.choose_spec.2 j i a b p hab hp x hx v
  have hscale := mul_le_mul_of_nonneg_left (hweight j) (mul_nonneg hB.le hW)
  apply hb.trans
  convert hscale using 1 <;> ring

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
      obtain ⟨A, hA, habound⟩ := hN.sectorCoefficientTower_uniform_oneHigh hT 0 s
      obtain ⟨B, hB, hb⟩ := hN.reference_coefficient_mixed_uniform_bound s
      refine ⟨A + B, add_nonneg hA hB, ?_⟩
      intro m j hcell i a b hab x hx v p hp
      have hpoint : (hN.sectorCoefficientTower j i a b p (hcell hp.1)).D 0 x v =
          coefficientFamily D S C i a b p (liftSectorParameter S C x) := by
        have hv : v = Fin.elim0 := Subsingleton.elim _ _
        rw [hv]
        exact (hN.sectorCoefficientTower j i a b p (hcell hp.1)).zero x hx
      have hinc := habound j i a b p hab (hcell hp.1) x hx v
      rw [hpoint] at hinc
      have hpD : p ∈ annularOpen D := by
        have he := hN.2.2.2.1.1 m
        exact ⟨⟨he.1.trans hp.1.1, hp.1.2.trans he.2.2⟩, mem_univ _⟩
      have hW : 1 ≤ oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          base (s + loss) x v := by
        simp only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
          mul_one, add_zero]
        exact le_add_of_nonneg_right (apply_nonneg _ _)
      have href := (hb i a b hab p hpD).trans
        (le_mul_of_one_le_right hB hW)
      rw [hN.originalComponentCoefficientScalarJet_mixedDerivative_zero
        hS hT m j hcell i a b x hx v hp]
      exact (abs_add_le _ _).trans ((add_le_add hinc href).trans_eq (by ring))
  | succ n =>
      obtain ⟨K, hK, hb⟩ := hN.sectorCoefficientTower_uniform_oneHigh hT (n + 1) s
      refine ⟨K, hK, ?_⟩
      intro m j hcell i a b hab x hx v p hp
      rw [hN.originalComponentCoefficientScalarJet_mixedDerivative_positive
        hS hT m j hcell i a b n hp x hx v]
      exact hb j i a b p hab (hcell hp.1) x hx v

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
  obtain ⟨K, hK, hb⟩ :=
    hN.originalComponentCoefficientScalarJet_uniform_oneHigh hS hT n s
  refine ⟨K, hK, ?_⟩
  intro m j hcell i a b hab x hx v p hp
  have heq := mixedDerivative_congr_on_open (isOpen_Ioo.prod isOpen_univ)
    (fun q hq => hN.originalCoefficient_parameterSpatialTower_parameterJet
      hS hT m j hcell i n x hx v hq) a b hp
  exact (congrArg abs heq).symm.trans_le (hb m j hcell i a b hab x hx v p hp)

end ContinuousFlexibility.Statements
