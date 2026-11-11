import ContinuousFlexibility.Analysis.N07aPrincipalModeBound

/-!
# The principal blocks of the actual relative operator

The estimates are obtained from the original current geometric jets,
the exact N04 cubic factor, and the original weak mode energy. The same
bound controls the frequency commutator, with a fixed additional loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

private theorem n07a_matrix_scalar_four_bounds {W M d c s : ℝ} (hW : 0 ≤ W)
    (h : W * |c| ≤ M ∧ W * |s| ≤ M ∧ W * |d * c| ≤ M ∧ W * |d * s| ≤ M)
    (commute sine : Bool) :
    |(W * (if commute then d else 1)) * (if sine then s else c)| ≤ M := by
  cases commute <;> cases sine
  · simpa only [Bool.false_eq_true, ite_false, mul_one, abs_mul, abs_of_nonneg hW] using h.1
  · simpa only [Bool.false_eq_true, ite_false, ite_true, mul_one, abs_mul, abs_of_nonneg hW] using h.2.1
  · simpa only [Bool.false_eq_true, ite_false, ite_true, mul_assoc, abs_mul, abs_of_nonneg hW] using h.2.2.1
  · simpa only [ite_true, mul_assoc, abs_mul, abs_of_nonneg hW] using h.2.2.2

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

private theorem n07a_actualPrincipal_from_divided_rows
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (u ur uθ urr urθ uθθ : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) (j l : ℕ)
    (hb : n07aAngularBand m hlen j u = u)
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrr : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    {κ M : ℝ} (hM : 0 ≤ M)
    (hrows : ∀ (i : Fin 3) sine x, x ∈ Ioo (0 : ℝ) 1 → ∀ a b : ℕ, a + b ≤ 1 →
      |κ * n07aTrigMatrixEntry sine
        (n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) a b x) l j| ≤ M) :
    ‖κ • n07aCanonicalUnitMode hlen
      (n07aRelativePrincipalJet href hcur z hz m hlen ur uθ urr urθ uθθ) l‖ ≤
      14 * (1 + (K.right m - K.left m)) ^ 6 * M *
        Real.sqrt (n07aScaledModeEnergy (K.right m - K.left m) (2 * (j : ℝ))
          (n07aCanonicalUnitMode hlen u j) (n07aCanonicalUnitMode hlen ur j)
          (n07aCanonicalUnitMode hlen urr j)) := by
  apply n07a_principalMode_bound hlen
    (n07aActualPrincipalDifference href hcur z hz m hlen)
    u ur uθ urr urθ uθθ hu j l hb hr hθ hrr hrθ hθθ hM
  · intro i sine x hx
    rw [n07a_actualPrincipal_value_matrix h01 h04 href hcur hz hm hlen i sine hx]
    have hg : |κ * n07aTrigMatrixEntry sine
        (fun θ => n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) (x, θ)) l j| ≤ M :=
      hrows i sine x hx 0 0 (by norm_num)
    have hw : 0 ≤ (K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg (cylinderWeight_nonneg (Ioo_subset_Icc_self hx)) _)
    calc
      _ = ((K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3) *
          |κ * n07aTrigMatrixEntry sine
          (fun θ => n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) (x, θ)) l j| := by
        rw [mul_left_comm κ, abs_mul, abs_of_nonneg hw]
      _ ≤ ((K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3) * M :=
        mul_le_mul_of_nonneg_left hg hw
      _ = _ := by ring
  · intro i sine x hx
    exact (n07a_actualPrincipal_normal_matrix_bound h01 h04 href hcur hz hm hlen i sine hx hM l j
      (hrows i sine x hx 0 0 (by norm_num)) (hrows i sine x hx 1 0 (by norm_num))).trans_eq (by ring)
  · intro i sine x hx
    rw [n07a_actualPrincipal_angular_matrix h01 h04 href hcur hz hm hlen i sine hx]
    have hw : 0 ≤ (K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg (cylinderWeight_nonneg (Ioo_subset_Icc_self hx)) _)
    calc
      _ = ((K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3) *
          |κ * n07aTrigMatrixEntry sine
          (n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) 0 1 x) l j| := by
        rw [mul_left_comm κ, abs_mul, abs_of_nonneg hw]
      _ ≤ ((K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3) * M :=
        mul_le_mul_of_nonneg_left (hrows i sine x hx 0 1 (by norm_num)) hw
      _ = _ := by ring

theorem n07a_actualPrincipal_block_bound
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε), ∀ m, K.positive m = true →
      ∀ hlen : K.left m < K.right m,
      ∀ u ur uθ urr urθ uθθ : CanonicalL2 S K m,
      n07aAngularReflection m u = u → ∀ j l : ℕ,
      n07aAngularBand m hlen j u = u →
      N07aWeakCanonicalMixedDerivative S K m u ur 1 0 →
      N07aWeakCanonicalMixedDerivative S K m u uθ 0 1 →
      N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 →
      N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1 →
      N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1 → ∀ commute : Bool,
      ‖(((1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s) *
          (if commute then ((l : ℝ) - j) else 1)) •
        n07aCanonicalUnitMode hlen
          (n07aRelativePrincipalJet href hcur z hz m hlen ur uθ urr urθ uθθ) l‖ ≤
        112 * (1 + (K.right m - K.left m)) ^ 6 * n07aDifferenceBlockBudget T S K d s B z m *
          n07aAngularTail ((j : ℤ) - l) *
          Real.sqrt (n07aScaledModeEnergy (K.right m - K.left m) (2 * (j : ℝ))
            (n07aCanonicalUnitMode hlen u j) (n07aCanonicalUnitMode hlen ur j)
            (n07aCanonicalUnitMode hlen urr j)) := by
  let estimates := n07a_actualDifference_jet_block_bounds href hcur
  let d : ℕ := estimates.choose
  refine ⟨d, fun s => ?_⟩
  let B : ℝ := (estimates.choose_spec s).choose
  have hB : 0 < B := (estimates.choose_spec s).choose_spec.1
  have hbnd := (estimates.choose_spec s).choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro z hz m hm hlen u ur uθ urr urθ uθθ hu j l hband hr hθ hrr hrθ hθθ commute
  let W := (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s
  let M := 8 * n07aDifferenceBlockBudget T S K d s B z m * n07aAngularTail ((j : ℤ) - l)
  let κ := W * (if commute then ((l : ℝ) - j) else 1)
  have hW : 0 ≤ W := by positivity
  have hM : 0 ≤ M :=
    (mul_nonneg hW (abs_nonneg _)).trans
      (hbnd z hz m .dividedA (1 / 2) (by norm_num) 0 0 (by norm_num) l j).1
  have hrows (i : Fin 3) (sine : Bool) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
      (a b : ℕ) (hab : a + b ≤ 1) :
      |κ * n07aTrigMatrixEntry sine
        (n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) a b x) l j| ≤ M := by
    exact n07a_matrix_scalar_four_bounds hW
      (hbnd z hz m (n07aCubicDividedAtom i) x hx a b hab l j) commute sine
  have h := n07a_actualPrincipal_from_divided_rows h01 h04 href hcur hz hm hlen
    u ur uθ urr urθ uθθ hu j l hband hr hθ hrr hrθ hθθ hM hrows
  exact h.trans_eq (by dsimp only [M]; ring)

end ContinuousFlexibility.Analysis
