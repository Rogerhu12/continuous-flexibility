import ContinuousFlexibility.Scalar.WeightedCompositionChainBounds
import ContinuousFlexibility.Scalar.WeightedJetNorm

/-!
# The zeroth scalar composition estimate with a common loss

The base and loss are fixed by interpolation before the scalar function,
the low-norm radius, or the output order. The outer radial weight is handled
by its actual finite Leibniz formula. The resulting estimates prove both
membership of the actual composition and its physical-norm Moser bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem weightedComposition_jet_bound_of_diagonal
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hγ : 0 ≤ γ)
    {base loss : ℕ} (hbase : 2 ≤ base)
    (hdiag : (normalizedMaterialJetFamily hT hA).DiagonalEstimate base loss)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (R : ℝ) (hR : 0 ≤ R) (s a b c : ℕ) (horder : a + b + c ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space, A.grading base u ≤ R →
      MemLp (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
        2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
        2 materialCylinderMeasure).toReal ≤ C * A.grading (s + loss) u := by
  classical
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hdata
  have hH (p : PolarPoint) : 0 < T.H (T.radius p.1) := (hpos _ (hinside p.1).1).2.1
  let w : ℝ → ℝ := fun x => T.H (T.radius x) ^ (-γ)
  have hw : ContDiff ℝ ∞ w := contDiff_materialH_rpow hT (-γ)
  choose B hB hBb using fun i : Fin (a + 1) =>
    iteratedDeriv_materialH_rpow_bound hT (-γ) i.val
  let K : Fin (a + 1) → ℝ := fun i => (a.choose i.val : ℝ) * B i
  have hK (i : Fin (a + 1)) : 0 ≤ K i := mul_nonneg (Nat.cast_nonneg _) (hB i)
  let g : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    (a.choose i.val : ℝ) * T.H (T.radius p.1) ^ γ * iteratedDeriv i.val w p.1
  have hg (i : Fin (a + 1)) : AEStronglyMeasurable (g i) materialCylinderMeasure := by
    have hi : ContDiff ℝ ∞ (iteratedDeriv i.val w) := by
      rw [iteratedDeriv_eq_iterate]
      exact hw.iterate_deriv i.val
    have hs : ContDiff ℝ ∞ (fun p : PolarPoint => T.H (T.radius p.1) ^ γ) :=
      (contDiff_materialH_rpow hT γ).comp contDiff_fst
    have hconst : ContDiff ℝ ∞ (fun _ : PolarPoint => (a.choose i.val : ℝ)) := contDiff_const
    exact ((hconst.mul hs).mul (hi.comp contDiff_fst)).continuous.aestronglyMeasurable
  have hcancel (p : PolarPoint) :
      T.H (T.radius p.1) ^ γ * T.H (T.radius p.1) ^ (-γ) = 1 := by
    rw [← Real.rpow_add (hH p), add_neg_cancel, Real.rpow_zero]
  have hgb (i : Fin (a + 1)) (p : PolarPoint) : |g i p| ≤ K i := by
    dsimp only [g, K]
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose i.val)),
      abs_of_pos (Real.rpow_pos_of_pos (hH p) γ)]
    calc
      _ ≤ (a.choose i.val : ℝ) * T.H (T.radius p.1) ^ γ *
          (B i * T.H (T.radius p.1) ^ (-γ)) :=
        mul_le_mul_of_nonneg_left (hBb i p.1)
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hH p).le _))
      _ = ((a.choose i.val : ℝ) * B i) *
          (T.H (T.radius p.1) ^ γ * T.H (T.radius p.1) ^ (-γ)) := by ring
      _ = (a.choose i.val : ℝ) * B i := by rw [hcancel, mul_one]
  have ht (i : Fin (a + 1)) := normalizedCompositionJet_bound hT hA hγ hbase hdiag
    hF hF0 R hR s (a - i.val) b c (by omega)
  choose C hC hCb using ht
  refine ⟨∑ i, K i * C i, Finset.sum_nonneg (fun i _ => mul_nonneg (hK i) (hC i)), ?_⟩
  intro u hu
  let term : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    g i p * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) *
      mixedDerivative (a - i.val) b (fun q => F (A.decode u (T.radius q.1, q.2))) p
  have hterm (i : Fin (a + 1)) := hCb i (g i) (K i) (hK i) (hg i) (hgb i) u hu
  have heq : weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)) =
      ∑ i : Fin (a + 1), term i := by
    funext p
    change T.M (T.radius p.1) ^ c *
      mixedDerivative a b (fun q => w q.1 * F (A.decode u (T.radius q.1, q.2))) p = _
    rw [mixedDerivative_radial_mul hw (hF.comp (decodedMaterialPullback_contDiff hT hA u)),
      Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [term]
    symm
    calc
      _ = T.M (T.radius p.1) ^ c *
          ((a.choose i.val : ℝ) * iteratedDeriv i.val w p.1 *
            mixedDerivative (a - i.val) b
              (fun q => F (A.decode u (T.radius q.1, q.2))) p) *
          (T.H (T.radius p.1) ^ γ * T.H (T.radius p.1) ^ (-γ)) := by
        dsimp only [g]
        ring
      _ = _ := by rw [hcancel, mul_one]
  rw [heq]
  exact scalar_finiteL2_sum_bound term (fun i => K i * C i) (A.grading (s + loss) u)
    (fun i => (hterm i).1) (fun i => (hterm i).2)

/-- One base and loss control every weighted jet of every smooth scalar
composition vanishing at zero. Neither is chosen from the scalar function. -/
theorem exists_weightedComposition_jet_bounds
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
      ∀ R : ℝ, 0 ≤ R → ∀ s a b c : ℕ, a + b + c ≤ s →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space, A.grading base u ≤ R →
        MemLp (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
          2 materialCylinderMeasure ∧
        (eLpNorm (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
          2 materialCylinderMeasure).toReal ≤ C * A.grading (s + loss) u := by
  obtain ⟨base, loss, hbase, hdiag⟩ := MaterialJetFamily.exists_diagonalEstimate
    hT (normalizedMaterialJetFamily hT hA) hinterp
  exact ⟨base, loss, hbase, fun _ hF hF0 R hR s a b c horder =>
    weightedComposition_jet_bound_of_diagonal hT hA hγ.le hbase hdiag hF hF0
      R hR s a b c horder⟩

/-- The literal composition belongs to the literal physical height space. -/
theorem weightedComposition_heightMember
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) (u : A.Space) :
    HeightMember D T γ (fun p => F (A.decode u p)) := by
  have hf := hA.2.2.2.1 u
  refine ⟨hF.comp_contDiffOn hf.1,
    (fun r θ => congrArg F (hf.2.1 r θ)),
    (fun p => congrArg F (hf.2.2.1 p)), ?_, ?_⟩
  · intro p hp
    rw [hf.2.2.2.1 p hp, hF0]
  · obtain ⟨base, loss, _, hbound⟩ := exists_weightedComposition_jet_bounds hT hA hinterp hγ
    intro a b c
    obtain ⟨C, hC, hCb⟩ := hbound F hF hF0 (A.grading base u) (apply_nonneg _ _)
      (a + b + c) a b c le_rfl
    exact (hCb u le_rfl).1

/-- The zeroth Moser estimate has one base and loss before F, R, and s.
The high seminorm enters linearly, with no additive constant. -/
theorem weightedComposition_physicalNorm_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space, A.grading base u ≤ R →
        physicalNorm T γ s (fun p => F (A.decode u p)) ≤ C * A.grading (s + loss) u := by
  classical
  obtain ⟨base, loss, hbase, hbound⟩ := exists_weightedComposition_jet_bounds hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro F hF hF0 R hR s
  have hj (j : JetIndex s) := hbound F hF hF0 R hR s
    (j.val 0).val (j.val 1).val (j.val 2).val j.property
  choose C hC hCb using hj
  let K : ℝ := ∑ j : JetIndex s, C j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, fun u hu => ?_⟩
  have hjet (a b c : ℕ) (horder : a + b + c ≤ s) :
      MemLp (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
        2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
        2 materialCylinderMeasure).toReal ≤ K * A.grading (s + loss) u := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hm : MemLp (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
        2 materialCylinderMeasure := by
      simpa [j] using (hCb j u hu).1
    have hn : (eLpNorm (weightedPhysicalJet T γ a b c (fun p => F (A.decode u p)))
        2 materialCylinderMeasure).toReal ≤ C j * A.grading (s + loss) u := by
      simpa [j] using (hCb j u hu).2
    have hCK : C j ≤ K := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right hCK (apply_nonneg _ _))⟩
  have h := physicalNorm_le_of_weightedJet_bounds
    (T := T) (γ := γ) (s := s) (f := fun p => F (A.decode u p))
    (B := K * A.grading (s + loss) u)
    (mul_nonneg hK (apply_nonneg _ _))
    (fun a b c horder => (hjet a b c horder).1)
    (fun a b c horder => (hjet a b c horder).2)
  exact h.trans_eq (by ring)

end ContinuousFlexibility.Statements
