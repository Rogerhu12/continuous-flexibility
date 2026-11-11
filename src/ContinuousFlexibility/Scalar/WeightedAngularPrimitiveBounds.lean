import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveL2

/-!
# Weighted membership and fixed-loss bounds for angular primitives

The radial weights commute with the primitive. Each weighted output jet is
therefore either a bounded angular integral of the corresponding input jet,
or an input jet with one fewer angular derivative. Summing these estimates
gives a bound at the same physical order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff Topology ENNReal BigOperators

theorem contDiff_weightedPhysicalJet
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (a b c : ℕ) : ContDiff ℝ ∞ (weightedPhysicalJet T γ a b c f) := by
  have hdata := hT
  obtain ⟨hsmooth, _, _, _, _, _, hradius, hinside, _⟩ := hdata
  have hM : ContDiff ℝ ∞ (fun p : PolarPoint => T.M (T.radius p.1)) :=
    (hsmooth T.M (by simp)).comp_contDiff (hradius.comp contDiff_fst)
      (fun p => (hinside p.1).1)
  exact (hM.pow c).mul (contDiff_mixedDerivative (contDiff_materialPullback hT hf) a b)

theorem scalarAngularPrimitive_weightedJets_memLp
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiff ℝ ∞ f)
    (hjets : ∀ a b c : ℕ, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure) :
    ∀ a b c : ℕ, MemLp (weightedPhysicalJet T γ a b c (scalarAngularPrimitive f))
      2 materialCylinderMeasure := by
  intro a b c
  cases b with
  | zero =>
      rw [weightedPhysicalJet_scalarAngularPrimitive_zero hT hf]
      exact (scalarAngularPrimitive_memLp_and_norm_le
        (contDiff_weightedPhysicalJet hT hf.contDiffOn a 0 c) (hjets a 0 c)).1
  | succ b =>
      rw [weightedPhysicalJet_scalarAngularPrimitive_succ hT hf]
      exact hjets a b c

/-- The primitive of an actual odd weighted field belongs to the actual even
height space, with exactly the same weight exponent. -/
theorem scalarAngularPrimitive_heightMember
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiff ℝ ∞ f)
    (hodd : ∀ r θ, f (r, -θ) = -f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0)
    (hjets : ∀ a b c : ℕ, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure) :
    HeightMember D T γ (scalarAngularPrimitive f) := by
  exact ⟨(scalarAngularPrimitive_contDiff hf).contDiffOn,
    scalarAngularPrimitive_even hodd,
    scalarAngularPrimitive_periodic hf.continuous hodd hperiod,
    scalarAngularPrimitive_eq_zero_outside hzero,
    scalarAngularPrimitive_weightedJets_memLp hT hf hjets⟩

private theorem scalar_physicalJet_norm_le_of_memLp
    {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hjets : ∀ a b c : ℕ, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure)
    {a b c s : ℕ} (h : a + b + c ≤ s) :
    (eLpNorm (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure).toReal ≤
      physicalNorm T γ s f := by
  classical
  let j : JetIndex s :=
    ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using h⟩
  let N (i : JetIndex s) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (i.val 0).val (i.val 1).val (i.val 2).val f)
      2 materialCylinderMeasure
  have hN (i : JetIndex s) : N i ≠ (⊤ : ℝ≥0∞) :=
    (hjets (i.val 0).val (i.val 1).val (i.val 2).val).eLpNorm_ne_top
  have hsum : (∑ i : JetIndex s, N i ^ 2) ≠ (⊤ : ℝ≥0∞) := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ENNReal.pow_ne_top (hN i)
  apply Real.le_sqrt_of_sq_le
  have hle : N j ^ 2 ≤ ∑ i : JetIndex s, N i ^ 2 :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)
  simpa only [ENNReal.toReal_pow] using ENNReal.toReal_mono hsum hle

/-- A fixed loss of zero is enough for every physical output order. The
displayed harmless finite-jet count avoids changing the actual norm. -/
theorem scalarAngularPrimitive_physicalNorm_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiff ℝ ∞ f)
    (hjets : ∀ a b c : ℕ, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure)
    (s : ℕ) :
    physicalNorm T γ s (scalarAngularPrimitive f) ≤
      (Real.sqrt (Fintype.card (JetIndex s) : ℝ) * Real.pi) * physicalNorm T γ s f := by
  classical
  let N := physicalNorm T γ s f
  let P (j : JetIndex s) : ℝ≥0∞ := eLpNorm
    (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
      (scalarAngularPrimitive f)) 2 materialCylinderMeasure
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hmem := scalarAngularPrimitive_weightedJets_memLp hT hf hjets
  have hP (j : JetIndex s) : P j ≠ (⊤ : ℝ≥0∞) :=
    (hmem (j.val 0).val (j.val 1).val (j.val 2).val).eLpNorm_ne_top
  have hbound (j : JetIndex s) : (P j).toReal ≤ Real.pi * N := by
    have horder := j.property
    change (eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val
      (j.val 2).val (scalarAngularPrimitive f)) 2 materialCylinderMeasure).toReal ≤ Real.pi * N
    cases hb : (j.val 1).val with
    | zero =>
        rw [weightedPhysicalJet_scalarAngularPrimitive_zero hT hf]
        apply (scalarAngularPrimitive_memLp_and_norm_le
          (contDiff_weightedPhysicalJet hT hf.contDiffOn (j.val 0).val 0 (j.val 2).val)
          (hjets (j.val 0).val 0 (j.val 2).val)).2.trans
        exact mul_le_mul_of_nonneg_left
          (scalar_physicalJet_norm_le_of_memLp hjets (by omega)) Real.pi_pos.le
    | succ b =>
        rw [weightedPhysicalJet_scalarAngularPrimitive_succ hT hf]
        calc
          _ ≤ N := scalar_physicalJet_norm_le_of_memLp hjets (by omega)
          _ ≤ Real.pi * N := le_mul_of_one_le_left hN hπ
  have hsum : (∑ j : JetIndex s, P j ^ 2).toReal ≤
      (Fintype.card (JetIndex s) : ℝ) * (Real.pi * N) ^ 2 := by
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.pow_ne_top (hP j))]
    simp only [ENNReal.toReal_pow]
    calc
      _ ≤ ∑ _ : JetIndex s, (Real.pi * N) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hbound j) 2
      _ = (Fintype.card (JetIndex s) : ℝ) * (Real.pi * N) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change Real.sqrt (∑ j : JetIndex s, P j ^ 2).toReal ≤
    (Real.sqrt (Fintype.card (JetIndex s) : ℝ) * Real.pi) * N
  calc
    _ ≤ Real.sqrt ((Fintype.card (JetIndex s) : ℝ) * (Real.pi * N) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = (Real.sqrt (Fintype.card (JetIndex s) : ℝ) * Real.pi) * N := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg Real.pi_pos.le hN)]
      ring

end ContinuousFlexibility.Statements
