import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison
import ContinuousFlexibility.Analysis.N01cMaterialAbsorption
import ContinuousFlexibility.Analysis.MaterialSampleCofinite

/-!
# Exact material weights under a bounded sample-index shift

The endpoint comparison already preserves the height exponent. On the
remaining compact middle, only finitely many target cells occur, and a
bounded index shift permits only finitely many source cells. Compactness
therefore supplies the missing global constant. The index association is
an explicit premise; no control interval is silently identified with a cell.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

/-- Global shifted-sample comparison with the original height exponent. -/
theorem materialSample_weight_bound_sameExponent
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (γ α : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (i j : ℕ) (r : ℝ),
      r ∈ D.cells j → |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B →
      T.H (T.sample i) ^ γ * T.E0 (T.sample j) ^ α ≤
        C * T.H r ^ γ * T.E0 r ^ K := by
  classical
  obtain ⟨δ, K, hδ, hK, hnear⟩ :=
    materialSample_endpoint_weight_bound_sameExponent hT hRef γ α hB
  obtain ⟨_, hbounds⟩ := hRef
  have hpart : RadialPartition D := hbounds.2.1
  have hcore (j : ℕ) (r : ℝ) (hr : r ∈ D.cells j) : r ∈ Ioo D.a D.b :=
    hpart.2.2.2.1 j hr
  have hsample (j : ℕ) : T.sample j ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hpart j
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : IsCompact middle := isCompact_Icc
  have hmiddleCore : middle ⊆ Ioo D.a D.b :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfiniteJ : {j : ℕ | (D.cells j ∩ middle).Nonempty}.Finite :=
    hbounds.2.2.2.2.2.1 middle hmiddle hmiddleCore
  let J : Finset ℕ := hfiniteJ.toFinset
  let maxIndex : ℕ := ∑ j ∈ J, D.cellIndex j
  obtain ⟨N, hN⟩ := exists_nat_ge B
  have hfiniteI : {i : ℕ | D.cellIndex i ≤ maxIndex + N}.Finite :=
    hbounds.2.2.2.2.1 (maxIndex + N)
  let I : Finset ℕ := hfiniteI.toFinset
  have source_mem (i j : ℕ) (hj : j ∈ J)
      (hij : |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B) : i ∈ I := by
    apply hfiniteI.mem_toFinset.mpr
    have hjBound : D.cellIndex j ≤ maxIndex :=
      Finset.single_le_sum (fun k _ => Nat.zero_le (D.cellIndex k)) hj
    have hjReal : (D.cellIndex j : ℝ) ≤ (maxIndex : ℝ) := by exact_mod_cast hjBound
    have hiReal : (D.cellIndex i : ℝ) ≤ (maxIndex : ℝ) + (N : ℝ) := by
      linarith only [(abs_le.mp hij).2, hjReal, hN]
    exact_mod_cast hiReal
  let V : ℝ → ℝ := fun r => T.H r ^ γ * T.E0 r ^ K
  have hVpos (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < V r :=
    mul_pos (Real.rpow_pos_of_pos (hT.2.1 r hr).2.1 γ)
      (Real.rpow_pos_of_pos (hT.2.1 r hr).2.2.1 K)
  have hH := (hT.1 T.H (by simp)).rpow_const_of_ne
    (fun r hr => (hT.2.1 r hr).2.1.ne') (p := γ)
  have hE := (hT.1 T.E0 (by simp)).rpow_const_of_ne
    (fun r hr => (hT.2.1 r hr).2.2.1.ne') (p := K)
  have hVc : ContinuousOn V (Ioo D.a D.b) := (hH.mul hE).continuousOn
  have hVinv : ContinuousOn (fun r => (V r)⁻¹) (Ioo D.a D.b) :=
    hVc.inv₀ (fun r hr => (hVpos r hr).ne')
  obtain ⟨Q₀, hQ₀⟩ := hmiddle.bddAbove_image (hVinv.mono hmiddleCore)
  let Q : ℝ := max 1 Q₀
  have hQ : 0 ≤ Q := zero_le_one.trans (le_max_left _ _)
  have hQbound (r : ℝ) (hr : r ∈ middle) : (V r)⁻¹ ≤ Q :=
    (hQ₀ ⟨r, hr, rfl⟩).trans (le_max_right _ _)
  let R : ℝ := ∑ i ∈ I, T.H (T.sample i) ^ γ
  let W : ℝ := ∑ j ∈ J, T.E0 (T.sample j) ^ α
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (hT.2.1 _ (hsample i)).2.1.le γ
  have hW : 0 ≤ W := Finset.sum_nonneg fun j _ =>
    Real.rpow_nonneg (hT.2.1 _ (hsample j)).2.2.1.le α
  let C : ℝ := 1 + R * W * Q
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    linarith only [mul_nonneg (mul_nonneg hR hW) hQ]
  refine ⟨C, K, zero_lt_one.trans_le hC1, hK, fun i j r hr hij => ?_⟩
  have hrCore := hcore j r hr
  suffices h : T.H (T.sample i) ^ γ * T.E0 (T.sample j) ^ α ≤ C * V r by
    simpa only [V, mul_assoc] using h
  by_cases hcollar : endpointDistance D r < δ
  · exact (hnear i j r hrCore hr hij hcollar).trans
      (by simpa only [one_mul, V] using
        mul_le_mul_of_nonneg_right hC1 (hVpos r hrCore).le)
  · have hd : δ ≤ endpointDistance D r := le_of_not_gt hcollar
    have hrMiddle : r ∈ middle := by
      have hh := le_min_iff.mp hd
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    have hj : j ∈ J := hfiniteJ.mem_toFinset.mpr ⟨r, hr, hrMiddle⟩
    have hi : i ∈ I := source_mem i j hj hij
    have hiR : T.H (T.sample i) ^ γ ≤ R :=
      Finset.single_le_sum (fun k _ =>
        Real.rpow_nonneg (hT.2.1 _ (hsample k)).2.1.le γ) hi
    have hjW : T.E0 (T.sample j) ^ α ≤ W :=
      Finset.single_le_sum (fun k _ =>
        Real.rpow_nonneg (hT.2.1 _ (hsample k)).2.2.1.le α) hj
    apply (div_le_iff₀ (hVpos r hrCore)).mp
    calc
      (T.H (T.sample i) ^ γ * T.E0 (T.sample j) ^ α) / V r =
          (T.H (T.sample i) ^ γ * T.E0 (T.sample j) ^ α) * (V r)⁻¹ :=
        div_eq_mul_inv _ _
      _ ≤ (R * W) * Q :=
        mul_le_mul
          (mul_le_mul hiR hjW
            (Real.rpow_nonneg (hT.2.1 _ (hsample j)).2.2.1.le α) hR)
          (hQbound r hrMiddle) (inv_pos.mpr (hVpos r hrCore)).le (mul_nonneg hR hW)
      _ ≤ C := by dsimp only [C]; linarith

/-- A positive height exponent absorbs every fixed coefficient power,
also when the two sample indices differ by a bounded amount. -/
theorem materialSample_shifted_weight_bounded
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ : ℝ} (hγ : 0 < γ) (α : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 < M ∧ ∀ i j : ℕ,
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B →
      T.H (T.sample i) ^ γ * T.E0 (T.sample j) ^ α ≤ M := by
  obtain ⟨C, K, hC, _, hcompare⟩ :=
    materialSample_weight_bound_sameExponent hT hRef γ α hB
  obtain ⟨M, hM, hbound⟩ := materialHeight_E0_weight_bounded hT hγ K
  have hsampleCell : ∀ j, T.sample j ∈ D.cells j := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  obtain ⟨_, hbounds⟩ := hRef
  refine ⟨C * M, mul_pos hC hM, fun i j hij => ?_⟩
  calc
    _ ≤ C * T.H (T.sample j) ^ γ * T.E0 (T.sample j) ^ K :=
      hcompare i j (T.sample j) (hsampleCell j) hij
    _ = C * (T.H (T.sample j) ^ γ * T.E0 (T.sample j) ^ K) := mul_assoc _ _ _
    _ ≤ C * M := mul_le_mul_of_nonneg_left
      (hbound _ (materialSample_mem_radialCore hT hbounds.2.1 j)) hC.le

end ContinuousFlexibility.Statements
