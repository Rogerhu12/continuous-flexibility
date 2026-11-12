import ContinuousFlexibility.Scalar.WeightedReferenceBounds
import ContinuousFlexibility.Scalar.WeightedMaterialRadiusJets

/-!
# Moving a sample estimate to the actual radial point

The endpoint comparison is made inside the actual reference cell. Compact
local finiteness supplies one constant on the remaining middle interval.
Control interval placement is not involved.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

private theorem coupled_referenceCell_near_bound_global
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {weight : ℕ → ℝ} {γ δ K : ℝ}
    (hweight : ∀ m, 0 ≤ weight m) (hδ : 0 < δ) (hK : 0 < K)
    (hnear : ∀ m r, r ∈ D.cells m → endpointDistance D r < δ →
      weight m ≤ K * T.H r ^ γ) :
    ∃ L : ℝ, 0 < L ∧ ∀ m r, r ∈ D.cells m → weight m ≤ L * T.H r ^ γ := by
  obtain ⟨B, hB⟩ := hD
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hfinite : {m | (D.cells m ∩ middle).Nonempty}.Finite :=
    hB.2.2.2.2.2.1 middle isCompact_Icc hmiddle
  obtain ⟨R, hR⟩ := (hfinite.image weight).bddAbove
  have hc : ContinuousOn (fun r => T.H r ^ (-γ)) middle :=
    (((hT.1 T.H (by simp)).continuousOn).rpow_const
      (fun r hr => Or.inl (hT.2.1 r hr).2.1.ne')).mono hmiddle
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact middle).bddAbove_image hc
  refine ⟨max K (max R 0 * max A 0), hK.trans_le (le_max_left _ _), ?_⟩
  intro m r hrm
  have hr : r ∈ Ioo D.a D.b := hB.2.1.2.2.2.1 m hrm
  have hp : 0 < T.H r := (hT.2.1 r hr).2.1
  by_cases hn : endpointDistance D r < δ
  · exact (hnear m r hrm hn).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hp _).le)
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hn
    have hrmid : r ∈ middle :=
      ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hwm : weight m ≤ max R 0 :=
      (hR ⟨m, ⟨r, hrm, hrmid⟩, rfl⟩).trans (le_max_left _ _)
    have hhm : T.H r ^ (-γ) ≤ max A 0 :=
      (hA ⟨r, hrmid, rfl⟩).trans (le_max_left _ _)
    calc
      weight m = (weight m * T.H r ^ (-γ)) * T.H r ^ γ := by
        rw [mul_assoc, ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ (max R 0 * max A 0) * T.H r ^ γ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hwm hhm (Real.rpow_pos_of_pos hp _).le (le_max_right _ _))
          (Real.rpow_pos_of_pos hp _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hp _).le

/-- Sample weights in the actual reference cell retain a positive fraction
of their height exponent at the evaluation point, uniformly over all cells. -/
theorem coupled_materialSample_point_weight_bound
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A ≤ K * T.H r ^ (γ / 16) := by
  obtain ⟨δ, K, hδ, hK, hb⟩ := materialSample_endpoint_weight_bound hT hD hγ A
    (B := 0) le_rfl
  obtain ⟨B, hB⟩ := hD
  have hsample (m : ℕ) := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hB.2.1 m)
  exact coupled_referenceCell_near_bound_global ⟨B, hB⟩ hT
    (fun m => mul_nonneg (Real.rpow_nonneg (hsample m).2.1.le _)
      (Real.rpow_nonneg (hsample m).2.2.1.le _)) hδ hK
    (fun m r hrm hn => hb m m r (hB.2.1.2.2.2.1 m hrm) hrm
      (by rw [sub_self, abs_zero]) hn)



open Filter
open scoped ContDiff Topology BigOperators

theorem coupled_product_jet_majorant {I : Type*} {U : Set ℝ}
    {f : ℝ → ℝ} {g : I → ℝ → ℝ} {W V : ℝ → ℝ} {P : I → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U)
    (hW : ∀ r ∈ U, 0 ≤ W r) (hV : ∀ r ∈ U, 0 ≤ V r) (hP : ∀ i, 0 ≤ P i)
    (s : ℕ)
    (hbF : ∀ j ≤ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ r ∈ U, |iteratedDeriv j f r| ≤ A * W r)
    (hbG : ∀ j ≤ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ i r, r ∈ U →
      |iteratedDeriv j (g i) r| ≤ A * V r * P i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ U →
      |iteratedDeriv s (fun t => f t * g i t) r| ≤ K * W r * V r * P i := by
  have hA (j : Fin (s + 1)) := hbF j.val (by omega)
  have hB (j : Fin (s + 1)) := hbG (s - j.val) (Nat.sub_le _ _)
  choose A hA hAb using hA
  choose B hB hBb using hB
  let K (j : Fin (s + 1)) : ℝ := (s.choose j.val : ℝ) * A j * B j
  have hK (j : Fin (s + 1)) : 0 ≤ K j :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB j)
  refine ⟨∑ j, K j, Finset.sum_nonneg (fun j _ => hK j), ?_⟩
  intro i r hr
  let term (j : ℕ) : ℝ :=
    (s.choose j : ℝ) * iteratedDeriv j f r * iteratedDeriv (s - j) (g i) r
  have hformula : iteratedDeriv s (fun t => f t * g i t) r =
      ∑ j : Fin (s + 1), term j.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul ((hf.contDiffAt (hU.mem_nhds hr)).of_le (by simp))
      (((hg i).contDiffAt (hU.mem_nhds hr)).of_le (by simp))
  rw [hformula, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  dsimp only [term]
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (s.choose j.val))]
  calc
    _ ≤ (s.choose j.val : ℝ) * (A j * W r) * (B j * V r * P i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hAb j r hr) (Nat.cast_nonneg _))
        (hBb j i r hr) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA j) (hW r hr)))
    _ = K j * W r * V r * P i := by dsimp only [K]; ring


theorem coupled_comp_materialRadius_majorant
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {I : Type*} {f : I → ℝ → ℝ} {N : I → ℝ} {W : ℝ → ℝ}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo D.a D.b))
    (hN : ∀ i, 0 ≤ N i) (hW : ∀ r ∈ Ioo D.a D.b, 0 ≤ W r)
    (n : ℕ) (hb : ∀ j ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv j (f i) r| ≤ C * N i * W r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      |iteratedDeriv n (fun t => f i (T.radius t)) x| ≤ C * N i * W (T.radius x) := by
  classical
  have hradius := hT.2.2.2.2.2.2.1
  have hinside := hT.2.2.2.2.2.2.2.1
  have houter (j : Fin (n + 1)) := hb j.val (by omega)
  have hinner (j : Fin (n + 1)) := iteratedDeriv_materialRadius_bounded hT j.val
  choose A hA hAb using houter
  choose B hB hBb using hinner
  let K : ℝ := ∑ j : Fin (n + 1), A j
  let L : ℝ := 1 + ∑ j : Fin (n + 1), B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hA j)
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith only [Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      hB j)]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLpow (j : ℕ) (hj : 1 ≤ j) : L ≤ L ^ j := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    calc
      L = 1 * L := (one_mul _).symm
      _ ≤ L ^ k * L := mul_le_mul_of_nonneg_right (one_le_pow₀ hL) hL0
      _ = L ^ (k + 1) := (pow_succ _ _).symm
  refine ⟨(n.factorial : ℝ) * K * L ^ n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) (pow_nonneg hL0 _), ?_⟩
  intro i x
  have hr := (hinside x).1
  have hout (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDerivWithin ℝ j (f i) (Ioo D.a D.b) (T.radius x)‖ ≤
        K * N i * W (T.radius x) := by
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioo hr, Real.norm_eq_abs]
    let k : Fin (n + 1) := ⟨j, by omega⟩
    exact (hAb k i _ hr).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ k)) (hN i)) (hW _ hr))
  have hin (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      ‖iteratedFDeriv ℝ j T.radius x‖ ≤ L ^ j := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    let k : Fin (n + 1) := ⟨j, by omega⟩
    have hk : B k ≤ L := by
      have hs := Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ k)
      dsimp only [L]
      linarith only [hs]
    exact (hBb k x).trans (hk.trans (hLpow j hj))
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (g := f i) (f := T.radius) (n := n)
    (t := Ioo D.a D.b) (by
      rintro r ⟨x, rfl⟩
      exact (hinside x).1) isOpen_Ioo.uniqueDiffOn (hf i) hradius (by simp) x hout hin
  have hfinal : |iteratedDeriv n (fun t => f i (T.radius t)) x| ≤
      (n.factorial : ℝ) * (K * N i * W (T.radius x)) * L ^ n := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Function.comp_def] using hcomp
  exact hfinal.trans_eq (by ring)

end ContinuousFlexibility.Statements
