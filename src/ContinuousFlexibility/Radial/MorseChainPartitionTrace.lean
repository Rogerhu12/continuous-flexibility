module

public import ContinuousFlexibility.Radial.MorseChainPartitionBounds
public import ContinuousFlexibility.Radial.MorseChainPartitionData

/-!
# Trace intervals for the actual radial partition

Each trace interval lies strictly between two actual successive seams,
or inside the finite middle gap. The same intervals lie in the actual
windows and have the quantitative widths of the radial contract.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped Topology

private noncomputable def morseTraceTailCenter (T : Statements.MorseChainData)
    (side : Bool) (k : ℕ) : ℝ :=
  morsePartitionOrientation side (morseSeamTraceCenter (morsePartitionSeam T side) k)

private noncomputable def morseTraceTailWidth (T : Statements.MorseChainData)
    (side : Bool) (k : ℕ) : ℝ :=
  morseSeamTraceWidth (morsePartitionSeam T side) k

private noncomputable def morseTraceMiddleCenter (T : Statements.MorseChainData) : ℝ :=
  (-morsePartitionSeam T false 0 + morsePartitionSeam T true 0) / 2

private noncomputable def morseTraceMiddleWidth (T : Statements.MorseChainData) : ℝ :=
  morsePartitionMiddleSpan T / 8

private theorem morseTrace_tail_closed {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (morseTraceTailCenter T side k - morseTraceTailWidth T side k)
      (morseTraceTailCenter T side k + morseTraceTailWidth T side k)) :
    morsePartitionOrientation side x ∈
      Ioo (morsePartitionSeam T side k) (morsePartitionSeam T side (k + 1)) ∧
    x ∈ morsePartitionTailCell G side k := by
  let s := morsePartitionSeam T
  let m := morsePartitionMiddleSpan T
  obtain ⟨hRm, hLm, hRt, hLt, hRc, hLc, hm⟩ := morsePartitionSeam_data G
  have hstrict (side : Bool) : s side k < s side (k + 1) := by
    cases side
    · exact hLm (Nat.lt_succ_self k)
    · exact hRm (Nat.lt_succ_self k)
  have hy : morsePartitionOrientation side x ∈
      Ioo (s side k) (s side (k + 1)) := by
    cases side
    · change x ∈ Icc (-((s false k + s false (k + 1)) / 2) -
        (s false (k + 1) - s false k) / 8) (-((s false k + s false (k + 1)) / 2) +
        (s false (k + 1) - s false k) / 8) at hx
      change -x ∈ Ioo (s false k) (s false (k + 1))
      exact ⟨by linarith only [hx.2, hstrict false], by linarith only [hx.1, hstrict false]⟩
    · change x ∈ Icc ((s true k + s true (k + 1)) / 2 -
        (s true (k + 1) - s true k) / 8) ((s true k + s true (k + 1)) / 2 +
        (s true (k + 1) - s true k) / 8) at hx
      change x ∈ Ioo (s true k) (s true (k + 1))
      exact ⟨by linarith only [hx.1, hstrict true], by linarith only [hx.2, hstrict true]⟩
  refine ⟨hy, ?_⟩
  cases side
  · exact (morseSeamOverlap_geometry (middle := m) hm hLm hLc hLt).2.2.1 k
      (Ioo_subset_Icc_self hy)
  · exact (morseSeamOverlap_geometry (middle := m) hm hRm hRc hRt).2.2.1 k
      (Ioo_subset_Icc_self hy)

private theorem morseTrace_middle_closed {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {x : ℝ}
    (hx : x ∈ Icc (morseTraceMiddleCenter T - morseTraceMiddleWidth T)
      (morseTraceMiddleCenter T + morseTraceMiddleWidth T)) :
    x ∈ Ioo (-morsePartitionSeam T false 0) (morsePartitionSeam T true 0) ∧
    x ∈ morsePartitionMiddleCell G := by
  let l := morsePartitionSeam T false
  let r := morsePartitionSeam T true
  let m := morsePartitionMiddleSpan T
  obtain ⟨hRm, hLm, _, _, hRc, hLc, hm⟩ := morsePartitionSeam_data G
  change 0 < r 0 + l 0 at hm
  change x ∈ Icc ((-l 0 + r 0) / 2 - (r 0 + l 0) / 8)
    ((-l 0 + r 0) / 2 + (r 0 + l 0) / 8) at hx
  have hi : x ∈ Ioo (-l 0) (r 0) :=
    ⟨by linarith only [hx.1, hm], by linarith only [hx.2, hm]⟩
  refine ⟨hi, ?_⟩
  have hl : 0 < morsePartitionWidth G false 0 :=
    (morseSeamWidth_bounds (middle := m) hm hLm hLc 0).1
  have hr : 0 < morsePartitionWidth G true 0 :=
    (morseSeamWidth_bounds (middle := m) hm hRm hRc 0).1
  change x ∈ Ioo (-(l 0 + morsePartitionWidth G false 0)) (r 0 + morsePartitionWidth G true 0)
  exact ⟨by linarith only [hi.1, hl], by linarith only [hi.2, hr]⟩

private theorem morseTrace_radialE_neg_le_exp {n : ℕ} (hn : 1 ≤ n)
    {K : ℝ} (hK : 1 ≤ K) :
    Statements.radialE n ^ (-K) ≤ exp (-(n : ℝ) ^ 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) ≤ n := zero_le_one.trans hnR
  have hPow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (5 / 2 : ℝ) := by
    calc
      (n : ℝ) ^ 2 = (n : ℝ) ^ ((2 : ℕ) : ℝ) := (rpow_natCast _ _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have hLog : 1 ≤ log (exp 1 + (n : ℝ)) := by
    calc
      1 = log (exp 1) := (log_exp _).symm
      _ ≤ _ := log_le_log (exp_pos _) (le_add_of_nonneg_right hn₀)
  have hQ : (n : ℝ) ^ 2 ≤ Statements.radialQ n := by
    exact hPow.trans (le_mul_of_one_le_right (rpow_nonneg hn₀ _) hLog)
  have hKQ : (n : ℝ) ^ 2 ≤ K * Statements.radialQ n :=
    hQ.trans (le_mul_of_one_le_left ((sq_nonneg _).trans hQ) hK)
  rw [Statements.radialE, ← exp_mul]
  apply exp_le_exp.mpr
  linarith only [hKQ, show Statements.radialQ n * (-K) = -(K * Statements.radialQ n) by ring]


private theorem morseTrace_tail_disjoint {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (p q : Bool × ℕ) (hpq : p ≠ q) :
    Disjoint
      (Ioo (morseTraceTailCenter T p.1 p.2 - morseTraceTailWidth T p.1 p.2)
        (morseTraceTailCenter T p.1 p.2 + morseTraceTailWidth T p.1 p.2))
      (Ioo (morseTraceTailCenter T q.1 q.2 - morseTraceTailWidth T q.1 q.2)
        (morseTraceTailCenter T q.1 q.2 + morseTraceTailWidth T q.1 q.2)) := by
  obtain ⟨hR, hL, _, _, _, _, hm⟩ := morsePartitionSeam_data G
  change 0 < morsePartitionSeam T true 0 + morsePartitionSeam T false 0 at hm
  have hMono (side : Bool) : StrictMono (morsePartitionSeam T side) := by
    cases side
    · exact hL
    · exact hR
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases p with ⟨s, k⟩
  rcases q with ⟨t, j⟩
  have hx' := (morseTrace_tail_closed G s k (Ioo_subset_Icc_self hx)).1
  have hy' := (morseTrace_tail_closed G t j (Ioo_subset_Icc_self hy)).1
  by_cases hst : s = t
  · subst t
    have hkj : k ≠ j := fun h => hpq (congrArg (Prod.mk s) h)
    rcases lt_or_gt_of_ne hkj with h | h
    · exact (not_lt_of_ge ((hMono s).monotone (Nat.succ_le_of_lt h))) (hy'.1.trans hx'.2)
    · exact (not_lt_of_ge ((hMono s).monotone (Nat.succ_le_of_lt h))) (hx'.1.trans hy'.2)
  · cases s <;> cases t
    · exact hst rfl
    · change -x ∈ Ioo (morsePartitionSeam T false k) (morsePartitionSeam T false (k + 1)) at hx'
      change x ∈ Ioo (morsePartitionSeam T true j) (morsePartitionSeam T true (j + 1)) at hy'
      have h0 := hL.monotone (Nat.zero_le k)
      have h1 := hR.monotone (Nat.zero_le j)
      linarith only [hx'.1, hy'.1, h0, h1, hm]
    · change x ∈ Ioo (morsePartitionSeam T true k) (morsePartitionSeam T true (k + 1)) at hx'
      change -x ∈ Ioo (morsePartitionSeam T false j) (morsePartitionSeam T false (j + 1)) at hy'
      have h0 := hR.monotone (Nat.zero_le k)
      have h1 := hL.monotone (Nat.zero_le j)
      linarith only [hx'.1, hy'.1, h0, h1, hm]
    · exact hst rfl

private theorem morseTrace_middle_disjoint {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    Disjoint
      (Ioo (morseTraceMiddleCenter T - morseTraceMiddleWidth T)
        (morseTraceMiddleCenter T + morseTraceMiddleWidth T))
      (Ioo (morseTraceTailCenter T side k - morseTraceTailWidth T side k)
        (morseTraceTailCenter T side k + morseTraceTailWidth T side k)) := by
  obtain ⟨hR, hL, _, _, _, _, _⟩ := morsePartitionSeam_data G
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := (morseTrace_middle_closed G (Ioo_subset_Icc_self hx)).1
  have hy' := (morseTrace_tail_closed G side k (Ioo_subset_Icc_self hy)).1
  cases side
  · change -x ∈ Ioo (morsePartitionSeam T false k) (morsePartitionSeam T false (k + 1)) at hy'
    have h0 := hL.monotone (Nat.zero_le k)
    linarith only [hx'.1, hy'.1, h0]
  · change x ∈ Ioo (morsePartitionSeam T true k) (morsePartitionSeam T true (k + 1)) at hy'
    exact (not_lt_of_ge ((hR.monotone (Nat.zero_le k)).trans hy'.1.le)) hx'.2


private theorem morseTrace_inv_le {t K : ℝ} (ht : 0 < t) (hK : t⁻¹ ≤ K) :
    K⁻¹ ≤ t := by
  simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr ht) hK

/-- A separated quantitative trace for the exact windows of the actual
two-sided Morse chain. The same reference data is used in all clauses. -/
theorem morsePartitionReference_trace {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) :
    Statements.RadialTraceScaffold (morsePartitionReference G w phi chi chiLeft) := by
  let C := morseTwoTailAt (morseTraceMiddleCenter T) (morseTraceTailCenter T)
  let W := morseTwoTailAt (morseTraceMiddleWidth T) (morseTraceTailWidth T)
  let c := G.factorLo * (9 / 10 : ℝ) / 24
  obtain ⟨_, _, _, _, _, _, hm⟩ := morsePartitionSeam_data G
  obtain ⟨_, _, hSeam⟩ := morsePartitionSeam_distance_bounds G
  have hMid : 0 < morseTraceMiddleWidth T := div_pos hm (by norm_num)
  have hc : 0 < c := div_pos (mul_pos G.factorLo_pos (by norm_num)) (by norm_num)
  let K := max 1 (max c⁻¹ (morseTraceMiddleWidth T)⁻¹)
  have hK₁ : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK₁
  have hKc : K⁻¹ ≤ c :=
    morseTrace_inv_le hc ((le_max_left _ _).trans (le_max_right _ _))
  have hKm : K⁻¹ ≤ morseTraceMiddleWidth T :=
    morseTrace_inv_le hMid ((le_max_right _ _).trans (le_max_right _ _))
  have hIdx (k : ℕ) : 1 ≤ T.index + k :=
    (show 1 ≤ 100 by omega).trans (G.start_large.trans (Nat.le_add_right _ _))
  have hTail (side : Bool) (k : ℕ) :
      c * exp (-((T.index + k : ℕ) : ℝ) ^ 2) ≤ morseTraceTailWidth T side k := by
    have h := (hSeam side k).2.2
    change G.factorLo * (9 / 10 : ℝ) * Statements.morseChainA T (T.index + k) ≤
      morsePartitionSeam T side (k + 1) - morsePartitionSeam T side k at h
    have hA := (morseChainA_exp_bounds T (T.index + k) (G.d_exact _)).1
    unfold morseTraceTailWidth morseSeamTraceWidth
    calc
      _ = (G.factorLo * (9 / 10 : ℝ) * (exp (-((T.index + k : ℕ) : ℝ) ^ 2) / 3)) / 8 := by
        dsimp only [c]
        ring
      _ ≤ (G.factorLo * (9 / 10 : ℝ) * Statements.morseChainA T (T.index + k)) / 8 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (mul_nonneg G.factorLo_pos.le (by norm_num))) (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_right h (by norm_num)
  refine ⟨C, W, K, hK, ?_, ?_⟩
  · intro j
    cases j with
    | zero =>
        change morseTraceMiddleCenter T ∈ morsePartitionMiddleCell G ∧
          0 < morseTraceMiddleWidth T ∧
          K⁻¹ * Statements.radialE T.index ^ (-K) ≤ morseTraceMiddleWidth T ∧ _
        have hE : Statements.radialE T.index ^ (-K) ≤ 1 :=
          (morseTrace_radialE_neg_le_exp (by simpa only [Nat.add_zero] using hIdx 0) hK₁).trans
            (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
        have hSub : Icc (morseTraceMiddleCenter T - morseTraceMiddleWidth T)
            (morseTraceMiddleCenter T + morseTraceMiddleWidth T) ⊆ morsePartitionMiddleCell G :=
          fun _ hx => (morseTrace_middle_closed G hx).2
        refine ⟨hSub ⟨sub_le_self _ hMid.le, le_add_of_nonneg_right hMid.le⟩, hMid, ?_, hSub⟩
        exact (mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hK.le)).trans
          ((mul_one _).le.trans hKm)
    | succ j =>
        let p := Equiv.boolProdNatEquivNat.symm j
        let z := morseTraceTailCenter T p.1 p.2
        let h := morseTraceTailWidth T p.1 p.2
        change z ∈ morsePartitionTailCell G p.1 p.2 ∧ 0 < h ∧
          K⁻¹ * Statements.radialE (T.index + p.2) ^ (-K) ≤ h ∧
          Icc (z - h) (z + h) ⊆ morsePartitionTailCell G p.1 p.2
        have hL := hTail p.1 p.2
        have hh : 0 < h := (mul_pos hc (exp_pos _)).trans_le hL
        have hSub : Icc (z - h) (z + h) ⊆ morsePartitionTailCell G p.1 p.2 :=
          fun _ hx => (morseTrace_tail_closed G p.1 p.2 hx).2
        refine ⟨hSub ⟨sub_le_self _ hh.le, le_add_of_nonneg_right hh.le⟩, hh, ?_, hSub⟩
        exact (mul_le_mul_of_nonneg_left (morseTrace_radialE_neg_le_exp (hIdx p.2) hK₁)
          (inv_nonneg.mpr hK.le)).trans
            ((mul_le_mul_of_nonneg_right hKc (exp_pos _).le).trans hL)
  · intro i j hij
    cases i with
    | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ j =>
            let p := Equiv.boolProdNatEquivNat.symm j
            exact morseTrace_middle_disjoint G p.1 p.2
    | succ i =>
        let p := Equiv.boolProdNatEquivNat.symm i
        cases j with
        | zero => exact (morseTrace_middle_disjoint G p.1 p.2).symm
        | succ j =>
            let q := Equiv.boolProdNatEquivNat.symm j
            have hpq : p ≠ q := fun h =>
              hij (congrArg Nat.succ (Equiv.boolProdNatEquivNat.symm.injective h))
            exact morseTrace_tail_disjoint G p q hpq

end ContinuousFlexibility.Radial
