module

public import ContinuousFlexibility.Radial.ScaleSlowVariation
public import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# A finite floor on the radial cell indices

Replacing index n by max n N changes only finitely many labels.  The
Gaussian and profile estimates survive with enlarged constants, while
the actual profile, cells, localizers and trace circles stay unchanged.
This permits one common label on a prescribed compact middle region.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

def floorReferenceIndex (D : ReferenceData) (N : ℕ) : ReferenceData :=
  { D with cellIndex := fun m => max (D.cellIndex m) N }

private theorem indexFloor_gaussian (n N : ℕ) :
    exp (-(n : ℝ) ^ 2) ≤
      exp ((N : ℝ) ^ 2) * exp (-((max n N : ℕ) : ℝ) ^ 2) := by
  rcases le_total n N with h | h
  · rw [max_eq_right h, ← exp_add, add_neg_cancel, exp_zero]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (n : ℝ)))
  · rw [max_eq_left h]
    exact le_mul_of_one_le_left (exp_pos _).le
      (one_le_exp_iff.mpr (sq_nonneg (N : ℝ)))

private theorem indexFloor_gaussian_mul {C C' : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hC' : exp ((N : ℝ) ^ 2) * C ≤ C') (n : ℕ) :
    C * exp (-(n : ℝ) ^ 2) ≤
      C' * exp (-((max n N : ℕ) : ℝ) ^ 2) := by
  calc
    _ ≤ C * (exp ((N : ℝ) ^ 2) * exp (-((max n N : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (indexFloor_gaussian n N) hC
    _ = (exp ((N : ℝ) ^ 2) * C) * exp (-((max n N : ℕ) : ℝ) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC' (exp_pos _).le

private theorem indexFloor_inverse_power {C C' : ℝ} (N n : ℕ)
    (hC : 0 ≤ C) (hCC' : C ≤ C') :
    radialE n ^ C ≤ radialE (max n N) ^ C' := by
  rw [radialE, radialE, Real.rpow_def_of_pos (exp_pos _),
    Real.rpow_def_of_pos (exp_pos _), log_exp, log_exp]
  exact exp_le_exp.mpr (mul_le_mul (radialQ_monotone (Nat.le_max_left n N))
    hCC' hC (radialQ_nonneg _))

private theorem indexFloor_negative_power {K : ℝ} (N n : ℕ) (hK : 0 ≤ K) :
    radialE (max n N) ^ (-K) ≤ radialE n ^ (-K) := by
  rw [radialE, radialE, Real.rpow_def_of_pos (exp_pos _),
    Real.rpow_def_of_pos (exp_pos _), log_exp, log_exp]
  exact exp_le_exp.mpr (mul_le_mul_of_nonpos_right
    (radialQ_monotone (Nat.le_max_left n N)) (neg_nonpos.mpr hK))

theorem isAccumulatingProfile_floorReferenceIndex {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (N : ℕ) (hN : 1 ≤ N) :
    IsAccumulatingProfile (floorReferenceIndex D N) := by
  rcases hD with ⟨C, hGeo, hPart, hC, hNE, hFin, hLoc, hDist,
    hLower, hJet, hInvJet, hWidth, hAbsorb, hTrace⟩
  let P : ℝ := (N : ℝ) ^ (5 / 2 : ℝ)
  let C' : ℕ → ℝ := fun s => (exp ((N : ℝ) ^ 2) + 1) * C s + P + 1
  have hP : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hC' (s : ℕ) : 0 < C' s := by
    have hp : 0 < (exp ((N : ℝ) ^ 2) + 1) * C s :=
      mul_pos (by positivity) (hC s)
    dsimp only [C']
    linarith only [hp, hP]
  have hdelta (s : ℕ) : P ≤ C' s - C s := by
    have hp := mul_nonneg (exp_pos ((N : ℝ) ^ 2)).le (hC s).le
    dsimp only [C']
    nlinarith only [hp]
  have hCC' (s : ℕ) : C s ≤ C' s := by linarith only [hdelta s, hP]
  have hEC' (s : ℕ) : exp ((N : ℝ) ^ 2) * C s ≤ C' s := by
    dsimp only [C']
    nlinarith only [hC s, hP]
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN₂ : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN₁]
  refine ⟨C', hGeo, hPart, hC', hNE, ?_, hLoc, ?_, ?_, ?_, ?_, ?_, hAbsorb, ?_⟩
  · intro M
    apply (hFin M).subset
    intro m hm
    change max (D.cellIndex m) N ≤ M at hm
    exact (Nat.le_max_left _ _).trans hm
  · intro m r hr
    obtain ⟨hlo, hhi⟩ := hDist m r hr
    refine ⟨?_, ?_⟩
    · change (C' 0)⁻¹ * exp (-(((max (D.cellIndex m) N : ℕ) : ℝ) + 1) ^ 2) ≤
        min (r - D.a) (D.b - r)
      have hcast : (D.cellIndex m : ℝ) ≤ (max (D.cellIndex m) N : ℕ) := by
        exact_mod_cast Nat.le_max_left (D.cellIndex m) N
      have hs : ((D.cellIndex m : ℝ) + 1) ^ 2 ≤
          (((max (D.cellIndex m) N : ℕ) : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hcast]) 2
      exact (mul_le_mul (inv_anti₀ (hC 0) (hCC' 0))
        (exp_le_exp.mpr (neg_le_neg hs)) (exp_pos _).le
        (inv_nonneg.mpr (hC 0).le)).trans hlo
    · exact hhi.trans (indexFloor_gaussian_mul N (hC 0).le (hEC' 0) (D.cellIndex m))
  · intro m r hr
    have hcast : (D.cellIndex m : ℝ) ≤ (max (D.cellIndex m) N : ℕ) := by
      exact_mod_cast Nat.le_max_left (D.cellIndex m) N
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg (D.cellIndex m)) hcast
      (by norm_num : (0 : ℝ) ≤ 5 / 2)
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (D.cellIndex m)) hcast 2
    have hc := mul_le_mul (hCC' 0) hs (sq_nonneg (D.cellIndex m : ℝ)) (hC' 0).le
    apply le_trans _ (hLower m r hr)
    apply exp_le_exp.mpr
    change -(((max (D.cellIndex m) N : ℕ) : ℝ) ^ (5 / 2 : ℝ)) -
        C' 0 * ((max (D.cellIndex m) N : ℕ) : ℝ) ^ 2 ≤ _
    linarith only [hp, hc]
  · intro m r hr s
    have h := hJet m r hr s
    change |radialJet s D.w r| ≤ C' s *
      exp (-(((max (D.cellIndex m) N : ℕ) : ℝ) ^ (5 / 2 : ℝ)) +
        C' s * ((max (D.cellIndex m) N : ℕ) : ℝ) ^ 2)
    by_cases hn : N ≤ D.cellIndex m
    · rw [max_eq_left hn]
      apply h.trans
      apply mul_le_mul (hCC' s) _ (exp_pos _).le (hC' s).le
      apply exp_le_exp.mpr
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right (hCC' s) (sq_nonneg (D.cellIndex m : ℝ)))
    · have hn' : D.cellIndex m ≤ N := (lt_of_not_ge hn).le
      rw [max_eq_right hn']
      have hcast : (D.cellIndex m : ℝ) ≤ N := by exact_mod_cast hn'
      have hs := pow_le_pow_left₀ (Nat.cast_nonneg (D.cellIndex m)) hcast 2
      have hp : 0 ≤ (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg (D.cellIndex m)) _
      have hmul := mul_le_mul_of_nonneg_left hs (hC s).le
      have hpay : P ≤ (C' s - C s) * (N : ℝ) ^ 2 :=
        (hdelta s).trans (le_mul_of_one_le_right
          (sub_nonneg.mpr (hCC' s)) hN₂)
      apply h.trans
      apply mul_le_mul (hCC' s) _ (exp_pos _).le (hC' s).le
      apply exp_le_exp.mpr
      change -(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) +
          C s * (D.cellIndex m : ℝ) ^ 2 ≤ -P + C' s * (N : ℝ) ^ 2
      nlinarith only [hp, hmul, hpay]
  · intro m r hr s
    apply (hInvJet m r hr s).trans
    exact mul_le_mul (hCC' s)
      (indexFloor_inverse_power N (D.cellIndex m) (hC s).le (hCC' s))
      (Real.rpow_nonneg (exp_pos _).le _) (hC' s).le
  · intro m
    obtain ⟨l, h, hsub, hlen⟩ := hWidth m
    exact ⟨l, h, hsub, hlen.trans
      (indexFloor_gaussian_mul N (hC 0).le (hEC' 0) (D.cellIndex m))⟩
  · obtain ⟨centers, widths, K, hK, hsc, hdisj⟩ := hTrace
    refine ⟨centers, widths, K, hK, ?_, hdisj⟩
    intro m
    obtain ⟨hcenter, hpos, hbound, hinc⟩ := hsc m
    refine ⟨hcenter, hpos, ?_, hinc⟩
    exact (mul_le_mul_of_nonneg_left
      (indexFloor_negative_power N (D.cellIndex m) hK.le)
      (inv_nonneg.mpr hK.le)).trans hbound

/-- A finite floor makes all cells meeting a prescribed compact middle
carry one common label. No cell or localizer is replaced. -/
theorem exists_floorReferenceIndex_compact_cover {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {K : Set ℝ}
    (hK : IsCompact K) (hKcore : K ⊆ radialCore D) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ r ∈ K, ∃ m,
      (floorReferenceIndex D N).cellIndex m = N ∧
      r ∈ (floorReferenceIndex D N).cells m := by
  classical
  obtain ⟨C, hbounds⟩ := hD
  have hlocal := hbounds.2.2.2.2.2.1 K hK hKcore
  obtain ⟨M, hM⟩ := (hlocal.image D.cellIndex).bddAbove
  refine ⟨max M 1, Nat.le_max_right _ _, ?_⟩
  intro r hr
  have hpart := hbounds.2.1
  have hnonzero : ∃ m, D.localizer m r ≠ 0 := by
    by_contra h
    push_neg at h
    have hsum := (hpart.2.2.2.2.1 r (hKcore hr)).2
    simp only [h, tsum_zero] at hsum
    norm_num at hsum
  obtain ⟨m, hm⟩ := hnonzero
  have hmem := hpart.2.2.1 m hm
  have hidx : D.cellIndex m ≤ M := hM ⟨m, ⟨r, hmem, hr⟩, rfl⟩
  refine ⟨m, ?_, hmem⟩
  exact max_eq_right (hidx.trans (Nat.le_max_left _ _))

end ContinuousFlexibility.Radial
