import ContinuousFlexibility.Radial.ReferenceIndexFloor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Compact interior surgery of an accumulating profile

The cells, localizers and trace scaffold are kept literally unchanged.
The modified profile agrees with the original one outside a compact
subset of the open annulus. The local-finiteness clause bounds the
labels of every affected cell. Compactness supplies all finite-order
profile and reciprocal-profile bounds on the surgery region.

The geometric profile clauses (smoothness, positivity, endpoint
flatness and simple critical points) are supplied by the actual gluing.
They do not replace any of the quantitative accumulating clauses.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def replaceReferenceProfile (D : ReferenceData) (w phi : ℝ → ℝ) : ReferenceData :=
  { D with w := w, phi := phi }

private theorem surgeryJet_eq (s : ℕ) (f : ℝ → ℝ) :
    radialJet s f = iteratedDeriv s f := by
  induction s with
  | zero => exact iteratedDeriv_zero.symm
  | succ s ih => rw [radialJet, ih, iteratedDeriv_succ]

private theorem surgery_inverse_jets_continuousOn
    {w : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ U, 0 < w x) (s : ℕ) :
    ContinuousOn (radialJet s (fun x => (w x)⁻¹)) U := by
  rw [surgeryJet_eq]
  have hi : ContDiffOn ℝ ∞ (fun x => (w x)⁻¹) U :=
    hw.contDiffOn.inv (fun x hx => (hpos x hx).ne')
  have hc := hi.continuousOn_iteratedDerivWithin (m := s) (by simp) hU.uniqueDiffOn
  apply hc.congr
  exact (iteratedDerivWithin_of_isOpen hU).symm

/-- Compact profile surgery preserves the quantitative specification when
the existing labels are positive. -/
theorem isAccumulatingProfile_replaceReferenceProfile
    {D : ReferenceData} {w phi : ℝ → ℝ} {K : Set ℝ}
    (hD : IsAccumulatingProfile D) (hIndex : ∀ m, 1 ≤ D.cellIndex m)
    (hNew : RadialProfileGeometry (replaceReferenceProfile D w phi))
    (hK : IsCompact K) (hKcore : K ⊆ radialCore D)
    (hSame : ∀ r ∉ K, w r = D.w r) :
    IsAccumulatingProfile (replaceReferenceProfile D w phi) := by
  classical
  rcases hD with ⟨C, hGeo, hPart, hC, hNE, hFin, hLoc, hDist,
    hLower, hJet, hInvJet, hWidth, hAbsorb, hTrace⟩
  have hw : ContDiff ℝ ∞ w := hNew.2.2.1.1
  have hpos : ∀ r ∈ radialCore D, 0 < w r := hNew.2.2.2.2.1
  have hOpen : IsOpen (radialCore D) := isOpen_Ioo
  have hBounds : ∀ s : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ r ∈ K,
      |radialJet s w r| ≤ M ∧ |radialJet s (fun x => (w x)⁻¹) r| ≤ M := by
    intro s
    have hc : ContinuousOn (radialJet s w) K := by
      rw [surgeryJet_eq]
      exact (hw.continuous_iteratedDeriv s (by simp)).continuousOn
    obtain ⟨Mw, hMw⟩ := hK.exists_bound_of_continuousOn hc
    obtain ⟨Mi, hMi⟩ := hK.exists_bound_of_continuousOn
      ((surgery_inverse_jets_continuousOn hOpen hw hpos s).mono hKcore)
    refine ⟨max 1 (max Mw Mi), le_max_left _ _, ?_⟩
    intro r hr
    constructor
    · exact (by simpa only [Real.norm_eq_abs] using hMw r hr).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact (by simpa only [Real.norm_eq_abs] using hMi r hr).trans
        ((le_max_right _ _).trans (le_max_right _ _))
  choose M hM hMBounds using hBounds
  let F : Finset ℕ := (hLoc K hK hKcore).toFinset
  let N : ℕ := F.sup D.cellIndex
  let P : ℝ := (N : ℝ) ^ (5 / 2 : ℝ)
  have hP : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hAffected (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) (hKr : r ∈ K) :
      D.cellIndex m ≤ N := by
    have hm : m ∈ F := by
      simp only [F, Set.Finite.mem_toFinset]
      exact ⟨r, hr, hKr⟩
    exact Finset.le_sup hm
  let C' : ℕ → ℝ := fun s => 1 + C s + M s * exp P + M s + M 0
  have hMpos (s : ℕ) : 0 < M s := zero_lt_one.trans_le (hM s)
  have hC' (s : ℕ) : 0 < C' s := by
    have ht : 0 < M s * exp P := mul_pos (hMpos s) (exp_pos P)
    dsimp only [C']
    linarith [hC s, hMpos s, hMpos 0]
  have hCC' (s : ℕ) : C s ≤ C' s := by
    dsimp only [C']
    linarith [hMpos s, hMpos 0, mul_nonneg (hMpos s).le (exp_pos P).le]
  have hMC' (s : ℕ) : M s ≤ C' s := by
    dsimp only [C']
    linarith [hC s, hMpos 0, mul_nonneg (hMpos s).le (exp_pos P).le]
  have hM0C' (s : ℕ) : M 0 ≤ C' s := by
    dsimp only [C']
    linarith [hC s, hMpos s, mul_nonneg (hMpos s).le (exp_pos P).le]
  have hME (s : ℕ) : M s * exp P ≤ C' s := by
    dsimp only [C']
    linarith [hC s, hMpos s, hMpos 0]
  have hGerm (r : ℝ) (hr : r ∉ K) : w =ᶠ[𝓝 r] D.w := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hr] with x hx
    exact hSame x hx
  have hE (n : ℕ) : 1 ≤ radialE n :=
    one_le_exp_iff.mpr (radialQ_nonneg n)
  refine ⟨C', hNew, hPart, hC', hNE, hFin, hLoc, ?_, ?_, ?_, ?_, ?_,
    hAbsorb, hTrace⟩
  · intro m r hr
    obtain ⟨hl, hu⟩ := hDist m r hr
    exact ⟨(mul_le_mul_of_nonneg_right (inv_anti₀ (hC 0) (hCC' 0))
      (exp_pos _).le).trans hl,
      hu.trans (mul_le_mul_of_nonneg_right (hCC' 0) (exp_pos _).le)⟩
  · intro m r hr
    by_cases hKr : r ∈ K
    · have hwr : 0 < w r := hpos r (hKcore hKr)
      have hInv : (w r)⁻¹ ≤ M 0 := by
        simpa only [radialJet, abs_of_pos (inv_pos.mpr hwr)] using (hMBounds 0 r hKr).2
      have hn : (1 : ℝ) ≤ D.cellIndex m := by exact_mod_cast hIndex m
      have ht : 1 ≤ (D.cellIndex m : ℝ) ^ 2 := by
        simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 2
      have hp : 0 ≤ (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hCt : C' 0 ≤ C' 0 * (D.cellIndex m : ℝ) ^ 2 :=
        le_mul_of_one_le_right (hC' 0).le ht
      have hCe : C' 0 ≤ exp (C' 0 * (D.cellIndex m : ℝ) ^ 2) :=
        hCt.trans ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _))
      apply (inv_le_inv₀ hwr (exp_pos _)).mp
      rw [← exp_neg]
      change (w r)⁻¹ ≤ exp (-(-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
        C' 0 * (D.cellIndex m : ℝ) ^ 2))
      have he : -(-((D.cellIndex m : ℝ) ^ (5 / 2 : ℝ)) -
          C' 0 * (D.cellIndex m : ℝ) ^ 2) =
          (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) + C' 0 * (D.cellIndex m : ℝ) ^ 2 := by ring
      rw [he]
      exact hInv.trans ((hM0C' 0).trans (hCe.trans
        (exp_le_exp.mpr (le_add_of_nonneg_left hp))))
    · rw [hSame r hKr]
      apply le_trans _ (hLower m r hr)
      apply exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right (hCC' 0) (sq_nonneg (D.cellIndex m : ℝ))
      linarith
  · intro m r hr s
    by_cases hKr : r ∈ K
    · have hLabel : (D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) ≤ P :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hAffected m r hr hKr)
          (by norm_num)
      have hMe : M s ≤ C' s * exp (-P) := by
        have h := (le_div_iff₀ (exp_pos P)).mpr (hME s)
        simpa only [div_eq_mul_inv, exp_neg] using h
      apply (hMBounds s r hKr).1.trans
      apply hMe.trans
      apply mul_le_mul_of_nonneg_left _ (hC' s).le
      apply exp_le_exp.mpr
      have hTerm := mul_nonneg (hC' s).le (sq_nonneg (D.cellIndex m : ℝ))
      linarith
    · have hj : radialJet s w r = radialJet s D.w r := by
        simpa only [surgeryJet_eq] using (hGerm r hKr).iteratedDeriv_eq s
      rw [hj]
      apply (hJet m r hr s).trans
      apply mul_le_mul (hCC' s) _ (exp_pos _).le (hC' s).le
      apply exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right (hCC' s) (sq_nonneg (D.cellIndex m : ℝ))
      linarith
  · intro m r hr s
    by_cases hKr : r ∈ K
    · exact (hMBounds s r hKr).2.trans ((hMC' s).trans
        (le_mul_of_one_le_right (hC' s).le
          (Real.one_le_rpow (hE _) (hC' s).le)))
    · have hi : (fun x => (w x)⁻¹) =ᶠ[𝓝 r] fun x => (D.w x)⁻¹ :=
        (hGerm r hKr).fun_comp Inv.inv
      have hj : radialJet s (fun x => (w x)⁻¹) r =
          radialJet s (fun x => (D.w x)⁻¹) r := by
        simpa only [surgeryJet_eq] using hi.iteratedDeriv_eq s
      rw [hj]
      exact (hInvJet m r hr s).trans (mul_le_mul (hCC' s)
        (Real.rpow_le_rpow_of_exponent_le (hE _) (hCC' s))
        (Real.rpow_nonneg (zero_le_one.trans (hE _)) _) (hC' s).le)
  · intro m
    obtain ⟨l, h, hs, hlen⟩ := hWidth m
    exact ⟨l, h, hs, hlen.trans
      (mul_le_mul_of_nonneg_right (hCC' 0) (exp_pos _).le)⟩

/-- Unrestricted compact surgery: remove label zero first. The selected
tail witness itself need not be relabelled; only the new reference is. -/
theorem isAccumulatingProfile_compactSurgery
    {D : ReferenceData} {w phi : ℝ → ℝ} {K : Set ℝ}
    (hD : IsAccumulatingProfile D)
    (hNew : RadialProfileGeometry (replaceReferenceProfile (positiveIndexReference D) w phi))
    (hK : IsCompact K) (hKcore : K ⊆ radialCore D)
    (hSame : ∀ r ∉ K, w r = D.w r) :
    IsAccumulatingProfile (replaceReferenceProfile (positiveIndexReference D) w phi) :=
  isAccumulatingProfile_replaceReferenceProfile
    (isAccumulatingProfile_positiveIndexReference hD)
    (positiveIndexReference_index_pos D) hNew hK hKcore hSame

end ContinuousFlexibility.Radial
