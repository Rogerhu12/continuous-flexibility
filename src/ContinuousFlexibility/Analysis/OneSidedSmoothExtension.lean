import ContinuousFlexibility.Analysis.FlatExtension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth extension across one regular endpoint

The construction uses compactly supported monomials with successively
smaller scales. Their lower derivatives are uniformly small, while the
specified derivative at the origin is unchanged. This supplies a single
smooth function realizing all prescribed endpoint jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff BigOperators

theorem exists_compact_iteratedDeriv_bound {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv k g x‖ ≤ C := by
  have hsupport : HasCompactSupport (iteratedDeriv k g) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hs
    | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv
  obtain ⟨C, hC⟩ := hsupport.exists_bound_of_continuous
    (ContDiff.continuous_iteratedDeriv k hg (by simp))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

def oneSidedJetBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- One compactly supported monomial, normalized by the factorial. -/
def oneSidedJetBase (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (c / (n.factorial : ℝ)) * x ^ n * oneSidedJetBump x

theorem contDiff_oneSidedJetBase (c : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (oneSidedJetBase c n) :=
  (contDiff_const.mul (contDiff_id.pow n)).mul oneSidedJetBump.contDiff

theorem hasCompactSupport_oneSidedJetBase (c : ℝ) (n : ℕ) :
    HasCompactSupport (oneSidedJetBase c n) :=
  oneSidedJetBump.hasCompactSupport.mul_left

theorem iteratedDeriv_oneSidedJetBase_zero (c : ℝ) (n k : ℕ) :
    iteratedDeriv k (oneSidedJetBase c n) 0 = if k = n then c else 0 := by
  have heq : oneSidedJetBase c n =ᶠ[𝓝 0] fun x => (c / (n.factorial : ℝ)) * x ^ n := by
    filter_upwards [oneSidedJetBump.eventuallyEq_one] with x hx
    simp only [oneSidedJetBase, hx, mul_one]
  rw [heq.iteratedDeriv_eq k, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  by_cases hkn : k = n
  · rw [if_pos hkn, if_pos hkn]
    exact div_mul_cancel₀ c (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  · rw [if_neg hkn, if_neg hkn, mul_zero]

/-- Scaling preserves the target jet while suppressing lower derivatives. -/
def oneSidedScaledJet (n : ℕ) (ε : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ε ^ n * g (ε⁻¹ * x)

theorem contDiff_oneSidedScaledJet {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (ε : ℝ) : ContDiff ℝ ∞ (oneSidedScaledJet n ε g) :=
  contDiff_const.mul (hg.comp (contDiff_const.mul contDiff_id))

theorem iteratedDeriv_oneSidedScaledJet {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (n k : ℕ) (ε x : ℝ) :
    iteratedDeriv k (oneSidedScaledJet n ε g) x =
      (ε ^ n * (ε⁻¹) ^ k) * iteratedDeriv k g (ε⁻¹ * x) := by
  rw [oneSidedScaledJet, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul ((contDiff_infty.mp hg) k) (ε⁻¹)]
  ring

theorem oneSidedScaledJet_factor {ε : ℝ} (hε : 0 < ε) {k n : ℕ} (hkn : k ≤ n) :
    ε ^ n * (ε⁻¹) ^ k = ε ^ (n - k) := by
  rw [inv_pow]
  exact (pow_sub₀ ε hε.ne' hkn).symm

/-- A single positive scale makes every derivative below the target order
uniformly as small as prescribed. -/
theorem exists_oneSidedScaledJet_small {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ k < n, ∀ x, ‖iteratedDeriv k (oneSidedScaledJet n ε g) x‖ ≤ δ := by
  choose C hC₀ hC using fun k : ℕ => exists_compact_iteratedDeriv_bound hg hs k
  have hall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ k ∈ Finset.range n, ε ^ (n - k) * C k < δ := by
    rw [eventually_all_finset]
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hcont : Continuous (fun ε : ℝ => ε ^ (n - k) * C k) :=
      (continuous_id.pow _).mul continuous_const
    have hlim : Tendsto (fun ε : ℝ => ε ^ (n - k) * C k) (𝓝 0) (𝓝 0) := by
      simpa only [zero_pow (Nat.sub_pos_of_lt hkn).ne', zero_mul] using hcont.tendsto (0 : ℝ)
    exact (hlim.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
  obtain ⟨ε, hsmall, hε⟩ :=
    (hall.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one))).exists
  refine ⟨ε, hε.1, hε.2.le, ?_⟩
  intro k hkn x
  calc
    ‖iteratedDeriv k (oneSidedScaledJet n ε g) x‖ =
        ε ^ (n - k) * ‖iteratedDeriv k g (ε⁻¹ * x)‖ := by
      rw [iteratedDeriv_oneSidedScaledJet hg, oneSidedScaledJet_factor hε.1 hkn.le,
        norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.1.le _)]
    _ ≤ ε ^ (n - k) * C k :=
      mul_le_mul_of_nonneg_left (hC k _) (pow_nonneg hε.1.le _)
    _ ≤ δ := (hsmall k (Finset.mem_range.mpr hkn)).le

theorem iteratedDeriv_oneSidedScaledJet_zero {ε : ℝ} (hε : 0 < ε)
    (c : ℝ) (n k : ℕ) :
    iteratedDeriv k (oneSidedScaledJet n ε (oneSidedJetBase c n)) 0 =
      if k = n then c else 0 := by
  rw [iteratedDeriv_oneSidedScaledJet (contDiff_oneSidedJetBase c n), mul_zero,
    iteratedDeriv_oneSidedJetBase_zero]
  by_cases hkn : k = n
  · subst k
    simp only [if_pos rfl, oneSidedScaledJet_factor hε le_rfl, Nat.sub_self,
      pow_zero, one_mul]
  · rw [if_neg hkn, mul_zero]

/-- Borel's endpoint-jet construction in one real variable. A single smooth
function realizes every member of an arbitrary sequence of derivatives. -/
theorem exists_contDiff_prescribed_jets (a : ℕ → ℝ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ k : ℕ, iteratedDeriv k g 0 = a k := by
  classical
  have hscale (n : ℕ) := exists_oneSidedScaledJet_small
    (contDiff_oneSidedJetBase (a n) n) (hasCompactSupport_oneSidedJetBase (a n) n) n
    (show 0 < (1 / 2 : ℝ) ^ n from pow_pos (by norm_num) _)
  choose ε hε₀ hε₁ hεsmall using hscale
  let f : ℕ → ℝ → ℝ := fun n => oneSidedScaledJet n (ε n) (oneSidedJetBase (a n) n)
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    contDiff_oneSidedScaledJet (contDiff_oneSidedJetBase (a n) n) n (ε n)
  choose C hC₀ hC using fun n k : ℕ =>
    exists_compact_iteratedDeriv_bound (contDiff_oneSidedJetBase (a n) n)
      (hasCompactSupport_oneSidedJetBase (a n) n) k
  let v : ℕ → ℕ → ℝ := fun k n =>
    if k < n then (1 / 2 : ℝ) ^ n else
      ‖(ε n) ^ n * ((ε n)⁻¹) ^ k‖ * C n k
  have hv (k : ℕ) : Summable (v k) := by
    have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    apply hgeo.congr_atTop
    filter_upwards [eventually_gt_atTop k] with n hn
    simp only [v, if_pos hn]
  have hbound (k n : ℕ) (x : ℝ) : ‖iteratedDeriv k (f n) x‖ ≤ v k n := by
    dsimp only [v]
    split_ifs with hkn
    · exact hεsmall n k hkn x
    · dsimp only [f]
      rw [iteratedDeriv_oneSidedScaledJet (contDiff_oneSidedJetBase (a n) n), norm_mul]
      exact mul_le_mul_of_nonneg_left (hC n k _) (norm_nonneg _)
  have hboundF (k n : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound k n x
  refine ⟨fun x => ∑' n, f n x,
    contDiff_tsum (N := ⊤) hf (fun k _ => hv k) (fun k n x _ => hboundF k n x), ?_⟩
  intro k
  have hsum : iteratedDeriv k (fun x => ∑' n, f n x) 0 =
      ∑' n, iteratedDeriv k (f n) 0 := by
    simp only [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
    rw [iteratedFDeriv_tsum (N := ⊤) hf (fun j _ => hv j)
      (fun j n x _ => hboundF j n x) (by simp)]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm
      .toContinuousLinearEquiv.map_tsum
  rw [hsum]
  have hjet (n : ℕ) : iteratedDeriv k (f n) 0 = if k = n then a n else 0 :=
    iteratedDeriv_oneSidedScaledJet_zero (hε₀ n) (a n) n k
  simp_rw [hjet]
  simp

end ContinuousFlexibility.Analysis
