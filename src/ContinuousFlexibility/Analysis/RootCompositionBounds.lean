import ContinuousFlexibility.Analysis.RootBoundaryJets
import ContinuousFlexibility.Analysis.RootEvenInteriorBounds
import ContinuousFlexibility.Analysis.RootOddBounds

/-!
# Uniform finite-order bounds for the root substitutions

The positive-halfspace Taylor estimate and the ordinary boundary-jet
comparison together bound the even substitution without losing a
derivative. The odd substitution is an even substitution of a smooth
integral of the middle derivative, and therefore loses exactly one
derivative. Boundary jets are handled using the actual globally defined
functions in `CSBound`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

local notation "sourceBox" =>
  (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
local notation "targetBox" =>
  (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)

/-- A bound through one order also bounds every smaller order. -/
theorem CSBound.mono_order {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : ℕ} {K : Set E} {f : E → ℝ} {M : ℝ}
    (h : CSBound s K f M) (ht : t ≤ s) : CSBound t K f M :=
  fun n hn x hx => h n (hn.trans ht) x hx

/-- Increasing the common constant preserves the finite jet bound. -/
theorem CSBound.mono_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℕ} {K : Set E} {f : E → ℝ} {M N : ℝ}
    (h : CSBound s K f M) (hMN : M ≤ N) : CSBound s K f N :=
  fun n hn x hx => (h n hn x hx).trans hMN

private theorem csBound_source_nonneg {s : ℕ} {G : ℝ × ℝ × ℝ → ℝ} {M : ℝ}
    (h : CSBound s sourceBox G M) : 0 ≤ M := by
  have hz : ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ sourceBox :=
    ⟨⟨le_rfl, zero_le_one⟩, ⟨by norm_num, by norm_num⟩,
      ⟨neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos.le⟩⟩
  exact (norm_nonneg (G (0, 0, 0))).trans (h.norm_le hz)

/-- The even substitution preserves the order of a uniform finite jet
bound, including the ordinary derivatives at the boundary. -/
theorem exists_csBound_rootEven (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
      ∀ M : ℝ, CSBound s sourceBox G M →
        CSBound s targetBox (rootEven G) (C * M) := by
  classical
  choose c hcpos hc using exists_rootEven_pos_jet_bound
  let C : ℝ := 1 + ∑ n ∈ Finset.range (s + 1), c n
  have hsum : 0 ≤ ∑ n ∈ Finset.range (s + 1), c n :=
    Finset.sum_nonneg (fun n _ => (hcpos n).le)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro G hG M hB n hn p hp
  have hM : 0 ≤ M := csBound_source_nonneg hB
  by_cases hx : p.1 = 0
  · have hpzero : p = (0, p.2) := by ext <;> simp [hx]
    have hq : ((0, 0, p.2) : ℝ × ℝ × ℝ) ∈ sourceBox :=
      ⟨⟨le_rfl, zero_le_one⟩, ⟨by norm_num, by norm_num⟩, hp.2⟩
    calc
      ‖iteratedFDeriv ℝ n (rootEven G) p‖ =
          ‖iteratedFDeriv ℝ n (rootEven G) (0, p.2)‖ :=
        congrArg (fun q => ‖iteratedFDeriv ℝ n (rootEven G) q‖) hpzero
      _ ≤ ‖iteratedFDeriv ℝ n G (0, 0, p.2)‖ :=
        norm_iteratedFDeriv_rootEven_zero_le hG n p.2
      _ ≤ M := hB n hn _ hq
      _ ≤ C * M := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hM
  · have hxpos : 0 < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm hx)
    have hcn : c n ≤ C := by
      have hsingle : c n ≤ ∑ k ∈ Finset.range (s + 1), c k :=
        Finset.single_le_sum (fun k _ => (hcpos k).le)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
      dsimp only [C]
      linarith
    exact (hc n G hG M (hB.mono_order hn) p hp hxpos).trans
      (mul_le_mul_of_nonneg_right hcn hM)

private theorem csBound_rootOdd_of_integral
    {s : ℕ} {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    {M C : ℝ} (hC : 1 ≤ C) (hB : CSBound (s + 1) sourceBox G M)
    (hI : CSBound s targetBox (rootEven (rootOddIntegral G)) (C * M)) :
    CSBound s targetBox (rootOdd G) (C * M) := by
  have hM : 0 ≤ M := csBound_source_nonneg hB
  intro n hn p hp
  by_cases hx : p.1 = 0
  · cases n with
    | zero =>
      have hzero := csBound_rootOdd_zero hG
        (hB.mono_order (Nat.succ_le_succ (Nat.zero_le s)))
      exact (hzero 0 le_rfl p hp).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hM)
    | succ n =>
      have hpzero : p = (0, p.2) := by ext <;> simp [hx]
      rw [hpzero, iteratedFDeriv_rootOdd_succ_zero, norm_zero]
      exact mul_nonneg (zero_le_one.trans hC) hM
  · have hxpos : 0 < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm hx)
    have heq : EqOn (rootEven (rootOddIntegral G)) (rootOdd G)
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
      intro q hq
      exact rootEven_rootOddIntegral_eqOn hG ⟨hq.1.le, hq.2⟩
    have hjet := iteratedFDeriv_eqOn_of_isOpen
      (isOpen_Ioi.prod isOpen_univ) heq n ⟨hxpos, mem_univ _⟩
    rw [← hjet]
    exact hI n hn p hp

/-- A single positive constant controls the even and odd substitutions
at every fixed finite order, with the stated zero and one derivative losses. -/
theorem exists_rootComposition_csBound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G → ∀ M : ℝ,
      (CSBound s sourceBox G M → CSBound s targetBox (rootEven G) (C * M)) ∧
      (CSBound (s + 1) sourceBox G M → CSBound s targetBox (rootOdd G) (C * M)) := by
  obtain ⟨CE, hCE, hEven⟩ := exists_csBound_rootEven s
  obtain ⟨CO, hCO, hIntegral⟩ := exists_csBound_rootOddIntegral s
  let C : ℝ := CE * (1 + CO)
  have hCE0 : 0 ≤ CE := zero_le_one.trans hCE
  have hCE_C : CE ≤ C := by
    dsimp only [C]
    nlinarith
  have hCEO_C : CE * CO ≤ C := by
    dsimp only [C]
    nlinarith
  have hC : 1 ≤ C := hCE.trans hCE_C
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro G hG M
  constructor
  · intro hB
    exact (hEven G hG M hB).mono_bound
      (mul_le_mul_of_nonneg_right hCE_C (csBound_source_nonneg hB))
  · intro hB
    have hK := hIntegral G hG M hB
    have hI := hEven (rootOddIntegral G) (contDiff_rootOddIntegral hG) (CO * M) hK
    have hI' : CSBound s targetBox (rootEven (rootOddIntegral G)) (C * M) :=
      hI.mono_bound (by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hCEO_C (csBound_source_nonneg hB))
    exact csBound_rootOdd_of_integral hG hC hB hI'

end ContinuousFlexibility.Statements
