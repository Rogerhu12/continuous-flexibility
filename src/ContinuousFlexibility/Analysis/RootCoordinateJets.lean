import ContinuousFlexibility.Analysis.RootPowerJets
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# Uniform jets of the root coordinate

Both samples in the even and odd root substitutions are covered by one
coordinate map with a scalar parameter of norm at most one. On the
positive radial interval, its derivatives admit the scale used by the
weighted composition estimate. The proof uses the max norm on products.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- The root coordinate, with a parameter covering both signs. -/
def rootCoordinate (σ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1, σ * p.1 ^ (3 / 2 : ℝ), p.2)

theorem contDiffAt_rootCoordinate (σ : ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (rootCoordinate σ) p :=
  contDiffAt_fst.prodMk
    ((contDiffAt_const.mul (contDiffAt_fst.rpow_const_of_ne hp.ne')).prodMk contDiffAt_snd)

/-- The coordinate map is smooth throughout the positive half-plane. -/
theorem contDiffOn_rootCoordinate (σ : ℝ) :
    ContDiffOn ℝ ∞ (rootCoordinate σ) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  intro p hp
  exact (contDiffAt_rootCoordinate σ hp.1).contDiffWithinAt

/-- Pulling a scalar power back by the first projection does not increase
the norm of any iterated derivative at a positive point. -/
theorem norm_iteratedFDeriv_rpow_fst_le (a : ℝ) (i : ℕ)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => q.1 ^ a) p‖ ≤
      ‖iteratedDeriv i (fun x : ℝ => x ^ a) p.1‖ := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hsmooth : ContDiffOn ℝ ∞ (fun x : ℝ => x ^ a) (Ioi (0 : ℝ)) :=
    fun x hx => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hopen : IsOpen (L ⁻¹' Ioi (0 : ℝ)) := isOpen_Ioi.preimage L.continuous
  have hmem : p ∈ L ⁻¹' Ioi (0 : ℝ) := hp
  have hcomp := L.iteratedFDerivWithin_comp_right hsmooth isOpen_Ioi.uniqueDiffOn
    hopen.uniqueDiffOn (x := p) (i := i) hmem (by simp)
  rw [iteratedFDerivWithin_of_isOpen i hopen hmem,
    iteratedFDerivWithin_of_isOpen i isOpen_Ioi (show L p ∈ Ioi (0 : ℝ) from hp)] at hcomp
  change ‖iteratedFDeriv ℝ i ((fun x : ℝ => x ^ a) ∘ L) p‖ ≤ _
  rw [hcomp]
  simpa [L, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
    (iteratedFDeriv ℝ i (fun x : ℝ => x ^ a) (L p)).norm_compContinuousLinearMap_le
      (fun _ => L)

private theorem norm_iteratedFDeriv_linear_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {i : ℕ} (hi : 1 ≤ i) (p : E) :
    ‖iteratedFDeriv ℝ i (L : E → F) p‖ ≤ ‖L‖ := by
  cases i with
  | zero => omega
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hfun : fderiv ℝ (L : E → F) = fun _ => L := funext fun _ => L.fderiv
    rw [hfun]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero]; exact le_rfl
    | succ j =>
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      exact norm_nonneg L

/-- The three component jets are bounded using the exact max product norm. -/
theorem norm_iteratedFDeriv_rootCoordinate_le {σ : ℝ} (hσ : ‖σ‖ ≤ 1)
    {i : ℕ} (hi : 1 ≤ i) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ‖iteratedFDeriv ℝ i (rootCoordinate σ) p‖ ≤
      max 1 (‖rpowJetCoefficient (3 / 2 : ℝ) i‖ * p.1 ^ (3 / 2 : ℝ) / p.1 ^ i) := by
  have hpower : ContDiffAt ℝ i (fun q : ℝ × ℝ => q.1 ^ (3 / 2 : ℝ)) p :=
    contDiffAt_fst.rpow_const_of_ne hp.ne'
  have hmiddle : ContDiffAt ℝ i (fun q : ℝ × ℝ => σ * q.1 ^ (3 / 2 : ℝ)) p :=
    contDiffAt_const.mul hpower
  have hfirst : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => q.1) p‖ ≤ 1 :=
    (norm_iteratedFDeriv_linear_le (ContinuousLinearMap.fst ℝ ℝ ℝ) hi p).trans
      (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have hlast : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => q.2) p‖ ≤ 1 :=
    (norm_iteratedFDeriv_linear_le (ContinuousLinearMap.snd ℝ ℝ ℝ) hi p).trans
      (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hmid : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => σ * q.1 ^ (3 / 2 : ℝ)) p‖ ≤
      ‖rpowJetCoefficient (3 / 2 : ℝ) i‖ * p.1 ^ (3 / 2 : ℝ) / p.1 ^ i := by
    change ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => σ • q.1 ^ (3 / 2 : ℝ)) p‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hpower, norm_smul]
    calc
      ‖σ‖ * ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => q.1 ^ (3 / 2 : ℝ)) p‖ ≤
          1 * ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => q.1 ^ (3 / 2 : ℝ)) p‖ :=
        mul_le_mul_of_nonneg_right hσ (norm_nonneg _)
      _ ≤ ‖iteratedDeriv i (fun x : ℝ => x ^ (3 / 2 : ℝ)) p.1‖ := by
        simpa only [one_mul] using norm_iteratedFDeriv_rpow_fst_le (3 / 2 : ℝ) i hp
      _ = _ := norm_iteratedDeriv_rpow_of_pos (3 / 2 : ℝ) i hp
  change ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => (q.1, σ * q.1 ^ (3 / 2 : ℝ), q.2)) p‖ ≤ _
  rw [iteratedFDeriv_prodMk contDiffAt_fst (hmiddle.prodMk contDiffAt_snd) le_rfl,
    iteratedFDeriv_prodMk hmiddle contDiffAt_snd le_rfl,
    ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  exact max_le (hfirst.trans (le_max_left _ _))
    (max_le (hmid.trans (le_max_right _ _)) (hlast.trans (le_max_left _ _)))

/-- At any fixed finite order the root coordinate has a uniform weighted
jet bound. The same constant works for every scalar parameter of norm at
most one, in particular for both signs. -/
theorem exists_rootCoordinate_jet_bound (s : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ σ : ℝ, ‖σ‖ ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ s →
      ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ 1 →
      ‖iteratedFDeriv ℝ i (rootCoordinate σ) p‖ ≤
        p.1 ^ (3 / 2 : ℝ) * (D / p.1 ^ (3 / 2 : ℝ)) ^ i := by
  obtain ⟨D, hD, hcoeff⟩ := exists_rpowJetCoefficient_bound (3 / 2 : ℝ) s
  refine ⟨D, hD, ?_⟩
  intro σ hσ i hi his p hp hp1
  let λ : ℝ := p.1 ^ (3 / 2 : ℝ)
  have hλ : 0 < λ := Real.rpow_pos_of_pos hp _
  have hλx : λ ≤ p.1 := Real.rpow_le_self_of_le_one hp.le hp1 (by norm_num)
  have hλ1 : λ ≤ 1 := hλx.trans hp1
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hDi : D ≤ D ^ i := by simpa only [pow_one] using pow_le_pow_right₀ hD hi
  have hratio : 1 ≤ D / λ := (le_div_iff₀ hλ).mpr (by simpa only [one_mul] using hλ1.trans hD)
  have hone : 1 ≤ λ * (D / λ) ^ i := by
    calc
      1 ≤ D := hD
      _ = λ * (D / λ) := by field_simp [hλ.ne'] <;> ring
      _ ≤ λ * (D / λ) ^ i := mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_right₀ hratio hi) hλ.le
  have hpower : λ ^ i ≤ p.1 ^ i := pow_le_pow_left₀ hλ.le hλx i
  have hmiddle : ‖rpowJetCoefficient (3 / 2 : ℝ) i‖ * λ / p.1 ^ i ≤
      λ * (D / λ) ^ i := by
    calc
      ‖rpowJetCoefficient (3 / 2 : ℝ) i‖ * λ / p.1 ^ i ≤ D ^ i * λ / λ ^ i :=
        div_le_div₀ (mul_nonneg (pow_nonneg hD0 i) hλ.le)
          (mul_le_mul_of_nonneg_right ((hcoeff i his).trans hDi) hλ.le)
          (pow_pos hλ i) hpower
      _ = λ * (D / λ) ^ i := by rw [div_pow]; ring
  exact (norm_iteratedFDeriv_rootCoordinate_le hσ hi hp).trans (max_le hone hmiddle)

end ContinuousFlexibility.Analysis
