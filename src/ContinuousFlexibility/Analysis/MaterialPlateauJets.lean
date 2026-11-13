import ContinuousFlexibility.Analysis.RadialPlateauCutoff
import ContinuousFlexibility.Analysis.RadialPrimitiveJets
import Mathlib.Data.Nat.Choose.Sum

/-!
# Quantitative material jets of a radial plateau test

The collar-width loss of the physical cutoff survives composition with
the actual material radius. Multiplying by the physical height weight
retains that weight, so no loss in its exponent is hidden in the cutoff
construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem iteratedDeriv_mul_le_of_jet_bounds {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : ∀ i : ℕ, i ≤ n → |iteratedDeriv i f x| ≤ A)
    (hgB : ∀ i : ℕ, i ≤ n → |iteratedDeriv i g x| ≤ B) :
    |iteratedDeriv n (fun t => f t * g t) x| ≤ (2 : ℝ) ^ n * A * B := by
  rw [iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by simp))
    (hg.contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        |(n.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (n - i) g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose i))]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfB i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _))
        (hgB (n - i) (Nat.sub_le n i)) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem finite_iteratedDeriv_bound {h : ℝ → ℝ}
    (hb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |iteratedDeriv n h x| ≤ K)
    (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ i : ℕ, i ≤ n → ∀ x : ℝ, |iteratedDeriv i h x| ≤ K := by
  classical
  have hA (i : Fin (n + 1)) := hb i.val
  choose A hA hAb using hA
  refine ⟨∑ i : Fin (n + 1), A i, Finset.sum_nonneg (fun i _ => hA i), ?_⟩
  intro i hi x
  let j : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  exact (hAb j x).trans (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ j))

theorem inv_pow_le_inv_pow_of_le_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {i n : ℕ} (hi : i ≤ n) : δ⁻¹ ^ i ≤ δ⁻¹ ^ n := by
  have hinv : 1 ≤ δ⁻¹ := by
    have h : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
    simpa only [one_div] using h
  exact pow_le_pow_right₀ hinv hi

def radialPlateauProduct (h : ℝ → ℝ) (l r δ : ℝ) : ℝ → ℝ :=
  fun x => radialPlateauCutoff l r δ x * h x

theorem radialPlateauProduct_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (l r δ : ℝ) : ContDiff ℝ ∞ (radialPlateauProduct h l r δ) :=
  (radialPlateauCutoff_contDiff l r δ).mul hh

/-- The full primitive times cutoff loses only a power of the collar
width at each fixed ordinary derivative order. -/
theorem radialPlateauProduct_iteratedDeriv_bound {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h)
    (hb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |iteratedDeriv n h x| ≤ K)
    (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : ℝ,
      |iteratedDeriv n (radialPlateauProduct h l r δ) x| ≤ K * δ⁻¹ ^ n := by
  classical
  have hA (i : Fin (n + 1)) := radialPlateauCutoff_iteratedDeriv_bound i.val
  choose A hA hAb using hA
  let A₀ : ℝ := ∑ i : Fin (n + 1), A i
  have hA₀ : 0 ≤ A₀ := Finset.sum_nonneg (fun i _ => hA i)
  obtain ⟨B, hB, hBb⟩ := finite_iteratedDeriv_bound hb n
  refine ⟨(2 : ℝ) ^ n * A₀ * B,
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) n) hA₀) hB, ?_⟩
  intro l r δ hδ hδ1 x
  have hcut (i : ℕ) (hi : i ≤ n) :
      |iteratedDeriv i (radialPlateauCutoff l r δ) x| ≤ A₀ * δ⁻¹ ^ n := by
    let j : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have ha : A j ≤ A₀ := Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ j)
    calc
      _ ≤ A j / δ ^ i := hAb j l r δ hδ x
      _ = A j * δ⁻¹ ^ i := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ A₀ * δ⁻¹ ^ n := mul_le_mul ha
        (inv_pow_le_inv_pow_of_le_one hδ hδ1 hi)
        (pow_nonneg (inv_nonneg.mpr hδ.le) i) hA₀
  have hmul := iteratedDeriv_mul_le_of_jet_bounds
    (radialPlateauCutoff_contDiff l r δ) hh n x
    (mul_nonneg hA₀ (pow_nonneg (inv_nonneg.mpr hδ.le) n)) hB
    hcut (fun i hi => hBb i hi x)
  change |iteratedDeriv n (radialPlateauProduct h l r δ) x| ≤
    (2 : ℝ) ^ n * (A₀ * δ⁻¹ ^ n) * B at hmul
  exact hmul.trans_eq (by ring)

theorem radialPlateauProduct_materialJet_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |iteratedDeriv n h x| ≤ K)
    (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : ℝ,
      |iteratedDeriv n (fun t => radialPlateauProduct h l r δ (T.radius t)) x|
        ≤ K * δ⁻¹ ^ n := by
  classical
  have hA (i : Fin (n + 1)) := radialPlateauProduct_iteratedDeriv_bound hh hb i.val
  choose A hA hAb using hA
  let A₀ : ℝ := ∑ i : Fin (n + 1), A i
  have hA₀ : 0 ≤ A₀ := Finset.sum_nonneg (fun i _ => hA i)
  obtain ⟨C, hC, hCb⟩ := iteratedDeriv_comp_materialRadius_le hT n
  refine ⟨C * A₀, mul_nonneg hC hA₀, ?_⟩
  intro l r δ hδ hδ1 x
  have houter (i : ℕ) (hi : i ≤ n) (y : ℝ) :
      |iteratedDeriv i (radialPlateauProduct h l r δ) y| ≤ A₀ * δ⁻¹ ^ n := by
    let j : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have ha : A j ≤ A₀ := Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ j)
    exact (hAb j l r δ hδ hδ1 y).trans (mul_le_mul ha
      (inv_pow_le_inv_pow_of_le_one hδ hδ1 hi)
      (pow_nonneg (inv_nonneg.mpr hδ.le) i) hA₀)
  have hcomp := hCb (radialPlateauProduct h l r δ)
    (radialPlateauProduct_contDiff hh l r δ) (A₀ * δ⁻¹ ^ n)
    (mul_nonneg hA₀ (pow_nonneg (inv_nonneg.mpr hδ.le) n)) houter x
  exact hcomp.trans_eq (by ring)

def materialPlateauPullback (T : MaterialData) (γ : ℝ)
    (h : ℝ → ℝ) (l r δ : ℝ) : ℝ → ℝ :=
  fun x => T.H (T.radius x) ^ (-γ) * radialPlateauProduct h l r δ (T.radius x)

/-- Every material derivative retains the exact physical height weight. -/
theorem materialPlateauPullback_iteratedDeriv_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hb : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |iteratedDeriv n h x| ≤ K)
    (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : ℝ,
      |iteratedDeriv n (materialPlateauPullback T γ h l r δ) x| ≤
        K * δ⁻¹ ^ n * T.H (T.radius x) ^ (-γ) := by
  classical
  have hA (i : Fin (n + 1)) := iteratedDeriv_materialH_rpow_bound hT (-γ) i.val
  have hB (i : Fin (n + 1)) := radialPlateauProduct_materialJet_bound hT hh hb i.val
  choose A hA hAb using hA
  choose B hB hBb using hB
  let A₀ : ℝ := ∑ i : Fin (n + 1), A i
  let B₀ : ℝ := ∑ i : Fin (n + 1), B i
  have hA₀ : 0 ≤ A₀ := Finset.sum_nonneg (fun i _ => hA i)
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg (fun i _ => hB i)
  have hdata := hT
  obtain ⟨hsmooth, hpos, _, _, _, _, hradius, hinside, _⟩ := hdata
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    materialRadius_comp_contDiff hT (hsmooth T.H (by simp))
  have hHp (x : ℝ) : 0 < T.H (T.radius x) := (hpos _ (hinside x).1).2.1
  have hweight : ContDiff ℝ ∞ (fun x => T.H (T.radius x) ^ (-γ)) :=
    hH.rpow_const_of_ne (fun x => (hHp x).ne')
  refine ⟨(2 : ℝ) ^ n * A₀ * B₀,
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) n) hA₀) hB₀, ?_⟩
  intro l r δ hδ hδ1 x
  have hw₀ : 0 ≤ T.H (T.radius x) ^ (-γ) := Real.rpow_nonneg (hHp x).le _
  have hweightB (i : ℕ) (hi : i ≤ n) :
      |iteratedDeriv i (fun t => T.H (T.radius t) ^ (-γ)) x| ≤
        A₀ * T.H (T.radius x) ^ (-γ) := by
    let j : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have ha : A j ≤ A₀ := Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ j)
    exact (hAb j x).trans (mul_le_mul_of_nonneg_right ha hw₀)
  have hproductB (i : ℕ) (hi : i ≤ n) :
      |iteratedDeriv i (fun t => radialPlateauProduct h l r δ (T.radius t)) x| ≤
        B₀ * δ⁻¹ ^ n := by
    let j : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have hb : B j ≤ B₀ := Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ j)
    exact (hBb j l r δ hδ hδ1 x).trans (mul_le_mul hb
      (inv_pow_le_inv_pow_of_le_one hδ hδ1 hi)
      (pow_nonneg (inv_nonneg.mpr hδ.le) i) hB₀)
  have hproduct : ContDiff ℝ ∞
      (fun t => radialPlateauProduct h l r δ (T.radius t)) :=
    (radialPlateauProduct_contDiff hh l r δ).comp hradius
  have hmul := iteratedDeriv_mul_le_of_jet_bounds hweight hproduct n x
    (mul_nonneg hA₀ hw₀) (mul_nonneg hB₀ (pow_nonneg (inv_nonneg.mpr hδ.le) n))
    hweightB hproductB
  change |iteratedDeriv n (materialPlateauPullback T γ h l r δ) x| ≤
    (2 : ℝ) ^ n * (A₀ * T.H (T.radius x) ^ (-γ)) * (B₀ * δ⁻¹ ^ n) at hmul
  exact hmul.trans_eq (by ring)

theorem referencePlateau_materialJet_bound {D : ReferenceData} {T : MaterialData}
    (hD : RadialProfileGeometry D) (hT : IsMaterialData D T) (γ : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : ℝ,
      |iteratedDeriv n (materialPlateauPullback T γ (referenceRadialPrimitive D) l r δ) x| ≤
        K * δ⁻¹ ^ n * T.H (T.radius x) ^ (-γ) :=
  materialPlateauPullback_iteratedDeriv_bound hT γ
    (referenceRadialPrimitive_contDiff hD) (referenceRadialPrimitive_iteratedDeriv_bounded hD) n

end ContinuousFlexibility.Statements
