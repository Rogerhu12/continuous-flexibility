import ContinuousFlexibility.Analysis.N07aReferenceUnitJets

/-!
# Primitive reference jets supply the positive unit-cylinder constants

The bound is polynomial in the actual primitive geometric envelopes.
In particular, neither an inverse estimate nor a commutator estimate is
assumed. The quotient's second derivative uses the primitive inverse-
leading atom, so no unquantified reciprocal differentiation occurs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

private theorem n07a_iteratedDeriv_two_eq (f : ℝ → ℝ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private theorem n07a_second_product_bound {f g : ℝ → ℝ} {x X : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hX : 0 ≤ X)
    (hfb : ∀ k : ℕ, k ≤ 2 → |iteratedDeriv k f x| ≤ X)
    (hgb : ∀ k : ℕ, k ≤ 2 → |iteratedDeriv k g x| ≤ X) :
    |deriv (deriv (fun y => f y * g y)) x| ≤ 4 * X ^ 2 := by
  have he := iteratedDeriv_fun_mul hf hg
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    n07a_iteratedDeriv_two_eq] at he
  have h₀ := mul_le_mul (hfb 0 (by omega)) (hgb 2 le_rfl) (abs_nonneg _) hX
  have h₁ := mul_le_mul (hfb 1 (by omega)) (hgb 1 (by omega)) (abs_nonneg _) hX
  have h₂ := mul_le_mul (hfb 2 le_rfl) (hgb 0 (by omega)) (abs_nonneg _) hX
  simp only [iteratedDeriv_zero, iteratedDeriv_one, n07a_iteratedDeriv_two_eq] at h₀ h₁ h₂
  rw [he]
  have ht := (abs_add_le (f x * deriv (deriv g) x + 2 * deriv f x * deriv g x)
    (deriv (deriv f) x * g x)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
  nlinarith

private theorem n07a_unit_degeneracy_lower {ell X P c d : ℝ}
    (hell : 0 < ell) (hX : 1 ≤ X) (hinv : |ell⁻¹| ≤ X)
    (hP : 0 < P) (hPX : P ≤ X) (hd : 0 ≤ d)
    (hc : P⁻¹ * ell ^ 2 * d ≤ c) :
    d / (4 * X ^ 5) ≤ ell ^ 2 * c := by
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hcap : 0 < 4 * X ^ 5 := by positivity
  have hc₀ : 0 ≤ c :=
    (mul_nonneg (mul_nonneg (inv_nonneg.mpr hP.le) (sq_nonneg ell)) hd).trans hc
  have hLX : 1 ≤ ell * X := by
    have h := mul_le_mul_of_nonneg_left hinv hell.le
    simpa only [abs_of_pos (inv_pos.mpr hell), mul_inv_cancel₀ hell.ne'] using h
  have hpow : 1 ≤ (ell * X) ^ 4 := one_le_pow₀ hLX
  have hpc : ell ^ 2 * d ≤ P * c := by
    have h := mul_le_mul_of_nonneg_left hc hP.le
    have he : P * (P⁻¹ * ell ^ 2 * d) = ell ^ 2 * d := by
      field_simp [hP.ne']
    rwa [he] at h
  have hpcc : ell ^ 4 * d ≤ P * (ell ^ 2 * c) := by
    nlinarith [mul_le_mul_of_nonneg_left hpc (sq_nonneg ell)]
  have hmain : d ≤ 4 * X ^ 5 * (ell ^ 2 * c) := by
    calc
      d ≤ (ell * X) ^ 4 * d := le_mul_of_one_le_left hd hpow
      _ = X ^ 4 * (ell ^ 4 * d) := by ring
      _ ≤ X ^ 4 * (P * (ell ^ 2 * c)) :=
        mul_le_mul_of_nonneg_left hpcc (pow_nonneg hX₀.le _)
      _ ≤ X ^ 4 * (X * (ell ^ 2 * c)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hPX (mul_nonneg (sq_nonneg ell) hc₀))
          (pow_nonneg hX₀.le _)
      _ ≤ 4 * X ^ 5 * (ell ^ 2 * c) := by
        nlinarith [mul_nonneg (pow_nonneg hX₀.le 5) (mul_nonneg (sq_nonneg ell) hc₀)]
  apply (div_le_iff₀ hcap).mpr
  nlinarith only [hmain]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

/-- All the numerical hypotheses of the open weak cubic estimate follow
from the primitive reference geometry, uniformly over every positive piece. -/
theorem n07a_reference_positive_unit_bounds
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (hE : ∀ m, 0 < T.E0 (T.sample (K.cell m)))
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ A P : ℝ, 0 < A ∧ 0 < P ∧ ∀ m, K.positive m = true →
      let X := 1 + A * T.E0 (T.sample (K.cell m)) ^ A +
        P * T.E0 (T.sample (K.cell m)) ^ P
      let J := 4 * X ^ 5
      1 ≤ J ∧ ∀ x ∈ Ioo (0 : ℝ) 1,
        1 / J ≤ n07aReferenceUnitAtom D T S C L K m .principalA x ∧
        n07aReferenceUnitAtom D T S C L K m .principalA x ≤ J ∧
        |deriv (n07aReferenceUnitAtom D T S C L K m .principalA) x| ≤ J ∧
        cylinderWeight x / J ≤ n07aReferenceUnitC D T S C L K m x ∧
        |n07aReferenceUnitC D T S C L K m x| ≤ J ∧
        |n07aReferenceUnitV D T S C L K m x| ≤ J ∧
        |deriv (deriv (n07aReferenceUnitQ D T S C L K m)) x| ≤ J := by
  obtain ⟨A, hA, hAb⟩ := n07aReferenceUnitAtom_twoJet_bound hJ
  obtain ⟨P, hPpos, hPb⟩ := hP.2
  refine ⟨A, P, hA, hPpos, ?_⟩
  intro m hm
  let R := A * T.E0 (T.sample (K.cell m)) ^ A
  let Z := P * T.E0 (T.sample (K.cell m)) ^ P
  let X := 1 + R + Z
  let J := 4 * X ^ 5
  have hR : 0 < R := mul_pos hA (Real.rpow_pos_of_pos (hE m) _)
  have hZ : 0 < Z := mul_pos hPpos (Real.rpow_pos_of_pos (hE m) _)
  have hX : 1 ≤ X := by dsimp only [X]; linarith
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hRX : R ≤ X := by dsimp only [X]; linarith
  have hZX : Z ≤ X := by dsimp only [X]; linarith
  have hXJ : X ≤ J := by
    have hp : X ≤ X ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 5)
    dsimp only [J]
    linarith [pow_nonneg hX₀.le 5]
  have hJ₁ : 1 ≤ J := hX.trans hXJ
  have hJpos : 0 < J := zero_lt_one.trans_le hJ₁
  have hb (a : Atom) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (k : ℕ) (hk : k ≤ 2) :
      |iteratedDeriv k (n07aReferenceUnitAtom D T S C L K m a) x| ≤ X :=
    (hAb m a x hx k hk).trans hRX
  have hell : 0 < K.right m - K.left m := sub_pos.mpr (hlen m)
  have hellX : |K.right m - K.left m| ≤ X := by
    simpa only [iteratedDeriv_zero, n07aReferenceUnitAtom, atom] using
      hb .canonicalLength (1 / 2) (by constructor <;> norm_num) 0 (by omega)
  have helliX : |(K.right m - K.left m)⁻¹| ≤ X := by
    simpa only [iteratedDeriv_zero, n07aReferenceUnitAtom, atom] using
      hb .canonicalLengthInverse (1 / 2) (by constructor <;> norm_num) 0 (by omega)
  have hell₂ : (K.right m - K.left m) ^ 2 ≤ X ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hellX 2
  have h3 : X ^ 3 ≤ J := by
    have h35 := pow_le_pow_right₀ hX (by omega : 3 ≤ 5)
    dsimp only [J]
    linarith [pow_nonneg hX₀.le 5]
  refine ⟨hJ₁, ?_⟩
  intro x hx
  have ha₀ := n07aReferenceUnitAtom_A_pos (D := D) (L := L) hP m (hlen m) hx
  have haI : |(n07aReferenceUnitAtom D T S C L K m .principalA x)⁻¹| ≤ X := by
    simpa only [iteratedDeriv_zero, n07aReferenceUnitAtom_inverse] using
      hb .principalAInverse x hx 0 (by omega)
  have haLow : 1 / X ≤ n07aReferenceUnitAtom D T S C L K m .principalA x := by
    apply (div_le_iff₀ hX₀).mpr
    have h := mul_le_mul_of_nonneg_left haI ha₀.le
    simpa only [abs_of_pos (inv_pos.mpr ha₀), mul_inv_cancel₀ ha₀.ne'] using h
  have hac : |n07aReferenceUnitAtom D T S C L K m .principalA x| ≤ X := by
    simpa only [iteratedDeriv_zero] using hb .principalA x hx 0 (by omega)
  have had : |deriv (n07aReferenceUnitAtom D T S C L K m .principalA) x| ≤ X := by
    simpa only [iteratedDeriv_one] using hb .principalA x hx 1 (by omega)
  have hc0 : |n07aReferenceUnitAtom D T S C L K m .principalC x| ≤ X := by
    simpa only [iteratedDeriv_zero] using hb .principalC x hx 0 (by omega)
  have hv0 : |n07aReferenceUnitAtom D T S C L K m .potential x| ≤ X := by
    simpa only [iteratedDeriv_zero] using hb .potential x hx 0 (by omega)
  have hcBound : |n07aReferenceUnitC D T S C L K m x| ≤ X ^ 3 := by
    rw [n07aReferenceUnitC, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul hell₂ hc0 (abs_nonneg _) (sq_nonneg X)).trans_eq (by ring)
  have hvBound : |n07aReferenceUnitV D T S C L K m x| ≤ X ^ 3 := by
    rw [n07aReferenceUnitV, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul hell₂ hv0 (abs_nonneg _) (sq_nonneg X)).trans_eq (by ring)
  have hclower : cylinderWeight x / J ≤ n07aReferenceUnitC D T S C L K m x := by
    have hactual := hPb m hm (canonicalUnitPoint K m (x, 0))
      (n07a_canonicalUnitPoint_mem m (hlen m) hx)
    have hbase : Z⁻¹ * (K.right m - K.left m) ^ 2 * cylinderWeight x ≤
        n07aReferenceUnitAtom D T S C L K m .principalC x := by
      convert hactual using 1 <;>
        simp only [Z, n07aReferenceUnitAtom, atom, canonicalUnitPoint, cylinderWeight]; ring
    exact n07a_unit_degeneracy_lower hell hX helliX hZ hZX
      (cylinderWeight_nonneg (Ioo_subset_Icc_self hx)) hbase
  have hqBound : |deriv (deriv (n07aReferenceUnitQ D T S C L K m)) x| ≤ J := by
    let f := n07aReferenceUnitAtom D T S C L K m .principalC
    let g := n07aReferenceUnitAtom D T S C L K m .principalAInverse
    have hf : ContDiffAt ℝ 2 f x :=
      ((n07aReferenceUnitAtom_contDiff hJ m .principalC).contDiffAt
        (isOpen_Ioo.mem_nhds hx)).of_le (by simp)
    have hg : ContDiffAt ℝ 2 g x :=
      ((n07aReferenceUnitAtom_contDiff hJ m .principalAInverse).contDiffAt
        (isOpen_Ioo.mem_nhds hx)).of_le (by simp)
    have hfg := n07a_second_product_bound hf hg hX₀.le (hb .principalC x hx)
      (hb .principalAInverse x hx)
    have hd : deriv (deriv (n07aReferenceUnitQ D T S C L K m)) x =
        (K.right m - K.left m) ^ 2 * deriv (deriv (fun y => f y * g y)) x := by
      rw [← n07a_iteratedDeriv_two_eq]
      unfold n07aReferenceUnitQ
      rw [iteratedDeriv_const_mul_field, n07a_iteratedDeriv_two_eq]
    rw [hd, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ X ^ 2 * (4 * X ^ 2) := mul_le_mul hell₂ hfg (abs_nonneg _) (sq_nonneg X)
      _ = 4 * X ^ 4 := by ring
      _ ≤ J := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by omega : 4 ≤ 5)) (by norm_num)
  exact ⟨(one_div_le_one_div_of_le hX₀ hXJ).trans haLow,
    (le_abs_self _).trans (hac.trans hXJ), had.trans hXJ, hclower,
    hcBound.trans h3, hvBound.trans h3, hqBound⟩

end ContinuousFlexibility.Analysis
