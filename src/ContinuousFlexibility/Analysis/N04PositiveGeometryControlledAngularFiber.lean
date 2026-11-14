module

public import ContinuousFlexibility.Analysis.AngularFiberFiniteJetBounds
public import ContinuousFlexibility.Analysis.FiniteInversePolynomialEnvelope

/-!
# Fixed polynomial costs for the actual angular inverse pullback

The first augmented inverse derivative is bounded by 3 M². The genuine
finite inverse polynomial then bounds all required inverse derivatives.
The actual composition partition formula and a finite sum yield one
coefficient and exponent before M, the angular lower bound, or any field.
No angular lift value or higher inverse-jet estimate is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n04PositiveGeometry_exists_angularFiberPullback_polynomial_envelope (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, ∀ {M κ : ℝ},
      1 ≤ M → 0 < κ → κ⁻¹ ≤ M →
      ∀ φ ξ : PolarPoint → ℝ, ∀ T : ℝ, T ≠ 0 →
        ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ξ →
      ∀ hpositive : (∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2),
        (∀ r θ, φ (r, θ + T) = φ (r, θ) + T) →
      ∀ p : PolarPoint,
        κ ≤ angularPartial φ (p.1, parameterizedCircleInverse φ p) →
        |radialPartial φ (p.1, parameterizedCircleInverse φ p)| ≤ M →
        (∀ k, 1 ≤ k → k ≤ n →
          ‖iteratedFDeriv ℝ k φ (p.1, parameterizedCircleInverse φ p)‖ ≤ M) →
        (∀ k, 1 ≤ k → k ≤ n →
          ‖iteratedFDeriv ℝ k ξ (p.1, parameterizedCircleInverse φ p)‖ ≤ M) →
        ‖iteratedFDeriv ℝ n (angularFiberPullback φ ξ) p‖ ≤ C * M ^ d := by
  have hfinite (j : ℕ) := exists_nonlinearInverse_finiteJet_polynomial_envelope
    (E := PolarPoint) (F := PolarPoint) j
  choose C hC d hCb using hfinite
  let K : ℝ := 1 + ∑ j ∈ Finset.range (n + 1), C j * 3 ^ d j
  let D : ℕ := ∑ j ∈ Finset.range (n + 1), 2 * d j
  have hcoef (j : ℕ) : 0 ≤ C j * 3 ^ d j :=
    mul_nonneg (zero_le_one.trans (hC j)) (pow_nonneg (by norm_num) _)
  have hK : 1 ≤ K := by
    have hs := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (n + 1)) => hcoef j)
    dsimp only [K]
    linarith
  refine ⟨1 + (Fintype.card (OrderedFinpartition n) : ℝ) * K ^ n,
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (zero_le_one.trans hK) _)), D * n + 1, ?_⟩
  intro M κ hM hκ hκinv φ ξ T hT hφ hξ hpositive hperiod p hangle hradial hφraw hξraw
  have hMn : 0 ≤ M := zero_le_one.trans hM
  have hMsq : M ≤ M ^ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hM (by decide : 1 ≤ 2)
  have hMtwo : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hR : 1 ≤ 3 * M ^ 2 := by nlinarith
  have hAugA : 1 + (1 + M) / κ ≤ 3 * M ^ 2 := by
    have hdiv : (1 + M) / κ ≤ (1 + M) * M := by
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hκinv (show 0 ≤ 1 + M by linarith)
    nlinarith
  have hAugF : 1 + M ≤ 3 * M ^ 2 := by nlinarith
  let A := parameterizedCircleInverse φ
  let f : PolarPoint → PolarPoint := fun q => (q.1, φ q)
  let g : PolarPoint → PolarPoint := fun q => (q.1, A q)
  have hA : ContDiff ℝ ∞ A :=
    contDiff_parameterizedCircleInverse hT hφ hpositive hperiod
  have hf : ContDiff ℝ ∞ f := contDiff_fst.prodMk hφ
  have hg : ContDiff ℝ ∞ g := contDiff_fst.prodMk hA
  have hfg : f ∘ g = id := by
    funext q
    exact Prod.ext rfl (parameterizedCircleInverse_right_inverse hT hφ hperiod q)
  have hgf : g ∘ f = id := by
    funext q
    exact Prod.ext rfl (parameterizedCircleInverse_left_inverse hpositive q)
  have hfp : f (g p) = p := congrFun hfg p
  let L : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ g p
  have hL : L.comp (fderiv ℝ f (g p)) = ContinuousLinearMap.id ℝ PolarPoint := by
    calc
      _ = (fderiv ℝ g (f (g p))).comp (fderiv ℝ f (g p)) := by rw [hfp]
      _ = fderiv ℝ (g ∘ f) (g p) :=
        (fderiv_comp (g p) (hg.differentiable (by simp) (f (g p)))
          (hf.differentiable (by simp) (g p))).symm
      _ = _ := by rw [hgf, fderiv_id]
  have hAfirst : ‖fderiv ℝ A p‖ ≤ (1 + M) / κ :=
    norm_fderiv_parameterizedCircleInverse_le hT hφ hpositive hperiod hκ hMn
      p hangle hradial
  have hLbound : ‖L‖ ≤ 3 * M ^ 2 := by
    have hh := flowJet_augmented_jet_norm_le hA (n := 1) le_rfl p
    simp only [norm_iteratedFDeriv_one] at hh
    exact (hh.trans (add_le_add (le_refl (1 : ℝ)) hAfirst)).trans hAugA
  have hgjets (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      ‖iteratedFDeriv ℝ k g p‖ ≤ K * M ^ D := by
    have hraw (j : ℕ) (_ : 1 ≤ j) (hjk : j ≤ k - 1) :
        ‖iteratedFDeriv ℝ (j + 1) f (g p)‖ ≤ 3 * M ^ 2 := by
      have hjn : j + 1 ≤ n := by omega
      have hjpos : 1 ≤ j + 1 := by omega
      exact ((flowJet_augmented_jet_norm_le hφ hjpos (g p)).trans
        (add_le_add (le_refl (1 : ℝ)) (hφraw (j + 1) hjpos hjn))).trans hAugF
    have hh := hCb (k - 1) hR f g p hf.contDiffAt hg.contDiffAt
      (Filter.Eventually.of_forall fun q => congrFun hfg q) L hL hLbound hraw
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [hk'] at hh
    have hmem : k - 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hcoeff : C (k - 1) * 3 ^ d (k - 1) ≤ K :=
      (Finset.single_le_sum (fun j _ => hcoef j) hmem).trans
        (le_add_of_nonneg_left zero_le_one)
    have hdegree : 2 * d (k - 1) ≤ D :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (2 * d j)) hmem
    calc
      ‖iteratedFDeriv ℝ k g p‖ ≤ C (k - 1) * (3 * M ^ 2) ^ d (k - 1) := hh
      _ = (C (k - 1) * 3 ^ d (k - 1)) * M ^ (2 * d (k - 1)) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ K * M ^ D := mul_le_mul hcoeff (pow_le_pow_right₀ hM hdegree)
        (pow_nonneg hMn _) (zero_le_one.trans hK)
  have hKM : 1 ≤ K * M ^ D := by
    simpa only [one_mul] using mul_le_mul hK (one_le_pow₀ hM)
      (show (0 : ℝ) ≤ 1 by norm_num) (zero_le_one.trans hK)
  have hs := norm_iteratedFDeriv_comp_le_partition_sum (x := p)
    hξ.contDiffAt hg.contDiffAt n
  have hterm (π : OrderedFinpartition n) :
      ‖iteratedFDeriv ℝ π.length ξ (g p)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) g p‖ ≤
        M * (K * M ^ D) ^ n := by
    have hprod : (∏ j, ‖iteratedFDeriv ℝ (π.partSize j) g p‖) ≤
        (K * M ^ D) ^ n := by
      calc
        _ ≤ ∏ _j : Fin π.length, K * M ^ D :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun j _ => hgjets (π.partSize j) (π.partSize_pos j) (π.partSize_le j))
        _ = (K * M ^ D) ^ π.length := by simp
        _ ≤ (K * M ^ D) ^ n := pow_le_pow_right₀ hKM π.length_le
    exact mul_le_mul (hξraw π.length (π.length_pos (by omega)) π.length_le)
      hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) hMn
  calc
    ‖iteratedFDeriv ℝ n (angularFiberPullback φ ξ) p‖ ≤
        ∑ π : OrderedFinpartition n, ‖iteratedFDeriv ℝ π.length ξ (g p)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) g p‖ := hs
    _ ≤ ∑ _π : OrderedFinpartition n, M * (K * M ^ D) ^ n :=
      Finset.sum_le_sum fun π _ => hterm π
    _ = (Fintype.card (OrderedFinpartition n) : ℝ) * (M * (K * M ^ D) ^ n) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((Fintype.card (OrderedFinpartition n) : ℝ) * K ^ n) * M ^ (D * n + 1) := by
      rw [mul_pow, ← pow_mul, pow_succ]
      ring
    _ ≤ (1 + (Fintype.card (OrderedFinpartition n) : ℝ) * K ^ n) *
        M ^ (D * n + 1) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg hMn _)

/-- A common fixed monomial controls all positive boundary traces through
N. Its coefficient and exponent precede both lower and upper raw bounds. -/
theorem n04PositiveGeometry_exists_angularFiberBoundaryJets_polynomial_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ, ∀ {M κ : ℝ},
      1 ≤ M → 0 < κ → κ⁻¹ ≤ M →
      ∀ φ ξ : PolarPoint → ℝ, ∀ T : ℝ, T ≠ 0 →
        ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ξ →
      ∀ hpositive : (∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2),
        (∀ r θ, φ (r, θ + T) = φ (r, θ) + T) →
      ∀ c : ℝ,
        (∀ θ, κ ≤ angularPartial φ (c, θ)) →
        (∀ θ, |radialPartial φ (c, θ)| ≤ M) →
        (∀ k, 1 ≤ k → k ≤ N → ∀ θ, ‖iteratedFDeriv ℝ k φ (c, θ)‖ ≤ M) →
        (∀ k, 1 ≤ k → k ≤ N → ∀ θ, ‖iteratedFDeriv ℝ k ξ (c, θ)‖ ≤ M) →
        ∀ k, 1 ≤ k → k ≤ N → ∀ θ,
          |radialBoundaryJet (angularFiberPullback φ ξ) c k θ| ≤ C * M ^ d := by
  have hfinite (j : ℕ) := n04PositiveGeometry_exists_angularFiberPullback_polynomial_envelope
    (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
  choose C hC d hCb using hfinite
  let B : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), C j
  let D : ℕ := ∑ j ∈ Finset.range (N + 1), d j
  have hB : 1 ≤ B := by
    have hs := Finset.sum_nonneg
      (fun j (_ : j ∈ Finset.range (N + 1)) => zero_le_one.trans (hC j))
    dsimp only [B]
    linarith
  refine ⟨B, hB, D, ?_⟩
  intro M κ hM hκ hκinv φ ξ T hT hφ hξ hpositive hperiod c hangle hradial hφraw hξraw k hk hkN θ
  have hb := hCb (k - 1) hM hκ hκinv φ ξ T hT hφ hξ hpositive hperiod (c, θ)
    (hangle _) (hradial _)
    (fun j hj hjk => hφraw j hj (by omega) _)
    (fun j hj hjk => hξraw j hj (by omega) _)
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk'] at hb
  have hσ := contDiff_angularFiberPullback hT hφ hξ hpositive hperiod
  have hrad := abs_mixedDerivative_le_norm_iteratedFDeriv
    isOpen_univ hσ.contDiffOn k 0 (Set.mem_univ (c, θ))
  have hr' : |radialBoundaryJet (angularFiberPullback φ ξ) c k θ| ≤
      ‖iteratedFDeriv ℝ k (angularFiberPullback φ ξ) (c, θ)‖ := by
    simpa only [mixedDerivative, radialBoundaryJet, iteratedDeriv_zero, Nat.add_zero] using hrad
  have hmem : k - 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hcoeff : C (k - 1) ≤ B :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hC j)) hmem).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdegree : d (k - 1) ≤ D :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) hmem
  exact (hr'.trans hb).trans (mul_le_mul hcoeff (pow_le_pow_right₀ hM hdegree)
    (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hB))

end ContinuousFlexibility.Analysis
