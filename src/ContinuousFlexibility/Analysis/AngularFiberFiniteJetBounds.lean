module

public import ContinuousFlexibility.Analysis.AngularFiberEndpointJets
public import ContinuousFlexibility.Analysis.AngularInverseFirstDerivative
public import ContinuousFlexibility.Analysis.CylinderMixedJetNorms
public import ContinuousFlexibility.Analysis.FiniteInverseJetBounds
public import ContinuousFlexibility.Analysis.ScalarFlowTriangularJets

/-!
# Finite endpoint bounds from actual forward coordinate jets

The angular inverse is constructed from the original lift. Its first
derivative is bounded by the original angular lower bound and radial
derivative. The existing inverse polynomial then controls every required
finite inverse jet, and the actual composition formula controls the
fiber radial field. No inverse higher-jet bound is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The numerical bound is chosen before the actual fields and point.
Only the required finite forward jets enter this estimate. -/
theorem exists_angularFiberPullback_finiteJet_bound
    (n : ℕ) (hn : 1 ≤ n) {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∃ B : ℝ, 1 ≤ B ∧
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
        ‖iteratedFDeriv ℝ n (angularFiberPullback φ ξ) p‖ ≤ B := by
  let R : ℝ := max (1 + (1 + M) / κ) (1 + M)
  have hR : 0 ≤ R := (show 0 ≤ 1 + M by linarith).trans (le_max_right _ _)
  have hfinite (j : ℕ) := exists_nonlinearInverse_finiteJet_bound
    (E := PolarPoint) (F := PolarPoint) j (fun _ => R) (fun _ => hR)
  choose C hC hCb using hfinite
  let B : ℝ := 1 + ∑ π : OrderedFinpartition n,
    M * ∏ j, C (π.partSize j - 1)
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ π : OrderedFinpartition n, M * ∏ j, C (π.partSize j - 1) :=
      Finset.sum_nonneg fun π _ => mul_nonneg hM
        (Finset.prod_nonneg fun j _ => zero_le_one.trans (hC _))
    dsimp only [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro φ ξ T hT hφ hξ hpositive hperiod p hangle hradial hφraw hξraw
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
    norm_fderiv_parameterizedCircleInverse_le
      hT hφ hpositive hperiod hκ hM p hangle hradial
  have hLbound : ‖L‖ ≤ R := by
    have hh := flowJet_augmented_jet_norm_le hA (n := 1) le_rfl p
    simp only [norm_iteratedFDeriv_one] at hh
    exact (hh.trans (add_le_add (le_refl (1 : ℝ)) hAfirst)).trans (le_max_left _ _)
  have hgjets (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      ‖iteratedFDeriv ℝ k g p‖ ≤ C (k - 1) := by
    have hraw (j : ℕ) (_ : 1 ≤ j) (hjk : j ≤ k - 1) :
        ‖iteratedFDeriv ℝ (j + 1) f (g p)‖ ≤ R := by
      have hjn : j + 1 ≤ n := by omega
      have hjpos : 1 ≤ j + 1 := by omega
      exact ((flowJet_augmented_jet_norm_le hφ hjpos (g p)).trans
        (add_le_add (le_refl (1 : ℝ)) (hφraw (j + 1) hjpos hjn))).trans
          (le_max_right _ _)
    have hh := hCb (k - 1) f g p hf.contDiffAt hg.contDiffAt
      (Filter.Eventually.of_forall fun q => congrFun hfg q) L hL hLbound hraw
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at hh
    exact hh
  have hs := norm_iteratedFDeriv_comp_le_partition_sum (x := p)
    hξ.contDiffAt hg.contDiffAt n
  have hsum :
      (∑ π : OrderedFinpartition n,
        ‖iteratedFDeriv ℝ π.length ξ (g p)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) g p‖) ≤
        ∑ π : OrderedFinpartition n, M * ∏ j, C (π.partSize j - 1) := by
    apply Finset.sum_le_sum
    intro π _
    exact mul_le_mul (hξraw π.length (π.length_pos (by omega)) π.length_le)
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => hgjets (π.partSize j) (π.partSize_pos j) (π.partSize_le j)))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM
  exact (hs.trans hsum).trans (le_add_of_nonneg_left zero_le_one)

/-- A single finite bound controls all positive radial endpoint jets
through the chosen order. It precedes the actual fields and boundary angle. -/
theorem exists_angularFiberBoundaryJets_bound
    (N : ℕ) {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∃ B : ℝ, 1 ≤ B ∧
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
          |radialBoundaryJet (angularFiberPullback φ ξ) c k θ| ≤ B := by
  have hfinite (j : ℕ) := exists_angularFiberPullback_finiteJet_bound
    (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hκ hM
  choose C hC hCb using hfinite
  let B : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), C j
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ j ∈ Finset.range (N + 1), C j :=
      Finset.sum_nonneg fun j _ => zero_le_one.trans (hC j)
    dsimp only [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro φ ξ T hT hφ hξ hpositive hperiod c hangle hradial hφraw hξraw k hk hkN θ
  have hb := hCb (k - 1) φ ξ T hT hφ hξ hpositive hperiod (c, θ)
    (hangle _) (hradial _)
    (fun j hj hjk => hφraw j hj (by omega) _)
    (fun j hj hjk => hξraw j hj (by omega) _)
  have hσ := contDiff_angularFiberPullback hT hφ hξ hpositive hperiod
  have hrad := abs_mixedDerivative_le_norm_iteratedFDeriv
    isOpen_univ hσ.contDiffOn k 0 (Set.mem_univ (c, θ))
  have hvalue : |radialBoundaryJet (angularFiberPullback φ ξ) c k θ| ≤ C (k - 1) := by
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [hk'] at hb
    have hr' : |radialBoundaryJet (angularFiberPullback φ ξ) c k θ| ≤
        ‖iteratedFDeriv ℝ k (angularFiberPullback φ ξ) (c, θ)‖ := by
      simpa only [mixedDerivative, radialBoundaryJet, iteratedDeriv_zero,
        Nat.add_zero] using hrad
    exact hr'.trans hb
  have hmem : k - 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hsum := Finset.single_le_sum
    (fun j _ => zero_le_one.trans (hC j)) hmem
  exact hvalue.trans (hsum.trans (le_add_of_nonneg_left zero_le_one))

end ContinuousFlexibility.Analysis

