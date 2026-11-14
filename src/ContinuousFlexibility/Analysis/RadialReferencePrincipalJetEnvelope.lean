import ContinuousFlexibility.Analysis.RadialReferencePotentialJetEnvelope

/-!
# Finite jets of the radial principal formulas

The forward principal coefficient is a product of three pullbacks, with
the height appearing twice. The inverse leading and tangential principal
coefficients replace the last pullback by the derivative of the genuine
inverse coordinate. The same finite polynomial bound handles both forms,
requiring smoothness of physical factors only at the evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

/-- One constant, chosen before all fields and envelopes, controls the
two actual product shapes. Only positive inverse-coordinate jets enter. -/
theorem exists_radialReferencePrincipal_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M : ℝ}, 1 ≤ M →
      ∀ (f g v χ : ℝ → ℝ) (x : ℝ),
      ContDiffAt ℝ ∞ f (χ x) → ContDiffAt ℝ ∞ g (χ x) →
      ContDiffAt ℝ ∞ v (χ x) → ContDiffAt ℝ ∞ χ x →
      (∀ k, k ≤ N → |iteratedDeriv k f (χ x)| ≤ M) →
      (∀ k, k ≤ N → |iteratedDeriv k g (χ x)| ≤ M) →
      (∀ k, k ≤ N → |iteratedDeriv k v (χ x)| ≤ M) →
      (∀ k, 1 ≤ k → k ≤ N + 1 → |iteratedDeriv k χ x| ≤ M) →
      |iteratedDeriv N (fun t => f (χ t) ^ 2 * g (χ t) * v (χ t)) x| ≤
          C * M ^ (4 * N + 4) ∧
      |iteratedDeriv N (fun t => f (χ t) ^ 2 * g (χ t) * deriv χ t) x| ≤
          C * M ^ (4 * N + 4) := by
  obtain ⟨CP, hCP, hproduct⟩ := referencePotential_product_envelope N
  obtain ⟨CC, hCC, hcomposition⟩ := referencePotential_composition_envelope N
  let C : ℝ := CP ^ 3 * CC ^ 4
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hCP) (one_le_pow₀ hCC)
  refine ⟨C, hC, ?_⟩
  intro M hM f g v χ x hf hg hv hχ hfj hgj hvj hχj
  let Z : ℝ := CC * M * M ^ N
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hCC hM) (one_le_pow₀ hM)
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hMZ : M ≤ Z :=
    (le_mul_of_one_le_left hM0 hCC).trans
      (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hCC) hM0)
        (one_le_pow₀ hM))
  have hcomposed {u : ℝ → ℝ} (hu : ContDiffAt ℝ ∞ u (χ x))
      (huj : ∀ k, k ≤ N → |iteratedDeriv k u (χ x)| ≤ M) :
      ∀ k, k ≤ N → |iteratedDeriv k (u ∘ χ) x| ≤ Z :=
    hcomposition hM0 hM u χ x hu hχ huj
      (fun k hk hkN => hχj k hk (by omega))
  have hfc := hcomposed hf hfj
  have hgc := hcomposed hg hgj
  have hvc := hcomposed hv hvj
  have hfχ : ContDiffAt ℝ ∞ (f ∘ χ) x := hf.comp x hχ
  have hgχ : ContDiffAt ℝ ∞ (g ∘ χ) x := hg.comp x hχ
  have hff : ∀ k, k ≤ N →
      |iteratedDeriv k (fun t => f (χ t) ^ 2) x| ≤ CP * Z * Z := by
    simpa only [Function.comp_apply, pow_two] using
      hproduct hZ0 hZ0 (f ∘ χ) (f ∘ χ) x hfχ hfχ hfc hfc
  have hff0 : 0 ≤ CP * Z * Z :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCP) hZ0) hZ0
  have hfg : ∀ k, k ≤ N →
      |iteratedDeriv k (fun t => f (χ t) ^ 2 * g (χ t)) x| ≤
        CP * (CP * Z * Z) * Z :=
    hproduct hff0 hZ0 (fun t => f (χ t) ^ 2) (g ∘ χ) x
      (hfχ.pow 2) hgχ hff hgc
  have hfg0 : 0 ≤ CP * (CP * Z * Z) * Z :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCP) hff0) hZ0
  have hfinish {u : ℝ → ℝ} (hu : ContDiffAt ℝ ∞ u x)
      (huj : ∀ k, k ≤ N → |iteratedDeriv k u x| ≤ Z) :
      |iteratedDeriv N (fun t => f (χ t) ^ 2 * g (χ t) * u t) x| ≤
        C * M ^ (4 * N + 4) := by
    have hb := hproduct hfg0 hZ0 (fun t => f (χ t) ^ 2 * g (χ t)) u x
      ((hfχ.pow 2).mul hgχ) hu hfg huj N le_rfl
    apply hb.trans_eq
    have hp : (M * M ^ N) ^ 4 = M ^ (4 * N + 4) := by
      rw [← pow_succ', ← pow_mul]
      congr 1 <;> omega
    calc
      _ = C * (M * M ^ N) ^ 4 := by dsimp only [C, Z]; ring
      _ = _ := by rw [hp]
  refine ⟨hfinish (hv.comp x hχ) hvc, hfinish (hχ.derivWithin (by simp)) ?_⟩
  intro k hk
  rw [← iteratedDeriv_succ']
  exact (hχj (k + 1) (by omega) (by omega)).trans hMZ

end ContinuousFlexibility.Analysis
