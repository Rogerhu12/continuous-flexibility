import ContinuousFlexibility.Analysis.RadialReferencePotentialJetEnvelope

/-!
# Local jets of the negative reference potential after unit cancellation

The physical potential is w H^3 (w H')'. Its canonical value is obtained
by composition with the same actual scalar inverse. Direct estimates on
the real height powers keep every input polynomial; only positive jets
of the inverse occur in the composition formula.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

/-- The coefficient precedes the actual fields, point and numerical
bound. Only genuine local smoothness is used, so no derivative cost of
an extension beyond the physical or canonical half enters the result. -/
theorem radialUnitDensityPotential_finiteJet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M : ℝ}, 1 ≤ M →
      ∀ (w H χ : ℝ → ℝ) (x : ℝ),
        ContDiffAt ℝ ∞ w (χ x) → ContDiffAt ℝ ∞ H (χ x) →
        ContDiffAt ℝ ∞ χ x →
        (∀ k, k ≤ N + 1 → |iteratedDeriv k w (χ x)| ≤ M) →
        (∀ k, k ≤ N + 2 → |iteratedDeriv k H (χ x)| ≤ M) →
        (∀ k, k ≤ N → |iteratedDeriv k (fun r => H r ^ 3) (χ x)| ≤ M) →
        (∀ k, 1 ≤ k → k ≤ N → |iteratedDeriv k χ x| ≤ M) →
        |iteratedDeriv N
          (fun t => w (χ t) * H (χ t) ^ 3 *
            deriv (fun r => w r * deriv H r) (χ t)) x| ≤ C * M ^ (N + 4) := by
  obtain ⟨CP, hCP, hprod⟩ := referencePotential_product_envelope N
  obtain ⟨CP1, hCP1, hprod1⟩ := referencePotential_product_envelope (N + 1)
  obtain ⟨CC, hCC, hcomp⟩ := referencePotential_composition_envelope N
  let C : ℝ := CC * CP * CP * CP1
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCC hCP) hCP) hCP1
  refine ⟨C, hC, ?_⟩
  intro M hM w H χ x hw hH hχ hwj hHj hH3j hχj
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hHd : ContDiffAt ℝ ∞ (deriv H) (χ x) := hH.derivWithin (by simp)
  let flux : ℝ → ℝ := fun r => w r * deriv H r
  have hflux : ContDiffAt ℝ ∞ flux (χ x) := hw.mul hHd
  have hfluxj (k : ℕ) (hk : k ≤ N + 1) :
      |iteratedDeriv k flux (χ x)| ≤ CP1 * M * M := by
    apply hprod1 hM0 hM0 w (deriv H) (χ x) hw hHd hwj _ k hk
    intro q hq
    rw [← iteratedDeriv_succ']
    exact hHj (q + 1) (by omega)
  have hfluxd : ContDiffAt ℝ ∞ (deriv flux) (χ x) :=
    hflux.derivWithin (by simp)
  have hfluxdj (k : ℕ) (hk : k ≤ N) :
      |iteratedDeriv k (deriv flux) (χ x)| ≤ CP1 * M * M := by
    rw [← iteratedDeriv_succ']
    exact hfluxj (k + 1) (by omega)
  let prefactor : ℝ → ℝ := fun r => w r * H r ^ 3
  have hprefactor : ContDiffAt ℝ ∞ prefactor (χ x) := hw.mul (hH.pow 3)
  have hprefactorj (k : ℕ) (hk : k ≤ N) :
      |iteratedDeriv k prefactor (χ x)| ≤ CP * M * M :=
    hprod hM0 hM0 w (fun r => H r ^ 3) (χ x) hw (hH.pow 3)
      (fun q hq => hwj q (by omega)) hH3j k hk
  have hP0 : 0 ≤ CP * M * M :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCP) hM0) hM0
  have hF0 : 0 ≤ CP1 * M * M :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCP1) hM0) hM0
  let potential : ℝ → ℝ := fun r => prefactor r * deriv flux r
  have hpotential : ContDiffAt ℝ ∞ potential (χ x) := hprefactor.mul hfluxd
  have hpotentialj (k : ℕ) (hk : k ≤ N) :
      |iteratedDeriv k potential (χ x)| ≤ CP * (CP * M * M) * (CP1 * M * M) :=
    hprod hP0 hF0 prefactor (deriv flux) (χ x) hprefactor hfluxd
      hprefactorj hfluxdj k hk
  have hbound0 : 0 ≤ CP * (CP * M * M) * (CP1 * M * M) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCP) hP0) hF0
  have hb := hcomp hbound0 hM potential χ x hpotential hχ
    hpotentialj hχj N le_rfl
  have hpower : M ^ 4 * M ^ N = M ^ (N + 4) := by
    rw [← pow_add]
    congr 1 <;> omega
  calc
    _ ≤ CC * (CP * (CP * M * M) * (CP1 * M * M)) * M ^ N := hb
    _ = C * (M ^ 4 * M ^ N) := by dsimp only [C]; ring
    _ = C * M ^ (N + 4) := by rw [hpower]

end ContinuousFlexibility.Analysis
