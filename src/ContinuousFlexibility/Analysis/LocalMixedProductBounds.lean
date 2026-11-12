import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
import ContinuousFlexibility.Analysis.ReverseCoordinateOperator
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
import ContinuousFlexibility.Analysis.SpacesHeightAlgebra
import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets
import ContinuousFlexibility.Analysis.PeriodicScalarFlow

/-!
# Local mixed derivatives and a fixed periodic multiplier

The source factor need only be smooth on its actual open physical domain.
A genuine cutoff extends its germ before the global mixed Leibniz rule
is used. On a compact radial set the fixed multiplier has uniform jets
at all angles by periodicity. The resulting bound is linear in the
source jet bound and introduces no derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem mixedDerivative_eq_of_germ {f g : PolarPoint → ℝ} {p : PolarPoint}
    (h : f =ᶠ[𝓝 p] g) (a b : ℕ) :
    mixedDerivative a b f p = mixedDerivative a b g p := by
  obtain ⟨U, hUsub, hU, hp⟩ := mem_nhds_iff.mp h
  exact mixedDerivative_eqOn_of_isOpen hU (fun _ hq => hUsub hq) a b hp

/-- A local source factor has the ordinary actual mixed Leibniz formula.
The globally smooth multiplier is kept unchanged in the cutoff argument. -/
theorem mixedDerivative_mul_of_contDiffOn
    {U : Set PolarPoint} (hU : IsOpen U) {φ g : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiffOn ℝ ∞ g U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b (fun q => φ q * g q) p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j φ p * mixedDerivative (a - i) (b - j) g p := by
  obtain ⟨G, hG, heG⟩ := exists_global_contDiff_germ_of_open hU hg hp
  have he : (fun q => φ q * G q) =ᶠ[𝓝 p] (fun q => φ q * g q) := by
    filter_upwards [heG] with q hq
    rw [hq]
  rw [← mixedDerivative_eq_of_germ he a b, spaces_mixedDerivative_mul hφ hG]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mixedDerivative_eq_of_germ heG (a - i) (b - j)]

/-- The multiplier constant is chosen before the open source domain,
source field, point, and source jet bound. Only source orders at most
`a+b` are used, so the source's existing fixed loss is preserved. -/
theorem exists_local_mixedMultiplier_constant
    {K : Set ℝ} (hK : IsCompact K) {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hperiod : Function.Periodic φ (0, Real.pi))
    (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : Set PolarPoint, IsOpen U → ∀ g : PolarPoint → ℝ,
        ContDiffOn ℝ ∞ g U → ∀ p ∈ U, p.1 ∈ K → ∀ M : ℝ, 0 ≤ M →
          (∀ i j : ℕ, i + j ≤ a + b → |mixedDerivative i j g p| ≤ M) →
          |mixedDerivative a b (fun q => φ q * g q) p| ≤ C * M := by
  have hperiod' (r : ℝ) : Function.Periodic (fun θ => φ (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hperiod (r, θ)
  have hbounds (i j : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ r ∈ K, ∀ θ, |mixedDerivative i j φ (r, θ)| ≤ A := by
    obtain ⟨A, hA, hb⟩ := exists_norm_bound_periodic_compact hK Real.pi_ne_zero
      (contDiff_mixedDerivative hφ i j).continuous.continuousOn
      (fun r _ => mixedDerivative_angular_periodic hperiod' i j r)
    exact ⟨A, hA, fun r hr θ => by simpa only [Real.norm_eq_abs] using hb r hr θ⟩
  choose A hA hbound using hbounds
  let C : ℝ := ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
    (b.choose j : ℝ) * (a.choose i : ℝ) * A i j
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by positivity) (hA i j)
  refine ⟨C, hC, ?_⟩
  intro U hU g hg p hp hpK M hM hgBound
  rw [mixedDerivative_mul_of_contDiffOn hU hφ hg a b hp]
  calc
    _ ≤ ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) * A i j * M := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have hij : (a - i) + (b - j) ≤ a + b := by omega
      have hc : 0 ≤ (b.choose j : ℝ) * (a.choose i : ℝ) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg hc]
      have hb := mul_le_mul (hbound i j p.1 hpK p.2)
        (hgBound (a - i) (b - j) hij) (abs_nonneg _) (hA i j)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hc
    _ = C * M := by simp only [C, Finset.sum_mul]

end ContinuousFlexibility.Analysis
