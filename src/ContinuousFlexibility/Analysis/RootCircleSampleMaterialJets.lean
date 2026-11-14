module

public import ContinuousFlexibility.Analysis.InteriorEndpointMaterialJets
public import ContinuousFlexibility.Analysis.RootExtensionPhysicalBounds
public import ContinuousFlexibility.Analysis.OneHighCircleFourierCompositionCalculus

/-!
# Actual angular jets on fixed sections of the controlled root input

A fixed radial and root-parameter sample is an affine restriction with
operator norm one. The original compact-box jet bounds therefore give
the same derivative loss on one angular period. Periodicity of the
actual displacement extends these bounds to every angular representative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootCircleSample (G : ℝ × ℝ × ℝ → ℝ) (x ζ : ℝ) (θ : ℝ) : ℝ :=
  G (x, ζ, θ)

private def rootCircleAngleInclusion : ℝ →L[ℝ] (ℝ × ℝ × ℝ) :=
  (0 : ℝ →L[ℝ] ℝ).prod ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ))

private theorem rootCircleAngleInclusion_apply (θ : ℝ) :
    rootCircleAngleInclusion θ = (0, 0, θ) := by
  simp only [rootCircleAngleInclusion, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]

private theorem rootCircleAngleInclusion_norm : ‖rootCircleAngleInclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro θ
  rw [rootCircleAngleInclusion_apply]
  simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg θ), one_mul, le_refl]

theorem contDiff_rootCircleSample
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (x ζ : ℝ) :
    ContDiff ℝ ∞ (rootCircleSample G x ζ) :=
  hG.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

theorem rootCircleSample_period_add
    {G : ℝ × ℝ × ℝ → ℝ}
    (hperiod : ∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi)
    (x ζ θ : ℝ) :
    rootCircleSample G x ζ (θ + Real.pi) = rootCircleSample G x ζ θ + Real.pi :=
  hperiod x ζ θ

/-- The constants precede the state, root input and chosen section.
All angular orders keep the original material derivative loss. -/
theorem exists_rootCircleSample_displacement_jet_constants
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ)
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
        (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) →
        (∀ s : ℕ, CSBound s
          (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G
            (A s * (1 + p (s + loss) z))) →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ Icc (-1 : ℝ) 1, ∀ θ : ℝ,
        PointwiseMaterialJetBound p loss B z (fun η => rootCircleSample G x ζ η - η) θ := by
  let B : ℕ → ℝ := fun n => A n + (1 + Real.pi)
  have hB (n : ℕ) : 0 < B n := add_pos (hA n) (add_pos zero_lt_one Real.pi_pos)
  refine ⟨B, hB, ?_⟩
  intro z G hG hperiod hjets x hx ζ hζ θ n
  let u : ℝ → ℝ := rootCircleSample G x ζ
  let v : ℝ → ℝ := fun η => u η - η
  have hu : ContDiff ℝ ∞ u := contDiff_rootCircleSample hG x ζ
  have hperiodv : Function.Periodic v Real.pi := by
    intro η
    change G (x, ζ, η + Real.pi) - (η + Real.pi) = G (x, ζ, η) - η
    rw [hperiod x ζ η]
    ring
  letI : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
  obtain ⟨t, ht, he⟩ := (periodic_iteratedDeriv hperiodv n).exists_mem_Ico₀ Real.pi_pos θ
  have ht' : t ∈ Icc (-Real.pi) Real.pi :=
    ⟨(neg_nonpos.mpr Real.pi_pos.le).trans ht.1, ht.2.le⟩
  have hpoint : (x, ζ, 0) + rootCircleAngleInclusion t = (x, ζ, t) := by
    rw [rootCircleAngleInclusion_apply]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hraw : PointwiseMaterialJetBound p loss A z G
      ((x, ζ, 0) + rootCircleAngleInclusion t) := by
    intro j
    rw [hpoint]
    exact hjets j j le_rfl (x, ζ, t) ⟨hx, hζ, ht'⟩
  have hcomp := PointwiseMaterialJetBound.affine_comp rootCircleAngleInclusion (x, ζ, 0)
    hG.contDiffAt hraw
  have hsample : (fun η => G ((x, ζ, 0) + rootCircleAngleInclusion η)) = u := by
    funext η
    rw [rootCircleAngleInclusion_apply]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  rw [hsample] at hcomp
  have hujet : PointwiseMaterialJetBound p loss A z u t := by
    intro j
    exact (hcomp j).trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (hA j).le
        (pow_le_one₀ (norm_nonneg _) rootCircleAngleInclusion_norm))
      (add_nonneg zero_le_one (apply_nonneg _ _)))
  have hid : PointwiseMaterialJetBound p loss (fun _ => 1 + Real.pi) z
      (fun η : ℝ => η) t :=
    pointwiseMaterialJetBound_linear p loss z (ContinuousLinearMap.id ℝ ℝ) t
      (add_nonneg zero_le_one Real.pi_pos.le)
      ((ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)).trans
        (le_add_of_nonneg_right Real.pi_pos.le))
      (by simpa only [ContinuousLinearMap.id_apply, Real.norm_of_nonneg ht.1] using
        ht.2.le.trans (le_add_of_nonneg_left zero_le_one))
  have hsub := PointwiseMaterialJetBound.sub hu.contDiffAt contDiffAt_id hujet hid
  change ‖iteratedFDeriv ℝ n v θ‖ ≤ B n * (1 + p (n + loss) z)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, he,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hsub n

end ContinuousFlexibility.Analysis
