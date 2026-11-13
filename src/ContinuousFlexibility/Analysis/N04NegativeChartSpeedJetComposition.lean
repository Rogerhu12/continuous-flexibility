import ContinuousFlexibility.Analysis.N04NegativeGeometryFlowCoefficientBounds
import ContinuousFlexibility.Analysis.N04NegativeChartVariationForcing

/-!
# Original mixed speed jets along the actual spatial flow

The finite state slots remain fixed while the radial parameters and
initial angle vary. The graph map retains these radial parameters.
Its positive spatial jets of order j have weight j-1, so composition
with a raw mixed speed jet spends exactly the requested spatial order.
The state-order power and any marked height factor remain linear.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The output uses the original speed tower on the same trajectory.
Only the actual state-free spatial flow jets enter the inner bounds. -/
theorem n04NegativeChart_speedJet_along_flow_weighted_prefix
    {G Θ : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ) (γ : V → E) (hγ : ContDiff ℝ ∞ γ)
    (L K D : ℕ) (v : Fin L → E × ℝ) (t : ℝ) (x : V × ℝ)
    {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hρ : 1 ≤ ρ)
    (hraw : ∀ j, j ≤ K →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ =>
        flowSpeedJointField J L (γ p.1) v (t, p.2))
          (x.1, Θ (γ x.1, (t, x.2)))‖ ≤ A * ρ ^ (D + j))
    (hflow : ∀ j, 1 ≤ j → j ≤ K →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => Θ (γ p.1, (t, p.2))) x‖ ≤
        B * ρ ^ (j - 1)) :
    ∀ k, k ≤ K →
      ‖iteratedFDeriv ℝ k (fun p : V × ℝ =>
        flowSpeedJointField J L (γ p.1) v (t, Θ (γ p.1, (t, p.2)))) x‖ ≤
          (K.factorial : ℝ) * A * B ^ K * ρ ^ (D + k) := by
  let F : V × ℝ → ℝ := fun p => flowSpeedJointField J L (γ p.1) v (t, p.2)
  let Φ : V × ℝ → V × ℝ := fun p => (p.1, Θ (γ p.1, (t, p.2)))
  have he : F = fun p => iteratedFDeriv ℝ L G (γ p.1, (t, p.2))
      (fun i => speedTimeSliceInjection (v i)) :=
    funext (fun p => flowSpeedJointField_eq_joint J hG L (γ p.1) v (t, p.2))
  have hF : ContDiff ℝ ∞ F := by
    rw [he]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin L => E × PolarPoint) ℝ
      (fun i => speedTimeSliceInjection (v i))).contDiff.comp
        ((hG.iteratedFDeriv_right (m := ∞) (i := L) (by simp)).comp
          ((hγ.comp contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd)))
  have hθ : ContDiff ℝ ∞ (fun p : V × ℝ => Θ (γ p.1, (t, p.2))) :=
    hΘ.comp ((hγ.comp contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd))
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_fst.prodMk hθ
  have hinner (j : ℕ) (hj : 1 ≤ j) (hjK : j ≤ K) :
      ‖iteratedFDeriv ℝ j Φ x‖ ≤ B * ρ ^ (j - 1) := by
    have hp : ‖iteratedFDeriv ℝ j (fun p : V × ℝ => p.1) x‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.coe_fst'] using
        (flowJet_norm_iteratedFDeriv_clm_le
          (ContinuousLinearMap.fst ℝ V ℝ) hj x).trans
          (ContinuousLinearMap.norm_fst_le ℝ V ℝ)
    change ‖iteratedFDeriv ℝ j
      (fun p : V × ℝ => (p.1, Θ (γ p.1, (t, p.2)))) x‖ ≤ _
    rw [iteratedFDeriv_prodMk contDiffAt_fst hθ.contDiffAt (by simp),
      ContinuousMultilinearMap.opNorm_prod]
    exact max_le (hp.trans (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hρ)))
      (hflow j hj hjK)
  intro k hk
  have houter (j : ℕ) (hjk : j ≤ k) :
      ‖iteratedFDeriv ℝ j F (Φ x)‖ ≤ (A * ρ ^ D) * ρ ^ j :=
    (hraw j (hjk.trans hk)).trans_eq (by rw [pow_add, mul_assoc])
  have hb := n04NegativeGeometry_weighted_composition_jet_le hΦ hF x k hB hρ
    houter (fun j hj hjk => hinner j hj (hjk.trans hk))
  have hfac : (k.factorial : ℝ) ≤ (K.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le_factorial hk
  calc
    _ ≤ (k.factorial : ℝ) * (A * ρ ^ D) * B ^ k * ρ ^ k := hb
    _ ≤ (K.factorial : ℝ) * (A * ρ ^ D) * B ^ K * ρ ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul
          (mul_le_mul_of_nonneg_right hfac
            (mul_nonneg hA (pow_nonneg (zero_le_one.trans hρ) _)))
          (pow_le_pow_right₀ hB hk) (pow_nonneg (zero_le_one.trans hB) _)
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg hA (pow_nonneg (zero_le_one.trans hρ) _))))
        (pow_nonneg (zero_le_one.trans hρ) _)
    _ = _ := by rw [pow_add]; ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_speedJet_along_flow_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_speedJet_along_flow_weighted_prefix
