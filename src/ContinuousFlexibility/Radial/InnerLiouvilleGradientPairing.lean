import ContinuousFlexibility.Radial.InnerLiouvilleEnergyLift

/-!
# Exact gradient pairings in the actual Liouville coordinates

Restriction and zero extension are adjoints. On a supported test the
restriction loses no pairing, while the intervening Liouville map is
an actual linear isometry. The physical gradient pairing therefore
equals the model pairing after subtracting the density drift.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem innerL2ZeroExtension_inner (μ : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (f g : Lp ℝ 2 (μ.restrict S)) :
    ⟪innerL2ZeroExtension μ S f, innerL2ZeroExtension μ S g⟫_ℝ = ⟪f, g⟫_ℝ := by
  calc
    _ = ⟪(innerL2ZeroExtension μ S).adjoint (innerL2ZeroExtension μ S f), g⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    _ = _ := by
      rw [innerL2ZeroExtension_adjoint, innerL2Restriction_zeroExtension μ S hS]

theorem innerL2Restriction_inner_of_support (μ : Measure ℝ) (S : Set ℝ)
    (hS : MeasurableSet S) (f g : Lp ℝ 2 μ)
    (hg : (g : ℝ → ℝ) =ᵐ[μ.restrict Sᶜ] (fun _ => 0)) :
    ⟪LpToLpRestrictCLM ℝ ℝ ℝ μ 2 S f, LpToLpRestrictCLM ℝ ℝ ℝ μ 2 S g⟫_ℝ =
      ⟪f, g⟫_ℝ := by
  have he : innerL2ZeroExtension μ S (LpToLpRestrictCLM ℝ ℝ ℝ μ 2 S g) = g := by
    apply Lp.ext
    filter_upwards [innerL2ZeroExtension_restriction_ae μ S hS g,
      ae_imp_of_ae_restrict hg] with x hx hgx
    rw [hx]
    by_cases hi : x ∈ S
    · rw [indicator_of_mem hi]
    · rw [indicator_of_notMem hi]
      exact (hgx hi).symm
  calc
    _ = ⟪f, innerL2ZeroExtension μ S (LpToLpRestrictCLM ℝ ℝ ℝ μ 2 S g)⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = _ := by rw [he]

theorem innerLiouvilleDriftMultiplier_adjoint (s : ℝ → ℝ) (a b : ℝ)
    (hs : ContDiff ℝ ∞ s) (hsp : ∀ x ∈ Icc a b, 0 < s x) :
    (innerLiouvilleDriftMultiplier s a b hs hsp).adjoint =
      innerLiouvilleDriftMultiplier s a b hs hsp := by
  unfold innerLiouvilleDriftMultiplier
  exact innerLiouvilleVelocityMultiplier_adjoint _ _ _ _ _ _ _

theorem innerLiouvilleDriftMultiplier_inner (s : ℝ → ℝ) (a b : ℝ)
    (hs : ContDiff ℝ ∞ s) (hsp : ∀ x ∈ Icc a b, 0 < s x) (f g : RadialL2) :
    ⟪innerLiouvilleDriftMultiplier s a b hs hsp f, g⟫_ℝ =
      ⟪f, innerLiouvilleDriftMultiplier s a b hs hsp g⟫_ℝ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (innerLiouvilleDriftMultiplier s a b hs hsp) f g
  rw [innerLiouvilleDriftMultiplier_adjoint s a b hs hsp] at h
  exact h.symm

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

theorem innerLiouvilleGradientLift_pairing (f d P Pd : RadialL2)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0)) :
    ⟪innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d),
      innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (P, Pd)⟫_ℝ =
      ⟪d - innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2) f,
        Pd - innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2) P⟫_ℝ := by
  let M := innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2)
  have htest : ((Pd - M P : RadialL2) : ℝ → ℝ) =ᵐ[
      volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub Pd (M P)), hPd,
      ae_restrict_of_ae (innerLiouvilleDriftMultiplier_ae s a b hs
        (fun x hx => (hp x hx).2.2) P),
      ae_restrict_mem measurableSet_Ioo.compl] with x hsub hpd hM hout
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hpd, hM, innerLiouvilleModelVelocity, indicator_of_notMem hout,
      zero_mul, sub_zero]
  rw [innerLiouvilleGradientLift_apply, innerLiouvilleGradientLift_apply,
    innerL2ZeroExtension_inner _ _ measurableSet_Ioo, LinearIsometryEquiv.inner_map_map]
  exact innerL2Restriction_inner_of_support volume (Ioo a b) measurableSet_Ioo _ _ htest

end ContinuousFlexibility.Radial
