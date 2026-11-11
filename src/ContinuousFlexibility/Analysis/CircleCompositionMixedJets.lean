import ContinuousFlexibility.Analysis.CircleChartCompositionJets
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Ordinary mixed derivatives of the actual composition jets

The displayed parameter jets are jointly smooth in the scalar line
parameter and angle. The already proved commutation of the actual
cylinder partial derivatives therefore identifies every angular jet of
the parameter derivative, rather than postulating mixed derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_angular_jet_of_contDiff
    {F G : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    (hderiv : ∀ t θ : ℝ, HasDerivAt (fun q => F (q, θ)) (G (t, θ)) t)
    (b : ℕ) (t θ : ℝ) :
    HasDerivAt (fun q => iteratedDeriv b (fun y => F (q, y)) θ)
      (iteratedDeriv b (fun y => G (t, y)) θ) t := by
  have hG : radialPartial F = G := by
    funext p
    exact (deriv_cylinder_radial_slice (hF.differentiable (by simp)) p.1 p.2).symm.trans
      (hderiv p.1 p.2).deriv
  have hjoint : ContDiff ℝ ∞
      (fun p : PolarPoint => iteratedDeriv b (fun y => F (p.1, y)) p.2) := by
    have h := contDiffOn_mixedDerivative isOpen_univ hF.contDiffOn 0 b
    simpa only [mixedDerivative, iteratedDeriv_zero] using contDiffOn_univ.mp h
  have hslice : ContDiff ℝ ∞
      (fun q => iteratedDeriv b (fun y => F (q, y)) θ) :=
    hjoint.comp (contDiff_id.prodMk contDiff_const)
  have hd : deriv (fun q => iteratedDeriv b (fun y => F (q, y)) θ) t =
      iteratedDeriv b (fun y => G (t, y)) θ := by
    calc
      _ = mixedDerivative 1 b F (t, θ) := by
        simp only [mixedDerivative, iteratedDeriv_one]
      _ = mixedDerivative 0 b (radialPartial F) (t, θ) :=
        (mixedDerivative_radialPartial isOpen_univ hF.contDiffOn 0 b (mem_univ _)).symm
      _ = _ := by rw [hG]; simp only [mixedDerivative, iteratedDeriv_zero]
  simpa only [hd] using (hslice.differentiable (by simp) t).hasDerivAt

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleCompositionPhase_scalar_angle_contDiff
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (x w : S.Space × S.Space) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : PolarPoint =>
      circleCompositionPhase travel (x + p.1 • w) m p.2) := by
  have heq : (fun p : PolarPoint => circleCompositionPhase travel (x + p.1 • w) m p.2) =
      (fun p => circleCompositionPhase travel x m p.2 + p.1 * S.decode w.1 m p.2) := by
    funext p
    exact circleCompositionPhase_line travel x w m p.2 p.1
  rw [heq]
  exact ((circleCompositionPhase_contDiff hS travel x m).comp contDiff_snd).add
    (contDiff_fst.mul (((hS.2.2.2.1 w.1).1 m).1.comp contDiff_snd))

theorem circleChartCompositionJets_scalar_angle_contDiff
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (n : ℕ) (x w : S.Space × S.Space) (v : Fin n → S.Space × S.Space) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : PolarPoint =>
      circleChartCompositionJets hS travel n (x + p.1 • w) v m p.2) := by
  classical
  let φ : PolarPoint → ℝ := fun p => circleCompositionPhase travel (x + p.1 • w) m p.2
  have hφ : ContDiff ℝ ∞ φ := circleCompositionPhase_scalar_angle_contDiff hS travel x w m
  have houter (u : S.Space) (a : ℕ) : ContDiff ℝ ∞
      (fun p : PolarPoint => iteratedDeriv a (S.decode u m) (φ p)) := by
    have hu : ContDiff ℝ ∞ (iteratedDeriv a (S.decode u m)) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv a ((hS.2.2.2.1 u).1 m).1
    exact hu.comp hφ
  have hmain : ContDiff ℝ ∞ (fun p : PolarPoint =>
      iteratedDeriv n (S.decode (x + p.1 • w).2 m) (φ p)) := by
    have heq : (fun p : PolarPoint => iteratedDeriv n (S.decode (x + p.1 • w).2 m) (φ p)) =
        (fun p => iteratedDeriv n (S.decode x.2 m) (φ p) +
          p.1 * iteratedDeriv n (S.decode w.2 m) (φ p)) := by
      funext p
      exact circleAngularJetEvaluation_line hS x.2 w.2 n m p.1 (φ p)
    rw [heq]
    exact (houter x.2 n).add (contDiff_fst.mul (houter w.2 n))
  have hin (i : Fin n) : ContDiff ℝ ∞
      (fun p : PolarPoint => S.decode (v i).1 m p.2) :=
    ((hS.2.2.2.1 (v i).1).1 m).1.comp contDiff_snd
  have heq : (fun p : PolarPoint =>
      circleChartCompositionJets hS travel n (x + p.1 • w) v m p.2) =
      (fun p => iteratedDeriv n (S.decode (x + p.1 • w).2 m) (φ p) *
        ∏ i, S.decode (v i).1 m p.2 +
      ∑ i : Fin n, iteratedDeriv (n - 1) (S.decode (v i).2 m) (φ p) *
        ∏ j ∈ Finset.univ.erase i, S.decode (v j).1 m p.2) := by
    funext p
    exact circleChartCompositionJets_apply hS travel n (x + p.1 • w) v m p.2
  rw [heq]
  exact (hmain.mul (contDiff_prod (fun i _ => hin i))).add
    (ContDiff.sum (fun i _ => (houter (v i).2 (n - 1)).mul
      (contDiff_prod (fun j _ => hin j))))

/-- The scalar derivative hypothesis required by the genuine circle
tower assembly holds for every angular derivative of the actual jets. -/
theorem circleChartCompositionJets_angular_line_hasDerivAt
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (n : ℕ) (x w : S.Space × S.Space) (v : Fin n → S.Space × S.Space)
    (t : ℝ) (m b : ℕ) (θ : ℝ) :
    HasDerivAt (fun q : ℝ =>
      iteratedDeriv b (circleChartCompositionJets hS travel n (x + q • w) v m) θ)
      (iteratedDeriv b (circleChartCompositionJets hS travel (n + 1)
        (x + t • w) (Fin.cons w v) m) θ) t :=
  hasDerivAt_angular_jet_of_contDiff
    (circleChartCompositionJets_scalar_angle_contDiff hS travel n x w v m)
    (fun q y => circleChartCompositionJets_line_hasDerivAt hS travel n x w v m y q) b t θ

end ContinuousFlexibility.Statements
