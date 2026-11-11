import ContinuousFlexibility.Analysis.CoupledCircleCompositionRealization
import ContinuousFlexibility.Analysis.SpacesParameterJets
import ContinuousFlexibility.Analysis.CircleJetEncoding

/-!
# Actual parameter derivatives of circle composition fields

The affine chart parameter is differentiated before passing to the
weighted Hilbert levels. Smooth spatial partials commute with this real
parameter derivative. The original circle model's graph condition also
identifies every level coordinate with the corresponding actual jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem coupled_hasDerivAt_parameter_iteratedDeriv
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (b : ℕ) (t θ : ℝ) :
    HasDerivAt (fun s => iteratedDeriv b (fun x => f (s, x)) θ)
      (iteratedDeriv b (fun x => deriv (fun s => f (s, x)) t) θ) t := by
  have hg : ContDiff ℝ ∞ (fun z : ℝ × PolarPoint => f (z.1, z.2.2)) :=
    hf.comp (contDiff_fst.prodMk contDiff_snd.snd)
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    spaces_hasDerivAt_parameter_mixedDerivative hg 0 b t (0, θ)

variable {T : MaterialData} {γ : ℝ} {M : CircleModelData}

theorem coupledCircleKernelField_affine_contDiff
    (hM : IsCircleModel T γ M) (r k : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (m : ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      coupledCircleKernelField M r k (ψ + z.1 • u) v w m z.2) := by
  have hψ := ((hM.2.2.2.1 ψ).1 m).1
  have hu := ((hM.2.2.2.1 u).1 m).1
  have hv := spaces_contDiff_iteratedDeriv ((hM.2.2.2.1 v).1 m).1 r
  have harg : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      z.2 + (M.decode ψ m z.2 + z.1 * M.decode u m z.2)) :=
    contDiff_snd.add ((hψ.comp contDiff_snd).add
      (contDiff_fst.mul (hu.comp contDiff_snd)))
  have hprod : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ∏ i, M.decode (w i) m z.2) :=
    contDiff_prod (fun i _ => ((hM.2.2.2.1 (w i)).1 m).1.comp contDiff_snd)
  simpa only [coupledCircleKernelField, map_add, map_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] using (hv.comp harg).mul hprod

theorem coupledCircleKernelField_affine_hasDerivAt
    (hM : IsCircleModel T γ M) (r k : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (t : ℝ) (m : ℕ) (θ : ℝ) :
    HasDerivAt (fun s => coupledCircleKernelField M r k (ψ + s • u) v w m θ)
      (coupledCircleKernelField M (r + 1) (k + 1) (ψ + t • u) v (Fin.cons u w) m θ) t := by
  have harg : HasDerivAt
      (fun s : ℝ => θ + (M.decode ψ m θ + s * M.decode u m θ))
      (M.decode u m θ) t := by
    simpa only [zero_add, one_mul] using
      (hasDerivAt_const t θ).add
        ((hasDerivAt_const t (M.decode ψ m θ)).add
          ((hasDerivAt_id' t).mul_const (M.decode u m θ)))
  have hv : HasDerivAt (iteratedDeriv r (M.decode v m))
      (iteratedDeriv (r + 1) (M.decode v m)
        (θ + (M.decode ψ m θ + t * M.decode u m θ)))
      (θ + (M.decode ψ m θ + t * M.decode u m θ)) := by
    rw [iteratedDeriv_succ]
    exact ((spaces_contDiff_iteratedDeriv ((hM.2.2.2.1 v).1 m).1 r).differentiable
      (by simp) _).hasDerivAt
  simpa only [coupledCircleKernelField, map_add, map_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Function.comp_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, mul_assoc] using
    (hv.comp t harg).mul_const (∏ i, M.decode (w i) m θ)

theorem coupledCircleKernelField_weightedJet_affine_hasDerivAt
    (hM : IsCircleModel T γ M) (r k b c : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (t : ℝ) (m : ℕ) (θ : ℝ) :
    HasDerivAt
      (fun s => (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv b (coupledCircleKernelField M r k (ψ + s • u) v w m) θ)
      ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv b
          (coupledCircleKernelField M (r + 1) (k + 1) (ψ + t • u) v (Fin.cons u w) m) θ) t := by
  have hd := coupled_hasDerivAt_parameter_iteratedDeriv
    (coupledCircleKernelField_affine_contDiff hM r k ψ u v w m) b t θ
  have he : (fun x => deriv
      (fun s => coupledCircleKernelField M r k (ψ + s • u) v w m x) t) =
      coupledCircleKernelField M (r + 1) (k + 1) (ψ + t • u) v (Fin.cons u w) m := by
    funext x
    exact (coupledCircleKernelField_affine_hasDerivAt hM r k ψ u v w t m x).deriv
  rw [he] at hd
  exact hd.const_mul _

/-- The frozen weak graph and its zero coordinate determine all actual
angular jet coordinates of any admissible circle model. -/
theorem coupled_circle_model_level_ae
    (hM : IsCircleModel T γ M) (u : M.Space) (s m : ℕ) (j : CircleJetIndex s) :
    ((((u.val s).val m j)) : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val (M.decode u m) θ) := by
  let g : ℝ → ℝ := fun θ => T.H (T.sample m) ^ (-γ) * M.decode u m θ
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul ((hM.2.2.2.1 u).1 m).1
  have hp : Function.Periodic g Real.pi := by
    intro θ
    exact congrArg (T.H (T.sample m) ^ (-γ) * ·) (((hM.2.2.2.1 u).1 m).2 θ)
  have h₀ : MemLp g 2 angleMeasure := memLp_angleMeasure_of_continuous hg.continuous
  have hb := memLp_angleMeasure_iteratedDeriv_of_contDiff hg (j.val 0).val
  have hzero : (u.val s).val m (zeroCircleJetIndex s) = h₀.toLp g := by
    apply Lp.ext
    exact (hM.2.2.2.2.2.2.1 u s m).trans (MemLp.coeFn_toLp h₀).symm
  have hgraph : (u.val s).val ∈ circleJetGraph T s := by
    rw [← hM.1 s]
    exact (u.val s).property
  obtain ⟨d, hd, hcoord⟩ := hgraph m j
  have hweak := hasWeakAngularDerivative_toLp_iteratedDeriv hg hp (j.val 0).val h₀ hb
  rw [← hzero] at hweak
  have he := hasWeakAngularDerivative_unique hd hweak
  rw [he] at hcoord
  filter_upwards [hcoord, MemLp.coeFn_toLp hb] with θ hθ hder
  rw [hθ, hder]
  change T.M (T.sample m) ^ (j.val 1).val *
      iteratedDeriv (j.val 0).val (fun x => T.H (T.sample m) ^ (-γ) * M.decode u m x) θ = _
  rw [iteratedDeriv_const_mul_field, mul_assoc]

end ContinuousFlexibility.Statements
