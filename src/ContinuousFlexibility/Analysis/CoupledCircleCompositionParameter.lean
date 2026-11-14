module

public import ContinuousFlexibility.Analysis.CoupledCircleCompositionRealization
public import ContinuousFlexibility.Analysis.SpacesParameterJets
public import ContinuousFlexibility.Analysis.CircleJetEncoding

/-!
# Actual parameter derivatives of circle composition fields

The affine chart parameter is differentiated before passing to the
weighted Hilbert levels. Smooth spatial partials commute with this real
parameter derivative. The original circle model's graph condition also
identifies every level coordinate with the corresponding actual jet.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coupled_hasDerivAt_parameter_iteratedDeriv
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (b : ℕ) (t θ : ℝ) :
    HasDerivAt (fun s => iteratedDeriv b (fun x => f (s, x)) θ)
      (iteratedDeriv b (fun x => deriv (fun s => f (s, x)) t) θ) t := by
  have hg : ContDiff ℝ ∞ (fun z : ℝ × PolarPoint => f (z.1, z.2.2)) :=
    hf.comp (contDiff_fst.prodMk contDiff_snd.snd)
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    spaces_hasDerivAt_parameter_mixedDerivative hg 0 b t (0, θ)

private theorem coupled_scalar_affine_contDiff {k : ℕ}
    {ψ u v : ℝ → ℝ} {w : Fin k → ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (r : ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      iteratedDeriv r v (z.2 + (ψ z.2 + z.1 * u z.2)) * ∏ i, w i z.2) := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z.2 + (ψ z.2 + z.1 * u z.2)) :=
    contDiff_snd.add ((hψ.comp contDiff_snd).add
      (contDiff_fst.mul (hu.comp contDiff_snd)))
  have hprod : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ∏ i, w i z.2) :=
    contDiff_prod (fun i _ => (hw i).comp contDiff_snd)
  simpa only [Function.comp_apply] using
    ((spaces_contDiff_iteratedDeriv hv r).comp harg).mul hprod

private theorem coupled_scalar_affine_hasDerivAt {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (r : ℕ) (a b c θ t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedDeriv r v (θ + (a + s * b)) * c)
      (iteratedDeriv (r + 1) v (θ + (a + t * b)) * (b * c)) t := by
  have harg : HasDerivAt (fun s : ℝ => θ + (a + s * b)) b t := by
    simpa only [one_mul] using
      (((hasDerivAt_id' t).mul_const b).const_add a).const_add θ
  have houter : HasDerivAt (iteratedDeriv r v)
      (iteratedDeriv (r + 1) v (θ + (a + t * b))) (θ + (a + t * b)) := by
    rw [iteratedDeriv_succ]
    exact ((spaces_contDiff_iteratedDeriv hv r).differentiable (by simp) _).hasDerivAt
  simpa only [Function.comp_apply, mul_assoc] using (houter.comp t harg).mul_const c

private theorem coupled_linear_decode_affine {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] (ℕ → ℝ → ℝ)) (ψ u : E) (t : ℝ) (m : ℕ) (θ : ℝ) :
    L (ψ + t • u) m θ = L ψ m θ + t * L u m θ := by
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem coupled_scalar_prod_cons {E : Type*} {k : ℕ}
    (f : E → ℝ) (u : E) (w : Fin k → E) :
    (∏ i : Fin (k + 1), f ((Fin.cons u w : Fin (k + 1) → E) i)) =
      f u * ∏ i, f (w i) :=
  Fin.prod_univ_succ (fun i : Fin (k + 1) => f ((Fin.cons u w : Fin (k + 1) → E) i))

variable {T : MaterialData} {γ : ℝ} {M : CircleModelData}

private theorem coupledCircleKernelField_affine_eq (r k : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (t : ℝ) (m : ℕ) (θ : ℝ) :
    coupledCircleKernelField M r k (ψ + t • u) v w m θ =
      iteratedDeriv r (M.decode v m)
        (θ + (M.decode ψ m θ + t * M.decode u m θ)) * ∏ i, M.decode (w i) m θ := by
  exact congrArg (fun a : ℝ =>
    iteratedDeriv r (M.decode v m) (θ + a) * ∏ i, M.decode (w i) m θ)
      (coupled_linear_decode_affine M.decode ψ u t m θ)

theorem coupledCircleKernelField_affine_contDiff
    (hM : IsCircleModel T γ M) (r k : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (m : ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      coupledCircleKernelField M r k (ψ + z.1 • u) v w m z.2) := by
  have he : (fun z : ℝ × ℝ =>
      coupledCircleKernelField M r k (ψ + z.1 • u) v w m z.2) =
      (fun z : ℝ × ℝ => iteratedDeriv r (M.decode v m)
        (z.2 + (M.decode ψ m z.2 + z.1 * M.decode u m z.2)) *
          ∏ i, M.decode (w i) m z.2) := by
    funext z
    exact coupledCircleKernelField_affine_eq r k ψ u v w z.1 m z.2
  rw [he]
  exact coupled_scalar_affine_contDiff ((hM.2.2.2.1 ψ).1 m).1
    ((hM.2.2.2.1 u).1 m).1 ((hM.2.2.2.1 v).1 m).1
    (fun i => ((hM.2.2.2.1 (w i)).1 m).1) r

theorem coupledCircleKernelField_affine_hasDerivAt
    (hM : IsCircleModel T γ M) (r k : ℕ)
    (ψ u v : M.Space) (w : Fin k → M.Space) (t : ℝ) (m : ℕ) (θ : ℝ) :
    HasDerivAt (fun s => coupledCircleKernelField M r k (ψ + s • u) v w m θ)
      (coupledCircleKernelField M (r + 1) (k + 1) (ψ + t • u) v (Fin.cons u w) m θ) t := by
  have he : (fun s : ℝ => coupledCircleKernelField M r k (ψ + s • u) v w m θ) =
      (fun s : ℝ => iteratedDeriv r (M.decode v m)
        (θ + (M.decode ψ m θ + s * M.decode u m θ)) * ∏ i, M.decode (w i) m θ) := by
    funext s
    exact coupledCircleKernelField_affine_eq r k ψ u v w s m θ
  have hd : coupledCircleKernelField M (r + 1) (k + 1)
      (ψ + t • u) v (Fin.cons u w) m θ =
      iteratedDeriv (r + 1) (M.decode v m)
        (θ + (M.decode ψ m θ + t * M.decode u m θ)) *
          (M.decode u m θ * ∏ i, M.decode (w i) m θ) := by
    exact (coupledCircleKernelField_affine_eq (r + 1) (k + 1)
      ψ u v (Fin.cons u w) t m θ).trans
        (congrArg (fun a : ℝ => iteratedDeriv (r + 1) (M.decode v m)
          (θ + (M.decode ψ m θ + t * M.decode u m θ)) * a)
            (coupled_scalar_prod_cons (fun a : M.Space => M.decode a m θ) u w))
  exact (congrArg₂ (fun (f : ℝ → ℝ) (d : ℝ) => HasDerivAt f d t) he hd).mpr
    (coupled_scalar_affine_hasDerivAt ((hM.2.2.2.1 v).1 m).1 r
      (M.decode ψ m θ) (M.decode u m θ) (∏ i, M.decode (w i) m θ) θ t)

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

private theorem coupled_circle_graph_coordinate_ae {s : ℕ}
    (z : CircleJetHilbert s) (hz : z ∈ circleJetGraph T s) (m : ℕ)
    (j : CircleJetIndex s) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (hbase : (z m (zeroCircleJetIndex s) : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => T.H (T.sample m) ^ (-γ) * f θ)) :
    (z m j : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val f θ) := by
  let g : ℝ → ℝ := fun θ => T.H (T.sample m) ^ (-γ) * f θ
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul hf
  have hgp : Function.Periodic g Real.pi := by
    intro θ
    exact congrArg (T.H (T.sample m) ^ (-γ) * ·) (hp θ)
  have h₀ : MemLp g 2 angleMeasure := memLp_angleMeasure_of_continuous hg.continuous
  have hb : MemLp (iteratedDeriv (j.val 0).val g) 2 angleMeasure :=
    memLp_angleMeasure_iteratedDeriv_of_contDiff hg (j.val 0).val
  have hzero : z m (zeroCircleJetIndex s) = h₀.toLp g := by
    apply Lp.ext
    exact hbase.trans (MemLp.coeFn_toLp h₀).symm
  have hdata := hz m j
  let d : AngleL2 := hdata.choose
  have hd : HasWeakAngularDerivative (z m (zeroCircleJetIndex s)) d (j.val 0).val :=
    hdata.choose_spec.1
  have hcoord : (z m j : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => T.M (T.sample m) ^ (j.val 1).val * d θ) := hdata.choose_spec.2
  have hweak : HasWeakAngularDerivative (z m (zeroCircleJetIndex s))
      (hb.toLp (iteratedDeriv (j.val 0).val g)) (j.val 0).val := by
    rw [hzero]
    exact hasWeakAngularDerivative_toLp_iteratedDeriv hg hgp (j.val 0).val h₀ hb
  have he : d = hb.toLp (iteratedDeriv (j.val 0).val g) :=
    hasWeakAngularDerivative_unique hd hweak
  rw [he] at hcoord
  filter_upwards [hcoord, MemLp.coeFn_toLp hb] with θ hθ hder
  rw [hθ, hder]
  change T.M (T.sample m) ^ (j.val 1).val *
      iteratedDeriv (j.val 0).val (fun x => T.H (T.sample m) ^ (-γ) * f x) θ = _
  rw [iteratedDeriv_const_mul_field, mul_assoc]

/-- The frozen weak graph and its zero coordinate determine all actual
angular jet coordinates of any admissible circle model. -/
theorem coupled_circle_model_level_ae
    (hM : IsCircleModel T γ M) (u : M.Space) (s m : ℕ) (j : CircleJetIndex s) :
    ((((u.val s).val m j)) : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv (j.val 0).val (M.decode u m) θ) := by
  have hgraph : (u.val s).val ∈ circleJetGraph T s :=
    (congrArg (fun V : Set (CircleJetHilbert s) => (u.val s).val ∈ V) (hM.1 s)).mp
      (u.val s).property
  exact coupled_circle_graph_coordinate_ae (u.val s).val hgraph m j (M.decode u m)
    ((hM.2.2.2.1 u).1 m).1 ((hM.2.2.2.1 u).1 m).2 (hM.2.2.2.2.2.2.1 u s m)

end ContinuousFlexibility.Statements
