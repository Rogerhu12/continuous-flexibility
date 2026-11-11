import ContinuousFlexibility.Analysis.PositiveConformalDensityAlgebra
import ContinuousFlexibility.Geometry.EuclideanRigidity

/-!
# The actual principal density of the finite conformal construction

The finite recurrence, rather than an assumed boundary normal form,
forces the three actual principal-density discrepancies to have zero
radial jets. Degree n+1 suffices through order n. The matrix fields need
only be smooth at the boundary points; all neighborhoods used below
come from ordinary continuity and positivity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem radialBoundaryJet_mul_zero
    {f g : PolarPoint → ℝ} {c θ : ℝ} {n k : ℕ}
    (hf : ContDiffAt ℝ ∞ f (c, θ)) (hg : ContDiffAt ℝ ∞ g (c, θ))
    (hzero : ∀ j ≤ n, radialBoundaryJet g c j θ = 0) (hk : k ≤ n) :
    radialBoundaryJet (fun p => f p * g p) c k θ = 0 := by
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hfs := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := f) c hf hline
  have hgs := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ)) (g := g) c hg hline
  change iteratedDeriv k (fun r => f (r, θ) * g (r, θ)) c = 0
  rw [iteratedDeriv_fun_mul
    (hfs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hgs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
  apply Finset.sum_eq_zero
  intro j _
  have hj := hzero (k - j) ((Nat.sub_le k j).trans hk)
  change iteratedDeriv (k - j) (fun r => g (r, θ)) c = 0 at hj
  rw [hj, mul_zero]

private theorem radialBoundaryJet_linear_zero
    {a b s t : PolarPoint → ℝ} {c θ : ℝ} {n k : ℕ}
    (ha : ContDiffAt ℝ ∞ a (c, θ)) (hb : ContDiffAt ℝ ∞ b (c, θ))
    (hs : ContDiffAt ℝ ∞ s (c, θ)) (ht : ContDiffAt ℝ ∞ t (c, θ))
    (hszero : ∀ j ≤ n, radialBoundaryJet s c j θ = 0)
    (htzero : ∀ j ≤ n, radialBoundaryJet t c j θ = 0) (hk : k ≤ n) :
    radialBoundaryJet (fun p => a p * s p + b p * t p) c k θ = 0 := by
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hleft := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
    (g := fun p => a p * s p) c (ha.mul hs) hline
  have hright := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
    (g := fun p => b p * t p) c (hb.mul ht) hline
  change iteratedDeriv k (fun r => a (r, θ) * s (r, θ) + b (r, θ) * t (r, θ)) c = 0
  rw [iteratedDeriv_fun_add
    (hleft.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hright.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
  simpa only [zero_add] using congrArg₂ (fun x y : ℝ => x + y)
    (radialBoundaryJet_mul_zero ha hs hszero hk)
    (radialBoundaryJet_mul_zero hb ht htzero hk)

private theorem radialBoundaryJet_zero_of_germ
    {f g : PolarPoint → ℝ} {c θ : ℝ} {k : ℕ}
    (he : f =ᶠ[𝓝 (c, θ)] g) (hg : radialBoundaryJet g c k θ = 0) :
    radialBoundaryJet f c k θ = 0 := by
  have hline : Continuous (fun r : ℝ => (r, θ)) := continuous_id.prodMk continuous_const
  have ht := ((he.comp_tendsto (hline.tendsto c)).iteratedDeriv k).eq_of_nhds
  exact ht.trans hg

/-- Actual zero jets of the two first-order residuals imply zero jets
of the three principal discrepancies. The next theorem supplies these
residual jets by the explicit finite recursion. -/
theorem positiveConformalDensity_zero_jets_of_residual
    {A : SymmetricCoefficients} {X : Bool → PolarPoint → ℝ} {c θ : ℝ} {n : ℕ}
    (hX : ∀ side, ContDiff ℝ ∞ (X side))
    (ha : ContDiffAt ℝ ∞ A.a (c, θ)) (hb : ContDiffAt ℝ ∞ A.b (c, θ))
    (hc : ContDiffAt ℝ ∞ A.c (c, θ))
    (ha0 : 0 < A.a (c, θ))
    (hdet : 0 < A.a (c, θ) * A.c (c, θ) - A.b (c, θ) ^ 2)
    (hJ0 : 0 < planeJacobian (fun p => (X false p, X true p)) (c, θ))
    (hzero : ∀ side j, j ≤ n → radialBoundaryJet
      (positiveConformalResidual (positiveConformalSpeed A) (positiveConformalShear A) X side)
      c j θ = 0) :
    let B := coordinatePrincipalDensity A (fun p => (X false p, X true p))
      (positiveConformalHeight A)
    ∀ k ≤ n,
      radialBoundaryJet (fun p => B.a p - 1) c k θ = 0 ∧
        radialBoundaryJet B.b c k θ = 0 ∧
        radialBoundaryJet (fun p => B.c p - 1) c k θ = 0 := by
  let d := positiveConformalSpeed A
  let e := positiveConformalShear A
  let s := positiveConformalResidual d e X false
  let t := positiveConformalResidual d e X true
  let u := angularPartial (X false)
  let v := angularPartial (X true)
  let J := planeJacobian (fun p => (X false p, X true p))
  have hfields := contDiffAt_positiveConformalFields ha hb hc ha0 hdet
  have hd : ContDiffAt ℝ ∞ d (c, θ) := hfields.1
  have he : ContDiffAt ℝ ∞ e (c, θ) := hfields.2.1
  have hu : ContDiffAt ℝ ∞ u (c, θ) :=
    (contDiff_cylinder_angularPartial (hX false)).contDiffAt
  have hv : ContDiffAt ℝ ∞ v (c, θ) :=
    (contDiff_cylinder_angularPartial (hX true)).contDiffAt
  have hs : ContDiffAt ℝ ∞ s (c, θ) :=
    (contDiff_cylinder_radialPartial (hX false)).contDiffAt.sub
      ((he.mul hu).add (hd.mul hv))
  have ht : ContDiffAt ℝ ∞ t (c, θ) :=
    (contDiff_cylinder_radialPartial (hX true)).contDiffAt.sub
      ((he.mul hv).add (hd.neg.mul hu))
  have hJ : ContDiffAt ℝ ∞ J (c, θ) :=
    contDiffAt_planeJacobian (((hX false).prodMk (hX true)).contDiffAt)
  have hd0 : d (c, θ) ≠ 0 := (positiveConformal_values ha0 hdet).1.ne'
  have hPa := (hv.add (hs.fun_div hd hd0)).fun_div hJ hJ0.ne'
  have hQa := hu.fun_div hJ hJ0.ne'
  have hPb := (hu.neg.add (ht.fun_div hd hd0)).fun_div hJ hJ0.ne'
  have hQb := hv.fun_div hJ hJ0.ne'
  have hPc := hv.neg.fun_div hJ hJ0.ne'
  have hNearA : ∀ᶠ p in 𝓝 (c, θ), 0 < A.a p :=
    ha.continuousAt.eventually (Ioi_mem_nhds ha0)
  have hNearDet : ∀ᶠ p in 𝓝 (c, θ), 0 < A.a p * A.c p - A.b p ^ 2 :=
    ((ha.mul hc).sub (hb.pow 2)).continuousAt.eventually (Ioi_mem_nhds hdet)
  have hNearJ : ∀ᶠ p in 𝓝 (c, θ), 0 < J p :=
    hJ.continuousAt.eventually (Ioi_mem_nhds hJ0)
  have hGerm : ∀ᶠ p in 𝓝 (c, θ),
      let B := coordinatePrincipalDensity A (fun q => (X false q, X true q))
        (positiveConformalHeight A)
      B.a p - 1 = ((v p + s p / d p) / J p) * s p + (u p / J p) * t p ∧
        B.b p = ((-u p + t p / d p) / J p) * s p + (v p / J p) * t p ∧
        B.c p - 1 = (-v p / J p) * s p + ((-u p + t p / d p) / J p) * t p := by
    filter_upwards [hNearA, hNearDet, hNearJ] with p hpA hpD hpJ
    exact positiveConformalDensity_remainder
      (fun side => (hX side).differentiable (by simp) p) hpA hpD hpJ
  intro k hk
  refine ⟨?_, ?_, ?_⟩
  · exact radialBoundaryJet_zero_of_germ (hGerm.mono fun _ hp => hp.1)
      (radialBoundaryJet_linear_zero hPa hQa hs ht (hzero false) (hzero true) hk)
  · exact radialBoundaryJet_zero_of_germ (hGerm.mono fun _ hp => hp.2.1)
      (radialBoundaryJet_linear_zero hPb hQb hs ht (hzero false) (hzero true) hk)
  · exact radialBoundaryJet_zero_of_germ (hGerm.mono fun _ hp => hp.2.2)
      (radialBoundaryJet_linear_zero hPc hPb hs ht (hzero false) (hzero true) hk)

/-- The explicit polynomial, with no normal-form or zero-jet hypothesis,
has positive boundary Jacobian and the unit principal density through
the prescribed finite order. This works at regular positive endpoints. -/
theorem positiveConformalBoundaryPolynomial_density_jets
    {A : SymmetricCoefficients} {c : ℝ}
    (ha : ∀ θ, ContDiffAt ℝ ∞ A.a (c, θ))
    (hb : ∀ θ, ContDiffAt ℝ ∞ A.b (c, θ))
    (hc : ∀ θ, ContDiffAt ℝ ∞ A.c (c, θ))
    (ha0 : ∀ θ, 0 < A.a (c, θ))
    (hdet : ∀ θ, 0 < A.a (c, θ) * A.c (c, θ) - A.b (c, θ) ^ 2)
    (n : ℕ) (v : ℝ) :
    let X := positiveConformalBoundaryPolynomial (n + 1) c v
      (positiveConformalSpeed A) (positiveConformalShear A)
    let F := fun p => (X false p, X true p)
    let B := coordinatePrincipalDensity A F (positiveConformalHeight A)
    ContDiff ℝ ∞ F ∧ ∀ θ,
      F (c, θ) = (v, θ) ∧ 0 < planeJacobian F (c, θ) ∧
      ContDiffAt ℝ ∞ (positiveConformalHeight A) (c, θ) ∧
      0 < positiveConformalHeight A (c, θ) ∧
      ∀ k ≤ n,
        radialBoundaryJet (fun p => B.a p - 1) c k θ = 0 ∧
          radialBoundaryJet B.b c k θ = 0 ∧
          radialBoundaryJet (fun p => B.c p - 1) c k θ = 0 := by
  let d := positiveConformalSpeed A
  let e := positiveConformalShear A
  let X := positiveConformalBoundaryPolynomial (n + 1) c v d e
  have hfields (θ : ℝ) := contDiffAt_positiveConformalFields
    (ha θ) (hb θ) (hc θ) (ha0 θ) (hdet θ)
  have hd (θ : ℝ) : ContDiffAt ℝ ∞ d (c, θ) := (hfields θ).1
  have he (θ : ℝ) : ContDiffAt ℝ ∞ e (c, θ) := (hfields θ).2.1
  have hX (side : Bool) : ContDiff ℝ ∞ (X side) :=
    contDiff_positiveConformalBoundaryPolynomial hd he (n + 1) v side
  have hfirst (θ : ℝ) := positiveConformalBoundaryPolynomial_first_jets
    hd he (show 1 ≤ n + 1 by omega) v θ
  have hθzero : (fun η => X false (c, η)) = fun _ => v :=
    funext fun η => (hfirst η).1
  have hθid : (fun η => X true (c, η)) = fun η => η :=
    funext fun η => (hfirst η).2.1
  have hangular (θ : ℝ) : angularPartial (X false) (c, θ) = 0 ∧
      angularPartial (X true) (c, θ) = 1 := by
    rw [← deriv_cylinder_angular_slice ((hX false).differentiable (by simp)) c θ,
      ← deriv_cylinder_angular_slice ((hX true).differentiable (by simp)) c θ,
      hθzero, hθid]
    simp
  refine ⟨(hX false).prodMk (hX true), ?_⟩
  intro θ
  have hDF := (((hX false).differentiable (by simp) (c, θ)).hasFDerivAt.prodMk
    ((hX true).differentiable (by simp) (c, θ)).hasFDerivAt).fderiv
  have hJ : 0 < planeJacobian (fun p => (X false p, X true p)) (c, θ) := by
    simp only [planeJacobian, hDF, ContinuousLinearMap.prod_apply]
    change 0 < radialPartial (X false) (c, θ) * angularPartial (X true) (c, θ) -
      radialPartial (X true) (c, θ) * angularPartial (X false) (c, θ)
    rw [(hfirst θ).2.2.1, (hfirst θ).2.2.2, (hangular θ).1, (hangular θ).2]
    simpa only [mul_one, mul_zero, sub_zero] using (positiveConformal_values (ha0 θ) (hdet θ)).1
  refine ⟨Prod.ext (hfirst θ).1 (hfirst θ).2.1, hJ, (hfields θ).2.2,
    (positiveConformal_values (ha0 θ) (hdet θ)).2.1, ?_⟩
  apply positiveConformalDensity_zero_jets_of_residual hX
    (ha θ) (hb θ) (hc θ) (ha0 θ) (hdet θ) hJ
  intro side j hj
  have hmatch := positiveConformalBoundaryPolynomial_equation_jets
    hd he (n + 1) v side (Nat.add_le_add_right hj 1) θ
  have hsign : ContDiffAt ℝ ∞ (fun p => if side then -d p else d p) (c, θ) := by
    cases side
    · exact hd θ
    · exact (hd θ).neg
  have hright := ((he θ).mul (contDiff_cylinder_angularPartial (hX side)).contDiffAt).add
    (hsign.mul (contDiff_cylinder_angularPartial (hX (!side))).contDiffAt)
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hleft := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
    (g := radialPartial (X side)) c
    (contDiff_cylinder_radialPartial (hX side)).contDiffAt hline
  have hright' := ContDiffAt.fun_comp (f := fun r : ℝ => (r, θ))
    (g := fun p => e p * angularPartial (X side) p +
      (if side then -d p else d p) * angularPartial (X (!side)) p) c hright hline
  change iteratedDeriv j (fun r => radialPartial (X side) (r, θ) -
    (e (r, θ) * angularPartial (X side) (r, θ) +
      (if side then -d (r, θ) else d (r, θ)) * angularPartial (X (!side)) (r, θ))) c = 0
  rw [iteratedDeriv_fun_sub
    (hleft.of_le (show (j : ℕ∞ω) ≤ ∞ by simp))
    (hright'.of_le (show (j : ℕ∞ω) ≤ ∞ by simp))]
  exact sub_eq_zero.mpr hmatch

end ContinuousFlexibility.Analysis
