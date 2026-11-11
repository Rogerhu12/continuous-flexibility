import ContinuousFlexibility.Analysis.N01FlowJointRegularity
import ContinuousFlexibility.Analysis.ReturnCorrectionResidualPeriodicity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Joint regularity of the actual inverse flow

The two-dimensional coordinate map is `(r, α) ↦ (r, Φ(r, α))`.
Its derivative is triangular, with nonzero angular diagonal. The inverse
function theorem applies to the actual candidate
`(r, θ) ↦ (r, invFun (Φ r) θ)` because it is a local left inverse.
No continuity premise on that inverse is needed.

The final theorem specializes this construction to the N01 ordinary flow.
The higher-regularity scalar lemma is also available for the cutoff
interpolation once its actual smooth formula is inserted.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The triangular coordinate derivative, with its explicit inverse. -/
def returnTriangularEquiv (a b : ℝ) (hb : b ≠ 0) : PolarPoint ≃L[ℝ] PolarPoint where
  toFun p := (p.1, a * p.1 + b * p.2)
  invFun q := (q.1, (q.2 - a * q.1) / b)
  map_add' p q := by
    apply Prod.ext
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · change a * (c * p.1) + b * (c * p.2) = c * (a * p.1 + b * p.2)
      ring
  left_inv p := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb] <;> ring
  right_inv q := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb] <;> ring
  continuous_toFun :=
    continuous_fst.prodMk ((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd))
  continuous_invFun :=
    continuous_fst.prodMk ((continuous_snd.sub (continuous_const.mul continuous_fst)).div_const b)

theorem returnTriangularEquiv_apply (a b : ℝ) (hb : b ≠ 0) (p : PolarPoint) :
    returnTriangularEquiv a b hb p = (p.1, a * p.1 + b * p.2) := rfl

theorem returnTriangularEquiv_graph_derivative (A : PolarPoint →L[ℝ] ℝ)
    (hb : A (0, 1) ≠ 0) :
    (returnTriangularEquiv (A (1, 0)) (A (0, 1)) hb : PolarPoint →L[ℝ] PolarPoint) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod A := by
  apply ContinuousLinearMap.ext
  intro p
  simp only [ContinuousLinearEquiv.coe_coe, returnTriangularEquiv_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
  apply Prod.ext
  · rfl
  · have h := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L p)
      (returnFlow_linearMap_coordinates A)
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul] using h.symm

theorem returnFlow_invFun_hasStrictFDerivAt
    {F : ℝ → ℝ → ℝ} {p : PolarPoint} {A : PolarPoint →L[ℝ] ℝ}
    (hF : HasStrictFDerivAt (fun q : PolarPoint => F q.1 q.2) A p)
    (hb : A (0, 1) ≠ 0)
    (hinj : ∀ᶠ r in 𝓝 p.1, Function.Injective (F r)) :
    HasStrictFDerivAt (fun q : PolarPoint => Function.invFun (F q.1) q.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((returnTriangularEquiv (A (1, 0)) (A (0, 1)) hb).symm : PolarPoint →L[ℝ] PolarPoint))
      (p.1, F p.1 p.2) := by
  let e := returnTriangularEquiv (A (1, 0)) (A (0, 1)) hb
  have hg : HasStrictFDerivAt (fun q : PolarPoint => (q.1, F q.1 q.2))
      (e : PolarPoint →L[ℝ] PolarPoint) p := by
    rw [show (e : PolarPoint →L[ℝ] PolarPoint) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod A from returnTriangularEquiv_graph_derivative A hb]
    exact hasStrictFDerivAt_fst.prodMk hF
  have hleft : ∀ᶠ q : PolarPoint in 𝓝 p,
      (fun y : PolarPoint => (y.1, Function.invFun (F y.1) y.2)) (q.1, F q.1 q.2) = q := by
    filter_upwards [continuous_fst.continuousAt.eventually hinj] with q hq
    apply Prod.ext
    · rfl
    · exact Function.leftInverse_invFun hq q.2
  exact (hg.to_local_left_inverse
    (g := fun q : PolarPoint => (q.1, Function.invFun (F q.1) q.2)) hleft).snd

/-- Higher regularity of the actual fiberwise inverse follows from the
forward coordinate map; inverse regularity is never an extra premise. -/
theorem returnFlow_invFun_contDiffAt
    {F : ℝ → ℝ → ℝ} {p : PolarPoint} {n : ℕ∞ω}
    (hF : ContDiffAt ℝ n (fun q : PolarPoint => F q.1 q.2) p) (hn : n ≠ 0)
    (hb : deriv (F p.1) p.2 ≠ 0)
    (hinj : ∀ᶠ r in 𝓝 p.1, Function.Injective (F r)) :
    ContDiffAt ℝ n (fun q : PolarPoint => Function.invFun (F q.1) q.2)
      (p.1, F p.1 p.2) := by
  let A := fderiv ℝ (fun q : PolarPoint => F q.1 q.2) p
  have hd := hF.differentiableAt hn
  have ht : deriv (F p.1) p.2 = A (0, 1) :=
    (hasDerivAt_angular_slice hd).deriv
  have hbA : A (0, 1) ≠ 0 := by rw [← ht]; exact hb
  let e := returnTriangularEquiv (A (1, 0)) (A (0, 1)) hbA
  have hpair : ContDiffAt ℝ n (fun q : PolarPoint => (q.1, F q.1 q.2)) p :=
    contDiffAt_fst.prodMk hF
  have hpairD : HasFDerivAt (fun q : PolarPoint => (q.1, F q.1 q.2))
      (e : PolarPoint →L[ℝ] PolarPoint) p := by
    rw [show (e : PolarPoint →L[ℝ] PolarPoint) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod A from returnTriangularEquiv_graph_derivative A hbA]
    exact hasFDerivAt_fst.prodMk hd.hasFDerivAt
  have hleft : ∀ᶠ q : PolarPoint in 𝓝 p,
      (fun y : PolarPoint => (y.1, Function.invFun (F y.1) y.2)) (q.1, F q.1 q.2) = q := by
    filter_upwards [continuous_fst.continuousAt.eventually hinj] with q hq
    apply Prod.ext
    · rfl
    · exact Function.leftInverse_invFun hq q.2
  have hs := hpair.hasStrictFDerivAt' hpairD hn
  have heq := hs.localInverse_unique
    (g := fun q : PolarPoint => (q.1, Function.invFun (F q.1) q.2)) hleft
  apply (hpair.to_localInverse hpairD hn).snd.congr_of_eventuallyEq
  exact heq.mono fun q hq => congrArg Prod.snd hq

theorem N01Properties.minusFlow_invFun_differentiableAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    DifferentiableAt ℝ (fun q : PolarPoint => Function.invFun (C.minusFlow z m q.1) q.2) p := by
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hclosed : p.1 ∈ Icc (C.left m) (C.right m) := ⟨hp.1.le, hp.2.le⟩
  have hsurj := returnLift_surjective Real.pi_pos
    (N01Properties.minusFlow_differentiable S C z m hN01 hz hclosed).continuous
    (hN01.minusFlow_add_period hz m hclosed)
  let α := Function.invFun (C.minusFlow z m p.1) p.2
  have hpoint : (p.1, C.minusFlow z m p.1 α) = p := by
    apply Prod.ext
    · rfl
    · exact Function.rightInverse_invFun hsurj p.2
  have hF := hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m (p.1, α) hp
  have hb :
      ((ContinuousLinearMap.toSpanSingleton ℝ
          (minusCharacteristicSpeed (originalCoefficients D S C z) (p.1, C.minusFlow z m p.1 α))).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (C.minusFlow z m p.1) α))) (0, 1) ≠ 0 := by
    simpa only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, zero_mul, one_mul, zero_add] using
        ((hflow z hz m α).2.2.2 p.1 hclosed).1.ne'
  have hinj : ∀ᶠ r in 𝓝 p.1, Function.Injective (C.minusFlow z m r) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with r hr
    exact (strictMono_of_deriv_pos fun θ =>
      ((hflow z hz m θ).2.2.2 r ⟨hr.1.le, hr.2.le⟩).1).injective
  have h := (returnFlow_invFun_hasStrictFDerivAt hF hb hinj).hasFDerivAt.differentiableAt
  rw [hpoint] at h
  exact h

end ContinuousFlexibility.Statements
