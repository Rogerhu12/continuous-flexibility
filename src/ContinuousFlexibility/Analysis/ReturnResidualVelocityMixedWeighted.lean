module

public import ContinuousFlexibility.Analysis.N01FlowInverseCollarJets
public import ContinuousFlexibility.Analysis.ReturnInterpolationMixedJets
public import ContinuousFlexibility.Analysis.ReturnResidualAngularWeightedBounds
public import ContinuousFlexibility.Analysis.PolynomialWeightedJets
public import ContinuousFlexibility.Analysis.PolynomialPositiveComposition

/-!
# Mixed weighted jets of the actual independent correction velocity

The ordinary inverse flow, cutoff interpolation inverse, and displacement
are the actual N01 objects. Their spatial compositions preserve the exact
component height factor of the independently decoded residual. All
additional losses are powers of the containing reference-cell weight.
The cutoff is an argument throughout, so this estimate applies to the
same quantitative optical collar selected for characteristic positivity.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

section ActualVelocity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B₀ : ℝ} (hB₀ : 0 < B₀)
  (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
  (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
    radialE (D.cellIndex (j m)) ^ (-B₀) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
  (hdisc : ∀ m : ℕ, ∀ p : PolarPoint, p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
  (hflow : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
    1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2)
  (hinverse : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
    |iteratedDeriv k (C.minusReturnInverse z m) θ| ≤ A)

include hN hS hT hz hsector hB₀ hcell hinside hspeed hdisc
  hχ hχrange hcutoff hflow hinverse

theorem N01Properties.returnCorrectionVelocityLinear_mixed_weighted_bound
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) p‖ ≤
        A * T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P := by
  let W (m : ℕ) : ℝ := radialE (D.cellIndex (j m))
  let H (m : ℕ) : ℝ := T.H (T.sample m) ^ (3 / 4 : ℝ)
  let U (m : ℕ) : Set PolarPoint := Ioo (x m - δ m) (x m + δ m) ×ˢ univ
  let F (m : ℕ) (p : PolarPoint) : ℝ := C.minusFlow z m p.1 p.2
  let α (m : ℕ) (p : PolarPoint) : ℝ := Function.invFun (C.minusFlow z m p.1) p.2
  let Agraph (m : ℕ) (p : PolarPoint) : PolarPoint := (p.1, α m p)
  let Binv (m : ℕ) (p : PolarPoint) : ℝ := Function.invFun
    (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) p.2
  let β (m : ℕ) (p : PolarPoint) : ℝ := Binv m (Agraph m p)
  let V (m : ℕ) (p : PolarPoint) : ℝ := fderiv ℝ (F m) p (0, 1)
  let u (m : ℕ) (p : PolarPoint) : ℝ := V m (Agraph m p)
  let c (m : ℕ) (p : PolarPoint) : ℝ := deriv (χ m) p.1
  let d (m : ℕ) (θ : ℝ) : ℝ := returnCorrectionDisplacementLinear S C z m θ ρ
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hH (m : ℕ) : 0 < H m :=
    Real.rpow_pos_of_pos ((material_circle_sample_weights_pos hT hN.1.1).2 m) _
  have hU (m : ℕ) : IsOpen (U m) := isOpen_Ioo.prod isOpen_univ
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hend (m : ℕ) (θ : ℝ) :
      1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
        deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2 :=
    hflow m (C.right m) ⟨(hC.1 m).2.1.le, le_rfl⟩ θ
  have hF (m : ℕ) : ContDiffOn ℝ ∞ (F m) (U m) :=
    hN.minusFlow_collar_contDiffOn hS hT hz hsector x δ hinside hdisc m
  have hα (m : ℕ) : ContDiffOn ℝ ∞ (α m) (U m) :=
    hN.minusFlow_invFun_collar_contDiffOn hS hT hz hsector x δ hinside hdisc m
  have hAgraph (m : ℕ) : ContDiffOn ℝ ∞ (Agraph m) (U m) :=
    contDiffOn_fst.prodMk (hα m)
  have hmap (m : ℕ) : MapsTo (Agraph m) (U m) (U m) :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hBinv (m : ℕ) : ContDiff ℝ ∞ (Binv m) :=
    hN.returnInterpolation_invFun_joint_contDiff hS hT hz hsector χ hχ hχrange m
  have hβ (m : ℕ) : ContDiffOn ℝ ∞ (β m) (U m) := by
    simpa only [Function.comp_def] using
      (hBinv m).contDiffOn.comp (hAgraph m) (fun _ _ => mem_univ _)
  have hV (m : ℕ) : ContDiffOn ℝ ∞ (V m) (U m) :=
    ((hF m).fderiv_of_isOpen (hU m) (by simp)).clm_apply contDiffOn_const
  have hu (m : ℕ) : ContDiffOn ℝ ∞ (u m) (U m) := by
    simpa only [Function.comp_def] using (hV m).comp (hAgraph m) (hmap m)
  have hdχ (m : ℕ) : ContDiff ℝ ∞ (deriv (χ m)) :=
    (contDiff_infty_iff_deriv.mp (hχ m)).2
  have hc (m : ℕ) : ContDiffOn ℝ ∞ (c m) (U m) :=
    ((hdχ m).comp contDiff_fst).contDiffOn
  have hd (m : ℕ) : ContDiff ℝ ∞ (d m) :=
    hN.returnCorrectionDisplacementLinear_contDiff hS hT hz hsector m ρ
  have hdbeta (m : ℕ) : ContDiffOn ℝ ∞ (fun p => d m (β m p)) (U m) := by
    simpa only [Function.comp_def] using
      (hd m).contDiffOn.comp (hβ m) (fun _ _ => mem_univ _)
  have hFb (k : ℕ) (hk : 1 ≤ k) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (F m) p‖ ≤ A * W m ^ P := by
    obtain ⟨A, P, hA, hP, hb⟩ := hN.minusFlow_collar_positive_fderiv_jets
      hS hT hz hsector j x δ hB₀ hcell hinside hspeed hdisc k hk
    exact ⟨A, P, hA, hP, fun m p hp => hb m p hp.1⟩
  have hαb (k : ℕ) (hk : 1 ≤ k) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (α m) p‖ ≤ A * W m ^ P := by
    obtain ⟨A, P, hA, hP, hb⟩ := hN.minusFlow_invFun_collar_positive_fderiv_jets
      hS hT hz hsector j x δ hB₀ hcell hinside hspeed hdisc
      (fun m r hr θ => (hflow m r hr θ).1) k hk
    exact ⟨A, P, hA, hP, fun m p hp => hb m p hp.1⟩
  have hAgb (k : ℕ) (hk : 1 ≤ k) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (Agraph m) p‖ ≤ A * W m ^ P :=
    norm_iteratedFDeriv_coordinate_graph_polynomial_bound W hW U hU α hα k hk (hαb k hk)
  have hBb (k : ℕ) (hk : 1 ≤ k) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ k (Binv m) p‖ ≤ A * W m ^ P :=
    hN.returnInterpolation_invFun_positive_fderiv_jets hS hT hz hsector
      χ hχ hχrange W hW hcutoff hend hinverse k hk
  have hβb (k : ℕ) (hk : 1 ≤ k) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (β m) p‖ ≤ A * W m ^ P := by
    apply norm_iteratedFDeriv_comp_positive_polynomial_bound W hW U (fun _ => univ)
      hU (fun _ => isOpen_univ) Agraph Binv hAgraph
      (fun m => (hBinv m).contDiffOn) (fun _ _ _ => mem_univ _) k hk
    · intro a ha _
      obtain ⟨A, P, hA, hP, hb⟩ := hBb a ha
      exact ⟨A, P, hA, hP, fun m p _ => hb m (Agraph m p)⟩
    · exact fun a ha _ => hAgb a ha
  have hVb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (V m) p‖ ≤ A * W m ^ P :=
    norm_iteratedFDeriv_fderiv_apply_polynomial_bound W U hU F hF (0, 1) k
      (hFb (k + 1) (by omega))
  have hub (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (u m) p‖ ≤ A * W m ^ P := by
    apply norm_iteratedFDeriv_comp_polynomial_bound W hW U U hU hU Agraph V
      hAgraph hV hmap k
    · intro a _
      obtain ⟨A, P, hA, hP, hb⟩ := hVb a
      exact ⟨A, P, hA, hP, fun m p hp => hb m (Agraph m p) (hmap m hp)⟩
    · exact fun a ha _ => hAgb a ha
  have hcb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (c m) p‖ ≤ A * W m ^ P := by
    apply norm_iteratedFDeriv_scalar_coordinate_polynomial_bound W hW U hU
      (fun m => deriv (χ m)) hdχ (ContinuousLinearMap.fst ℝ ℝ ℝ) k
    intro a _
    obtain ⟨A, P, hA, hP, hb⟩ := hcutoff (a + 1)
    refine ⟨A, P, hA, hP, fun m r => ?_⟩
    simpa only [iteratedDeriv_succ'] using hb m r
  have hdβb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (fun q => d m (β m q)) p‖ ≤ A * H m * W m ^ P := by
    apply norm_iteratedFDeriv_comp_weighted_polynomial_bound W H hW hH U (fun _ => univ)
      hU (fun _ => isOpen_univ) β d hβ (fun m => (hd m).contDiffOn)
      (fun _ _ _ => mem_univ _) k
    · intro a _
      obtain ⟨A, hA, hb⟩ := hN.returnCorrectionDisplacementLinear_angular_weighted_bound
        hS hT hz hsector hend hinverse ρ a
      refine ⟨A, 0, hA, le_rfl, fun m p _ => ?_⟩
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        Real.rpow_zero, mul_one]
      exact hb m (β m p)
    · exact fun a ha _ => hβb a ha
  have hucb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (fun q => u m q * c m q) p‖ ≤ A * W m ^ P :=
    norm_iteratedFDeriv_mul_polynomial_bound W hW U hU u c hu hc k
      (fun a _ => hub a) (fun a _ => hcb a)
  obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_mul_weighted_polynomial_bound
    W H hW hH U hU (fun m q => u m q * c m q) (fun m q => d m (β m q))
    (fun m => (hu m).mul (hc m)) hdbeta n (fun k _ => hucb k) (fun k _ => hdβb k)
  refine ⟨A, P, hA, hP, fun m p hp => ?_⟩
  have hpU : p ∈ U m := ⟨hp, mem_univ _⟩
  have heq : (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) =ᶠ[𝓝 p]
      (fun q => u m q * c m q * d m (β m q)) := by
    filter_upwards [(hU m).mem_nhds hpU] with q hq
    rw [returnCorrectionVelocityLinear_apply]
    have hder : deriv (C.minusFlow z m q.1) (α m q) = V m (Agraph m q) :=
      (hasDerivAt_angular_slice
        (((hF m).contDiffAt ((hU m).mem_nhds (hmap m hq))).differentiableAt (by simp))).deriv
    change deriv (C.minusFlow z m q.1) (α m q) * c m q * d m (β m q) =
      u m q * c m q * d m (β m q)
    rw [hder]
  rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hb m p hpU

end ActualVelocity

end ContinuousFlexibility.Statements
