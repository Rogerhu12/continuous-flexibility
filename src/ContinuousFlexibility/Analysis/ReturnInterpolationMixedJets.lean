import ContinuousFlexibility.Analysis.ReturnInitialMapJetBounds
import ContinuousFlexibility.Analysis.ReturnInterpolationJetBounds
import ContinuousFlexibility.Analysis.ReturnCorrectionVelocityRegularity
import ContinuousFlexibility.Analysis.PolynomialFiberInverseJets

/-!
# Mixed jets of the actual cutoff interpolation and its inverse

The initial displacement is uniformly bounded at every angular order.
The actual cutoff has component-power radial bounds. Their product
controls the full mixed jets of the interpolation, and the triangular
inverse recurrence controls its actual inverse with the same weights.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

section ActualInterpolation

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, χ m r ∈ Icc (0 : ℝ) 1)

include hN hS hT hz hsector hχ hχrange

theorem N01Properties.returnInterpolation_invFun_joint_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (fun p : PolarPoint =>
      Function.invFun (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) p.2) := by
  let K : ℝ → ℝ := returnCorrectionInitialMap S C z m
  let F (r : ℝ) : ℝ → ℝ := returnInterpolation (χ m r) K
  have hK : ContDiff ℝ ∞ K := hN.returnCorrectionInitialMap_contDiff hS hT hz hsector m
  have hF : ContDiff ℝ ∞ (fun p : PolarPoint => F p.1 p.2) :=
    hN.returnInterpolation_joint_contDiff hS hT hz hsector m χ (hχ m)
  have hsurj (r : ℝ) : Function.Surjective (F r) :=
    returnLift_surjective Real.pi_pos (returnInterpolation_contDiff hK (χ m r)).continuous
      (returnInterpolation_periodic_lift (hN.returnCorrectionInitialMap_add_period hz hsector m)
        (χ m r))
  have hpos (r θ : ℝ) : 0 < deriv (F r) θ := by
    rw [(returnInterpolation_hasDerivAt (χ := χ m r)
      ((hK.differentiable (by simp) θ).hasDerivAt)).deriv]
    exact returnInterpolation_deriv_pos (hχrange m r).1 (hχrange m r).2
      (hN.returnCorrectionInitialMap_deriv_pos hz hsector m θ)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  let θ := Function.invFun (F p.1) p.2
  have heq : (p.1, F p.1 θ) = p := by
    apply Prod.ext
    · rfl
    · exact Function.rightInverse_invFun (hsurj p.1) p.2
  have h := returnFlow_invFun_contDiffAt (F := F)
    (hF.contDiffAt (x := (p.1, θ))) (by simp) (hpos p.1 θ).ne'
    (Eventually.of_forall fun r => (strictMono_of_deriv_pos (hpos r)).injective)
  rw [heq] at h
  exact h

variable (W : ℕ → ℝ) (hW : ∀ m, 1 ≤ W m)
  (hcutoff : ∀ n : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv n (χ m) r| ≤ A * W m ^ P)
  (hflow : ∀ m θ, 1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
    deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2)
  (hinverse : ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
    |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ A)

include W hW hcutoff hflow hinverse

theorem N01Properties.returnInterpolation_positive_fderiv_jets (n : ℕ) (hn : 1 ≤ n) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ n (fun q : PolarPoint =>
        returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m) q.2) p‖ ≤
        A * W m ^ P := by
  let U (_ : ℕ) : Set PolarPoint := univ
  let d (m : ℕ) (θ : ℝ) : ℝ := returnCorrectionInitialMap S C z m θ - θ
  let a (m : ℕ) (p : PolarPoint) : ℝ := χ m p.1
  let b (m : ℕ) (p : PolarPoint) : ℝ := d m p.2
  have hd (m : ℕ) : ContDiff ℝ ∞ (d m) :=
    (hN.returnCorrectionInitialMap_contDiff hS hT hz hsector m).sub contDiff_id
  have hdb (k : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ, |iteratedDeriv k (d m) θ| ≤ A :=
    hN.returnCorrectionInitialMap_sub_id_angular_jets_uniform hS hT hz hsector
      (hN.returnCorrectionInitialMap_positive_jets_uniform hS hT hz hsector hflow hinverse) k
  have ha (m : ℕ) : ContDiffOn ℝ ∞ (a m) (U m) := ((hχ m).comp contDiff_fst).contDiffOn
  have hb (m : ℕ) : ContDiffOn ℝ ∞ (b m) (U m) := ((hd m).comp contDiff_snd).contDiffOn
  have hab (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (a m) p‖ ≤ A * W m ^ P :=
    norm_iteratedFDeriv_scalar_coordinate_polynomial_bound W hW U (fun _ => isOpen_univ)
      χ hχ (ContinuousLinearMap.fst ℝ ℝ ℝ) k (fun j _ => hcutoff j)
  have hbb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ k (b m) p‖ ≤ A * W m ^ P := by
    apply norm_iteratedFDeriv_scalar_coordinate_polynomial_bound W hW U (fun _ => isOpen_univ)
      d hd (ContinuousLinearMap.snd ℝ ℝ ℝ) k
    intro j _
    obtain ⟨A, hA, hbound⟩ := hdb j
    exact ⟨A, 0, hA, le_rfl, fun m θ => by
      simpa only [Real.rpow_zero, mul_one] using hbound m θ⟩
  have hprod := norm_iteratedFDeriv_mul_polynomial_bound W hW U (fun _ => isOpen_univ)
    a b ha hb n (fun k _ => hab k) (fun k _ => hbb k)
  have hid : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ U m →
      ‖iteratedFDeriv ℝ n (fun q : PolarPoint => q.2) p‖ ≤ A * W m ^ P := by
    refine ⟨‖ContinuousLinearMap.snd ℝ ℝ ℝ‖, 0, norm_nonneg _, le_rfl, fun m p _ => ?_⟩
    simpa only [Real.rpow_zero, mul_one] using
      norm_iteratedFDeriv_linear_of_pos (ContinuousLinearMap.snd ℝ ℝ ℝ) n hn p
  obtain ⟨A, P, hA, hP, hbound⟩ := norm_iteratedFDeriv_add_polynomial_bound
    W hW U (fun _ => isOpen_univ) (fun _ p => p.2) (fun m p => a m p * b m p)
    (fun _ => contDiffOn_snd) (fun m => (ha m).mul (hb m)) n hid hprod
  refine ⟨A, P, hA, hP, fun m p => ?_⟩
  have heq : (fun q : PolarPoint =>
      returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m) q.2) =
      fun q => q.2 + a m q * b m q := by
    funext q
    exact returnInterpolation_apply _ _ _
  rw [heq]
  exact hbound m p (mem_univ _)

theorem N01Properties.returnInterpolation_invFun_positive_fderiv_jets
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ n (fun q : PolarPoint => Function.invFun
        (returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m)) q.2) p‖ ≤
        A * W m ^ P := by
  let U (_ : ℕ) : Set PolarPoint := univ
  let F (m : ℕ) (p : PolarPoint) : ℝ :=
    returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m) p.2
  let g (m : ℕ) (p : PolarPoint) : ℝ :=
    Function.invFun (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) p.2
  have hF (m : ℕ) : ContDiff ℝ ∞ (F m) :=
    hN.returnInterpolation_joint_contDiff hS hT hz hsector m χ (hχ m)
  have hg (m : ℕ) : ContDiff ℝ ∞ (g m) :=
    hN.returnInterpolation_invFun_joint_contDiff hS hT hz hsector χ hχ hχrange m
  have hK (m : ℕ) := hN.returnCorrectionInitialMap_contDiff hS hT hz hsector m
  have hright (m : ℕ) (p : PolarPoint) (_hp : p ∈ U m) : F m (p.1, g m p) = p.2 := by
    have hsurj := returnLift_surjective Real.pi_pos
      (returnInterpolation_contDiff (hK m) (χ m p.1)).continuous
      (returnInterpolation_periodic_lift (hN.returnCorrectionInitialMap_add_period hz hsector m)
        (χ m p.1))
    exact Function.rightInverse_invFun hsurj p.2
  have hlo (m : ℕ) (p : PolarPoint) (_hp : p ∈ U m) :
      (1 / 12 : ℝ) ≤ fderiv ℝ (F m) p (0, 1) := by
    have heq : deriv (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) p.2 =
        fderiv ℝ (F m) p (0, 1) :=
      (hasDerivAt_angular_slice ((hF m).differentiable (by simp) p)).deriv
    rw [← heq]
    exact (returnInterpolation_deriv_bounds (hK m)
      (hN.returnCorrectionInitialMap_deriv_bounds hz hsector hflow m) (hχrange m p.1) p.2).1
  have hforward (k : ℕ) (hk : 1 ≤ k) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (F m) p‖ ≤ A * W m ^ P := by
    obtain ⟨A, P, hA, hP, hb⟩ := hN.returnInterpolation_positive_fderiv_jets
      hS hT hz hsector χ hχ hχrange W hW hcutoff hflow hinverse k hk
    exact ⟨A, P, hA, hP, fun m p _ => hb m p⟩
  obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_fiber_inverse_polynomial_bound
    W hW U (fun _ => isOpen_univ) F g (fun m => (hF m).contDiffOn)
    (fun m => (hg m).contDiffOn) (fun _ _ _ => mem_univ _) hright
    (by norm_num : (0 : ℝ) < 1 / 12) hlo hforward n hn
  exact ⟨A, P, hA, hP, fun m p => hb m p (mem_univ _)⟩

end ActualInterpolation

end ContinuousFlexibility.Statements
