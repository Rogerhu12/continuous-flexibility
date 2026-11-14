module

public import ContinuousFlexibility.Analysis.N01FlowCollarJetBounds
public import ContinuousFlexibility.Analysis.N01FlowInverseJetBounds
public import ContinuousFlexibility.Analysis.PolynomialFiberInverseJets

/-!
# Mixed jets of the actual inverse flow on the selected optical collars

The inverse is the actual `Function.invFun` of the N01 flow. Its
smoothness and right-inverse identity are derived from N01. The common
angular derivative lower bound then converts the forward mixed-jet
bounds into bounds for every positive-order mixed inverse jet.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

section ActualCollar

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
  (hangle : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
    1 / 2 ≤ deriv (C.minusFlow z m r) θ)

include hN hS hT hz hsector hinside hdisc

theorem N01Properties.minusFlow_invFun_collar_contDiffOn (m : ℕ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => Function.invFun (C.minusFlow z m p.1) p.2)
      (Ioo (x m - δ m) (x m + δ m) ×ˢ univ) := by
  intro p hp
  exact (hN.minusFlow_invFun_contDiffAt_of_discriminant hS hT hz hsector m p
    ⟨(hinside m).1.trans hp.1.1, hp.1.2.trans (hinside m).2⟩
    (hdisc m p hp.1)).contDiffWithinAt

include j hB₀ hcell hspeed hangle

theorem N01Properties.minusFlow_invFun_collar_positive_fderiv_jets
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      ‖iteratedFDeriv ℝ n
        (fun q : PolarPoint => Function.invFun (C.minusFlow z m q.1) q.2) p‖ ≤
        A * radialE (D.cellIndex (j m)) ^ P := by
  let W (m : ℕ) : ℝ := radialE (D.cellIndex (j m))
  let U (m : ℕ) : Set PolarPoint := Ioo (x m - δ m) (x m + δ m) ×ˢ univ
  let F (m : ℕ) (p : PolarPoint) : ℝ := C.minusFlow z m p.1 p.2
  let g (m : ℕ) (p : PolarPoint) : ℝ := Function.invFun (C.minusFlow z m p.1) p.2
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hU (m : ℕ) : IsOpen (U m) := isOpen_Ioo.prod isOpen_univ
  have hF (m : ℕ) : ContDiffOn ℝ ∞ (F m) (U m) :=
    hN.minusFlow_collar_contDiffOn hS hT hz hsector x δ hinside hdisc m
  have hg (m : ℕ) : ContDiffOn ℝ ∞ (g m) (U m) :=
    hN.minusFlow_invFun_collar_contDiffOn hS hT hz hsector x δ hinside hdisc m
  have hclosed (m : ℕ) (p : PolarPoint) (hp : p ∈ U m) :
      p.1 ∈ Icc (C.left m) (C.right m) :=
    ⟨((hinside m).1.trans hp.1.1).le, (hp.1.2.trans (hinside m).2).le⟩
  have hright (m : ℕ) (p : PolarPoint) (hp : p ∈ U m) : F m (p.1, g m p) = p.2 := by
    have hsurj := returnLift_surjective Real.pi_pos
      (N01Properties.minusFlow_differentiable S C z m hN hz (hclosed m p hp)).continuous
      (hN.minusFlow_add_period hz m (hclosed m p hp))
    exact Function.rightInverse_invFun hsurj p.2
  have hlo (m : ℕ) (p : PolarPoint) (hp : p ∈ U m) :
      (1 / 2 : ℝ) ≤ fderiv ℝ (F m) p (0, 1) := by
    have hd := ((hF m).contDiffAt ((hU m).mem_nhds hp)).differentiableAt (by simp)
    have heq : deriv (C.minusFlow z m p.1) p.2 = fderiv ℝ (F m) p (0, 1) :=
      (hasDerivAt_angular_slice hd).deriv
    rw [← heq]
    exact hangle m p.1 (hclosed m p hp) p.2
  have hforward (k : ℕ) (hk : 1 ≤ k) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ m p, p ∈ U m → ‖iteratedFDeriv ℝ k (F m) p‖ ≤ A * W m ^ P := by
    obtain ⟨A, P, hA, hP, hb⟩ := hN.minusFlow_collar_positive_fderiv_jets
      hS hT hz hsector j x δ hB₀ hcell hinside hspeed hdisc k hk
    exact ⟨A, P, hA, hP, fun m p hp => hb m p hp.1⟩
  obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_fiber_inverse_polynomial_bound
    W hW U hU F g hF hg (fun _ p hp => ⟨hp.1, mem_univ _⟩) hright
    (by norm_num : (0 : ℝ) < 1 / 2) hlo hforward n hn
  exact ⟨A, P, hA, hP, fun m p hp => hb m p ⟨hp, mem_univ _⟩⟩

end ActualCollar

/-- The angular denominator premise is supplied on one common smaller
N01 neighborhood. All previously selected collar witnesses are fixed. -/
theorem N01Properties.exists_uniform_collar_inverse_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B₀) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
    (hdisc : ∀ z ∈ stateNeighborhood S C base ε, ∀ m : ℕ, ∀ p : PolarPoint,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ n : ℕ, 1 ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
        p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
        ‖iteratedFDeriv ℝ n
          (fun q : PolarPoint => Function.invFun (C.minusFlow z m q.1) q.2) p‖ ≤
          A * radialE (D.cellIndex (j m)) ^ P := by
  obtain ⟨base', ε', hb, hε', hεε, hnew, hangular⟩ :=
    hN.exists_uniform_inverse_angular_jets hS hT
  refine ⟨base', ε', hb, hε', hεε, hnew, fun z hz hsector n hn => ?_⟩
  have hzold := stateNeighborhood_mono S C hb hεε hz
  exact hN.minusFlow_invFun_collar_positive_fderiv_jets hS hT hzold hsector
    j x δ hB₀ hcell hinside hspeed (hdisc z hzold)
    (fun m r hr θ => ((hangular z hz hsector).1 m r hr θ).1) n hn

end ContinuousFlexibility.Statements
