import ContinuousFlexibility.Analysis.N01ReferenceFlowJetBounds
import ContinuousFlexibility.Analysis.N01FlowJointSmoothness
import ContinuousFlexibility.Analysis.ActualRadialCellComparison

/-!
# Mixed and Fréchet jets of the actual flow on optical collars

The original N01 spatial tower already estimates the difference from
the reference flow. The quantitative collar removes its endpoint
weights, and material height absorption removes its sample factors.
Adding the actual reference-flow jets gives fixed component-power
bounds for every positive-order jet of the actual flow.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01FlowCollarJetBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem N01Properties.minusFlow_reference_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ ∞ (fun q : PolarPoint => C.minusFlow (C.referenceState, 0) m q.1 q.2) p := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hmem : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · have hzero : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
        (congrArg (fun v : AnnularState S => stateGrading S base v)
          (sub_self C.referenceState)).trans (stateGrading S base).map_zero'
      exact hzero.trans_lt hN.2.1
    · simpa only [abs_zero] using hN.2.1
  have hsector : stateSector S C.referenceState := by
    obtain ⟨_, _, _, hκ, hh, _⟩ := hN.2.2.1
    constructor
    · intro m θ φ
      simp only [hκ, map_zero, Pi.zero_apply]
    · intro m θ
      simp only [hh, map_zero, Pi.zero_apply, neg_zero]
  have hcore : p.1 ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hp.1, hp.2.trans (hC.1 m).2.2⟩
  have hw : 0 < D.w p.1 := hg.2.2.2.2.1 _ hcore
  have hr : 0 < p.1 := hg.1.trans hcore.1
  have hc : deriv D.w p.1 / p.1 < 0 := div_neg_of_neg_of_pos (hC.2.2.2.1 m _ hp) hr
  apply hN.minusFlow_contDiffAt_of_discriminant hS hT hmem hsector m p hp
  obtain ⟨ha, hb, hcc⟩ := hN.reference_coefficients
    (p.1, C.minusFlow (C.referenceState, 0) m p.1 p.2)
  rw [ha, hb, hcc, zero_pow (by decide : 2 ≠ 0), zero_sub]
  exact neg_pos.mpr (mul_neg_of_pos_of_neg hw hc)

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

include hN hS hT hz hsector hinside hdisc

theorem N01Properties.minusFlow_collar_contDiffOn (m : ℕ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (Ioo (x m - δ m) (x m + δ m) ×ˢ univ) := by
  intro p hp
  have hcomp : p.1 ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans hp.1.1, hp.1.2.trans (hinside m).2⟩
  exact (hN.minusFlow_contDiffAt_of_discriminant hS hT hz hsector m p hcomp
    (hdisc m (p.1, C.minusFlow z m p.1 p.2) hp.1)).contDiffWithinAt

include j hB₀ hcell hspeed

theorem N01Properties.minusFlow_collar_mixed_jets (a b : ℕ) (hab : 1 ≤ a + b) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      |mixedDerivative a b (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p| ≤
        A * radialE (D.cellIndex (j m)) ^ P := by
  obtain ⟨K, R, B, hK, hR, hB, hraw⟩ :=
    hN.ordinaryFlowFamily_collar_bound j x δ hB₀ hcell hinside hspeed (a + b)
  obtain ⟨V, hV, hweight⟩ := materialSample_H_E0_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) B
  let Q : ℝ := 1 + pairGrading (stateGrading S) realGrading (a + b + hN.ordinaryFlowLoss 0)
    (z - (C.referenceState, 0))
  have hQ : 0 ≤ Q := add_nonneg zero_le_one (apply_nonneg _ _)
  let M : ℝ := B * V * Q
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hB.le hV.le) hQ
  obtain ⟨A₀, P₀, hA₀, hP₀, href⟩ :=
    hN.reference_minusFlow_collar_mixed_jets hS hT j x δ hB₀ hcell hinside hspeed a b hab
  have hRP : 0 ≤ R * a := mul_nonneg hR.le (Nat.cast_nonneg _)
  have hKM : 0 ≤ K ^ a * M := mul_nonneg (pow_nonneg hK.le _) hM
  refine ⟨K ^ a * M + A₀, R * a + P₀, add_nonneg hKM hA₀,
    add_nonneg hRP hP₀, fun m p hp => ?_⟩
  let E : ℝ := radialE (D.cellIndex (j m))
  have hE : 1 ≤ E := one_le_radialE_of_nat _
  have hE₀ : 0 < E := zero_lt_one.trans_le hE
  have hinner : B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B * Q ≤ M := by
    have h := mul_le_mul_of_nonneg_left (hweight (C.cell m)) (mul_nonneg hB.le hQ)
    convert h using 1 <;> ring
  have hdiff : |ordinaryFlowFamily S C m a b p z| ≤ (K ^ a * M) * E ^ (R * a) := by
    have h := (hraw z hz m a b p le_rfl ⟨hp.1.le, hp.2.le⟩).trans
      (mul_le_mul_of_nonneg_left hinner
        (mul_nonneg (pow_nonneg hK.le _) (Real.rpow_nonneg hE₀.le _)))
    exact h.trans_eq (by ring)
  let U : Set PolarPoint := Ioo (x m - δ m) (x m + δ m) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hF : ContDiffOn ℝ ∞ (fun q : PolarPoint => C.minusFlow z m q.1 q.2) U :=
    hN.minusFlow_collar_contDiffOn hS hT hz hsector x δ hinside hdisc m
  have hF₀ : ContDiffOn ℝ ∞
      (fun q : PolarPoint => C.minusFlow (C.referenceState, 0) m q.1 q.2) U := by
    intro q hq
    exact (hN.minusFlow_reference_contDiffAt hS hT m q
      ⟨(hinside m).1.trans hq.1.1, hq.1.2.trans (hinside m).2⟩).contDiffWithinAt
  have hsub := mixedDerivative_sub_of_contDiffOn hU hF hF₀ a b
    (show p ∈ U from ⟨hp, mem_univ _⟩)
  change ordinaryFlowFamily S C m a b p z =
    mixedDerivative a b (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p -
      mixedDerivative a b (fun q : PolarPoint => C.minusFlow (C.referenceState, 0) m q.1 q.2) p at hsub
  have hfirst := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hE (by linarith : R * a ≤ R * a + P₀)) hKM
  have hsecond := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hE (by linarith : P₀ ≤ R * a + P₀)) hA₀
  calc
    _ = |ordinaryFlowFamily S C m a b p z +
      mixedDerivative a b (fun q : PolarPoint => C.minusFlow (C.referenceState, 0) m q.1 q.2) p| := by
        rw [hsub, sub_add_cancel]
    _ ≤ |ordinaryFlowFamily S C m a b p z| +
      |mixedDerivative a b (fun q : PolarPoint => C.minusFlow (C.referenceState, 0) m q.1 q.2) p| :=
        abs_add_le _ _
    _ ≤ (K ^ a * M) * E ^ (R * a) + A₀ * E ^ P₀ := add_le_add hdiff (href m p hp)
    _ ≤ (K ^ a * M) * E ^ (R * a + P₀) + A₀ * E ^ (R * a + P₀) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

theorem N01Properties.minusFlow_collar_positive_fderiv_jets (n : ℕ) (hn : 1 ≤ n) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      ‖iteratedFDeriv ℝ n (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p‖ ≤
        A * radialE (D.cellIndex (j m)) ^ P := by
  let W (m : ℕ) : ℝ := radialE (D.cellIndex (j m))
  let U (m : ℕ) : Set PolarPoint := Ioo (x m - δ m) (x m + δ m) ×ˢ univ
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hb (k : ℕ) (hk : k ≤ n) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p ∈ U m → |mixedDerivative k (n - k)
        (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p| ≤ A * W m ^ P := by
    obtain ⟨A, P, hA, hP, hbound⟩ := hN.minusFlow_collar_mixed_jets
      hS hT hz hsector j x δ hB₀ hcell hinside hspeed hdisc k (n - k) (by omega)
    exact ⟨A, P, hA, hP, fun m p hp => hbound m p hp.1⟩
  obtain ⟨A, P, hA, hP, hbound⟩ := finite_polynomial_majorant W hW U
    (fun k m p => |mixedDerivative k (n - k)
      (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p|) n hb
  refine ⟨(2 : ℝ) ^ n * A, P, mul_nonneg (pow_nonneg (by norm_num) _) hA,
    hP, fun m p hp => ?_⟩
  have h := norm_iteratedFDeriv_le_of_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
    (hN.minusFlow_collar_contDiffOn hS hT hz hsector x δ hinside hdisc m) n
    (show p ∈ U m from ⟨hp, mem_univ _⟩)
    (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans (hW m)) _))
    (fun a b hab => by
      have ha : a ≤ n := by omega
      have hbn : b = n - a := by omega
      rw [hbn, Real.norm_eq_abs]
      exact hbound a ha m p ⟨hp, mem_univ _⟩)
  exact h.trans_eq (mul_assoc _ _ _).symm

end ActualCollar

end ContinuousFlexibility.Statements
