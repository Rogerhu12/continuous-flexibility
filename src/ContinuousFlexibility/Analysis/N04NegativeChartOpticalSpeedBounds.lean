import ContinuousFlexibility.Analysis.N04NegativeChartOpticalSquareBounds
import ContinuousFlexibility.Analysis.N04NegativeChartAffineSqrtBounds

/-!
# Actual divided optical-speed jets through the closed half

The affine square is the actual state optical factor, with a common
positive lower bound. The existing genuine affine square-root tower
therefore gives every radial/state jet. Every positive state order
retains one full height factor; all direction seminorms have order zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

private abbrev rootSpeedStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] rootSpeedStateTopology
private abbrev rootSpeedStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] rootSpeedStateGroup
private abbrev rootSpeedStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] rootSpeedStateModule
private abbrev rootSpeedStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (rootSpeedStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] rootSpeedStateSMul

private theorem negativeDirection_radial_bound (j : ℕ) (f : ℝ → ℝ)
    {a b t C H E p q : ℝ} (hab : a = b)
    (hb : |b * iteratedDeriv j f t| ≤ C * H * E * p)
    (hcost : 0 ≤ C * H * E) (hpq : p ≤ q) :
    |iteratedDeriv j (fun s => a * (-f s)) t| ≤ C * E * H * q := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_neg, hab, mul_neg, abs_neg]
  exact hb.trans ((mul_le_mul_of_nonneg_left hpq hcost).trans_eq (by ring))

private theorem affineSqrt_bounds_from_inverse
    {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : Seminorm ℝ X) {U : Set X} (hU : IsOpen U)
    (I : ι → Set ℝ) (q₀ g : ι → ℝ → ℝ) (L : ι → X →L[ℝ] ℝ)
    (Q f : ι → X → ℝ → ℝ)
    (hq : ∀ m, ContDiff ℝ ∞ (q₀ m)) (hg : ∀ m, ContDiff ℝ ∞ (g m))
    (hQ : ∀ m x, (fun t => q₀ m t + L m x * g m t) = Q m x)
    (hf : ∀ m x, (fun t => Real.sqrt (q₀ m t + L m x * g m t)) = f m x)
    (E H : ι → ℝ) (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (hbounded : ∃ R : ℝ, 0 < R ∧ ∀ m, H m ≤ R)
    (hpos : ∀ m t, t ∈ I m → ∀ x ∈ U, 0 < Q m x t)
    (hinv : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m t, t ∈ I m →
      ∀ x ∈ U, (Q m x t)⁻¹ ≤ B * E m ^ A)
    (hjetq : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m t, t ∈ I m → ∀ x ∈ U, |iteratedDeriv j (Q m x) t| ≤ C * E m ^ A)
    (hjetg : ∀ j : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m t, t ∈ I m → ∀ v : X,
        |iteratedDeriv j (fun s => L m v * g m s) t| ≤ C * E m ^ A * H m * p v)
    (n k : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m t, t ∈ I m →
      ∀ J : SmoothDirections U (fun x => iteratedDeriv n (f m x) t),
      ∀ x ∈ U, ∀ v : Fin k → X,
        |J.D k x v| ≤ B * E m ^ A * parameterHeightWeight (H m) k * ∏ i, p (v i) := by
  obtain ⟨R, hR, hHR⟩ := hbounded
  obtain ⟨Bi, Ai, hBi, hAi, hinverse⟩ := hinv
  have hlower (m) (t) (ht : t ∈ I m) (x) (hx : x ∈ U) :
      Bi⁻¹ * E m ^ (-Ai) ≤ q₀ m t + L m x * g m t := by
    have hi := inv_anti₀ (inv_pos.mpr (hpos m t ht x hx)) (hinverse m t ht x hx)
    have hi' : (Bi * E m ^ Ai)⁻¹ ≤ Q m x t := by simpa only [inv_inv] using hi
    calc
      _ = (Bi * E m ^ Ai)⁻¹ := by
        rw [mul_inv_rev, Real.rpow_neg (zero_le_one.trans (hE m))]
        ring
      _ ≤ Q m x t := hi'
      _ = _ := (congrFun (hQ m x) t).symm
  have hqjet (j : ℕ) : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m t, t ∈ I m → ∀ x ∈ U,
        |iteratedDeriv j (fun s => q₀ m s + L m x * g m s) t| ≤ C * E m ^ A := by
    obtain ⟨C, A, hC, hA, hb⟩ := hjetq j
    refine ⟨C, A, hC, hA, fun m t ht x hx => ?_⟩
    rw [hQ m x]
    exact hb m t ht x hx
  obtain ⟨B, A, hB, hA, hb⟩ := n04NegativeChart_affineSqrtJet_material_bounds
    p hU I q₀ g L hq hg E H hE hH hR hHR (inv_pos.mpr hBi) hAi hlower hqjet hjetg n k
  refine ⟨B, A, hB, hA, fun m t ht J x hx v => ?_⟩
  exact hb m t ht (J.congr (fun y _ =>
    (congrArg (fun f : ℝ → ℝ => iteratedDeriv n f t) (hf m y)).symm)) x hx v

namespace N04RealizationStart.NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

def opticalSpeed (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) (t : ℝ) : ℝ :=
  Real.sqrt (F.stateSquare z m side t)

private theorem square_affine (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) :
    (fun t => F.reference m side t +
      stateJointKappaCLM W.hS W.hT W.radial.1 m z * (-F.control m side t)) =
        F.stateSquare z m side := by
  funext t
  rw [stateJointKappaCLM_apply]
  dsimp only [stateSquare]
  ring

private theorem speed_affine (z : AnnularState W.S × ℝ) (m : ℕ) (side : Bool) :
    (fun t => Real.sqrt (F.reference m side t +
      stateJointKappaCLM W.hS W.hT W.radial.1 m z * (-F.control m side t))) =
        F.opticalSpeed z m side := by
  funext t
  exact congrArg Real.sqrt (congrFun (F.square_affine z m side) t)

/-- Genuine state towers exist even at the physical root and at the
actual optical cut. Smooth scalar input germs are taken on the full line. -/
def opticalSpeed_radialJetTower (m : ℕ) (side : Bool) (n : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
    SmoothDirections (stateNeighborhood W.S W.C W.base (W.ε / 2))
      (fun z => iteratedDeriv n (F.opticalSpeed z m side) t) := by
  let J := affineOpticalRadialJetSmoothDirections
    (stateJointKappaCLM W.hS W.hT W.radial.1 m) isOpen_univ
    (F.reference_smooth m side).contDiffOn (F.control_smooth m side).neg.contDiffOn
    n t (mem_univ t) (isOpen_stateNeighborhood W.S W.C W.base (W.ε / 2))
    (fun z hz => by
      rw [congrFun (F.square_affine z m side) t]
      exact F.stateSquare_pos hz m side ht)
  exact J.congr (fun z _ => congrArg (fun f : ℝ → ℝ => iteratedDeriv n f t)
    (F.speed_affine z m side))

private theorem opticalDirection_joint_material_bounds (j : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ i : ℕ × Bool, ∀ t,
      t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) → ∀ v : AnnularState W.S × ℝ,
        |iteratedDeriv j (fun s => stateJointKappaCLM W.hS W.hT W.radial.1 i.1 v *
          (-F.control i.1 i.2 s)) t| ≤
          C * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^ A *
            (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^ (3 / 4 : ℝ)) *
              pairGrading (stateGrading W.S) realGrading 0 v := by
  refine (F.control_direction_material_jets j).elim ?_
  intro C hCA
  refine hCA.elim ?_
  intro A hAdata
  have hC := hAdata.1
  have hA := hAdata.2.1
  have hb := hAdata.2.2
  refine ⟨C, A, hC, hA, fun i t ht v => ?_⟩
  have hH : 0 ≤ W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hcost : 0 ≤ C * (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^
      (3 / 4 : ℝ)) * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^ A :=
    mul_nonneg (mul_nonneg hC.le hH) (Real.rpow_nonneg (zero_le_one.trans (W.floor _)) _)
  exact negativeDirection_radial_bound j (F.control i.1 i.2)
    (stateJointKappaCLM_apply W.hS W.hT W.radial.1 i.1 v)
    (hb i.1 i.2 t ht v.1) hcost (stateGrading_fst_le_jointStateGrading W.S 0 v)

/-- The mixed bound is for every genuine parameter tower of the actual
radial derivative. Constants precede the component, state and point. -/
theorem opticalSpeed_mixed_material_bounds (n k : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m side t,
      t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      ∀ J : SmoothDirections (stateNeighborhood W.S W.C W.base (W.ε / 2))
        (fun z => iteratedDeriv n (F.opticalSpeed z m side) t),
      ∀ z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2),
      ∀ v : Fin k → AnnularState W.S × ℝ,
        |J.D k z v| ≤
          B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ A *
            parameterHeightWeight
              (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ)) k *
              ∏ i, pairGrading (stateGrading W.S) realGrading 0 (v i) := by
  let I : ℕ × Bool → Set ℝ := fun i => Icc 0 (W.negativeOpticalWidth i.1 i.2)
  let E : ℕ × Bool → ℝ := fun i =>
    W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl i))))
  let H : ℕ × Bool → ℝ := fun i =>
    W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^ (3 / 4 : ℝ)
  have hE (i : ℕ × Bool) : 1 ≤ E i := W.floor _
  have hH (i : ℕ × Bool) : 0 ≤ H i := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  obtain ⟨R, hR, hHeight⟩ := materialHeight_E0_weight_bounded W.hT
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hHR (i : ℕ × Bool) : H i ≤ R := by
    simpa only [Real.rpow_zero, mul_one] using
      hHeight (W.T.sample ((W.A e).cell (e.symm (.inl i))))
        (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)
  refine (affineSqrt_bounds_from_inverse
    (pairGrading (stateGrading W.S) realGrading 0)
    (isOpen_stateNeighborhood W.S W.C W.base (W.ε / 2)) I
    (fun i => F.reference i.1 i.2) (fun i t => -F.control i.1 i.2 t)
    (fun i => stateJointKappaCLM W.hS W.hT W.radial.1 i.1)
    (fun i z => F.stateSquare z i.1 i.2) (fun i z => F.opticalSpeed z i.1 i.2)
    (fun i => F.reference_smooth i.1 i.2) (fun i => (F.control_smooth i.1 i.2).neg)
    (fun i z => F.square_affine z i.1 i.2) (fun i z => F.speed_affine z i.1 i.2)
    E H hE hH ⟨R, hR, hHR⟩ (fun i t ht z hz => F.stateSquare_pos hz i.1 i.2 ht)
    (by
      refine F.stateSquare_inverse_material.elim ?_
      intro B hBA
      refine hBA.elim ?_
      intro A h
      exact ⟨B, A, h.1, h.2.1, fun i t ht z hz => h.2.2 z hz i.1 i.2 t ht⟩)
    (fun j => by
      refine (F.stateSquare_material_jets j).elim ?_
      intro B hBA
      refine hBA.elim ?_
      intro A h
      exact ⟨B, A, h.1, h.2.1, fun i t ht z hz => h.2.2 z hz i.1 i.2 t ht⟩)
    (F.opticalDirection_joint_material_bounds) n k).elim ?_
  intro B hBA
  refine hBA.elim ?_
  intro A h
  exact ⟨B, A, h.1, h.2.1, fun m side => h.2.2 (m, side)⟩

end N04RealizationStart.NegativeOpticalFactors
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_mixed_material_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_mixed_material_bounds
