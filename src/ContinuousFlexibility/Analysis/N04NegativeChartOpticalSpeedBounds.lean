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

namespace ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

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
  obtain ⟨Bi, Ai, hBi, hAi, hinverse⟩ := F.stateSquare_inverse_material
  have hlower (i : ℕ × Bool) (t : ℝ) (ht : t ∈ I i)
      (z : AnnularState W.S × ℝ)
      (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2)) :
      Bi⁻¹ * E i ^ (-Ai) ≤ F.reference i.1 i.2 t +
        stateJointKappaCLM W.hS W.hT W.radial.1 i.1 z * (-F.control i.1 i.2 t) := by
    have hp := F.stateSquare_pos hz i.1 i.2 ht
    have hi := inv_anti₀ (inv_pos.mpr hp) (hinverse z hz i.1 i.2 t ht)
    have hi' : (Bi * E i ^ Ai)⁻¹ ≤ F.stateSquare z i.1 i.2 t := by
      simpa only [inv_inv] using hi
    calc
      _ = (Bi * E i ^ Ai)⁻¹ := by
        rw [mul_inv_rev, Real.rpow_neg (zero_le_one.trans (hE i))]
        ring
      _ ≤ F.stateSquare z i.1 i.2 t := hi'
      _ = _ := (congrFun (F.square_affine z i.1 i.2) t).symm
  have hqjet (j : ℕ) : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ i : ℕ × Bool, ∀ t, t ∈ I i →
      ∀ z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2),
        |iteratedDeriv j (fun s => F.reference i.1 i.2 s +
          stateJointKappaCLM W.hS W.hT W.radial.1 i.1 z * (-F.control i.1 i.2 s)) t| ≤
            C * E i ^ A := by
    obtain ⟨C, A, hC, hA, hb⟩ := F.stateSquare_material_jets j
    refine ⟨C, A, hC, hA, fun i t ht z hz => ?_⟩
    rw [F.square_affine z i.1 i.2]
    exact hb z hz i.1 i.2 t ht
  have hgjet (j : ℕ) : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ i : ℕ × Bool, ∀ t, t ∈ I i → ∀ v : AnnularState W.S × ℝ,
        |iteratedDeriv j (fun s =>
          stateJointKappaCLM W.hS W.hT W.radial.1 i.1 v * (-F.control i.1 i.2 s)) t| ≤
            C * E i ^ A * H i * pairGrading (stateGrading W.S) realGrading 0 v := by
    obtain ⟨C, A, hC, hA, hb⟩ := F.control_direction_material_jets j
    refine ⟨C, A, hC, hA, fun i t ht v => ?_⟩
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_neg,
      stateJointKappaCLM_apply, mul_neg, abs_neg]
    have hcost : 0 ≤ C * H i * E i ^ A :=
      mul_nonneg (mul_nonneg hC.le (hH i))
        (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
    exact (hb i.1 i.2 t ht v.1).trans
      ((mul_le_mul_of_nonneg_left (stateGrading_fst_le_jointStateGrading W.S 0 v)
        hcost).trans_eq (by ring))
  obtain ⟨B, A, hB, hA, hb⟩ := n04NegativeChart_affineSqrtJet_material_bounds
    (pairGrading (stateGrading W.S) realGrading 0)
    (isOpen_stateNeighborhood W.S W.C W.base (W.ε / 2)) I
    (fun i => F.reference i.1 i.2) (fun i t => -F.control i.1 i.2 t)
    (fun i => stateJointKappaCLM W.hS W.hT W.radial.1 i.1)
    (fun i => F.reference_smooth i.1 i.2) (fun i => (F.control_smooth i.1 i.2).neg)
    E H hE hH hR hHR (inv_pos.mpr hBi) hAi hlower hqjet hgjet n k
  refine ⟨B, A, hB, hA, fun m side t ht J z hz v => ?_⟩
  exact hb (m, side) t ht
    (J.congr (fun x _ => (congrArg (fun f : ℝ → ℝ => iteratedDeriv n f t)
      (F.speed_affine x m side)).symm)) z hz v

end ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_mixed_material_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_mixed_material_bounds
