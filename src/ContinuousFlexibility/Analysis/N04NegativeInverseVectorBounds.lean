module

public import ContinuousFlexibility.Analysis.N04NegativeInverseOutputAtoms
public import ContinuousFlexibility.Analysis.N04NegativeInversePhysicalBounds

/-!
# Recover the actual vector chart from its normalized scalar atoms

The radial coordinate is a fixed affine output normalization. The
angular coordinate adds the original physical angle. The latter has
only a first spatial derivative, so it introduces no height loss on
positive parameter tuples and no extra power in the spatial budget.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements CanonicalGeometry

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Fixed affine scalar normalizations recover the vector chart with
the same parameter height and the same saved spatial degree. -/
theorem n04NegativeInverse_vector_of_normalizedAtoms
    {U : Set (E × PolarPoint)} {F : E × PolarPoint → PolarPoint}
    (J : SmoothDirections U F) (left span : ℝ) (hspan : span ≠ 0)
    (JR : SmoothDirections U (fun x => ((F x).1 - left) / span))
    (JA : SmoothDirections U (fun x => (F x).2 - x.2.2))
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (shift : ℕ)
    {x : E × PolarPoint} (hx : x ∈ U)
    (v : Fin n → E × PolarPoint)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0)
    {C H t : ℝ} (hC : 1 ≤ C) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hr : |JR.D n x v| ≤ C * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1))
    (ha : |JA.D n x v| ≤ C * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1)) :
    ‖J.D n x v‖ ≤ (2 + |span|) * C * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1) := by
  let Q : ℝ := parameterHeightWeight H w.stateArity *
    t ^ (w.angleArity + shift * w.stateArity - 1)
  have hQ : 0 ≤ Q := mul_nonneg (parameterHeightWeight_nonneg hH _)
    (pow_nonneg (zero_le_one.trans ht) _)
  have hCQ : 0 ≤ C * Q := mul_nonneg (zero_le_one.trans hC) hQ
  have hr' : |JR.D n x v| ≤ C * Q := by simpa only [Q, mul_assoc] using hr
  have ha' : |JA.D n x v| ≤ C * Q := by simpa only [Q, mul_assoc] using ha
  have hradial : |(J.D n x v).1| ≤ |span| * (C * Q) := by
    have he := n04NegativeInverse_affineRadial_jet J left span JR hn hx v
    have he' : (J.D n x v).1 = JR.D n x v * span := (div_eq_iff hspan).mp he.symm
    rw [he', abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hr' (abs_nonneg span)
  have hangle : |(J.D n x v).2| ≤ 2 * (C * Q) := by
    by_cases hk : w.stateArity = 0
    · let L : (E × PolarPoint) →L[ℝ] ℝ :=
        (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
      let T := smoothDirectionsOfJets J.open_domain (continuousLinearJets L)
        (hasProjectiveJetsOn_continuousLinear L U)
      have hT : |T.D n x v| ≤ 1 := by
        change |continuousLinearJets L n x v| ≤ 1
        cases n with
        | zero => exact (Nat.lt_irrefl 0 hn).elim
        | succ n =>
            cases n with
            | zero =>
                simp only [continuousLinearJets,
                  ContinuousMultilinearMap.ofSubsingleton_apply_apply]
                change |(v 0).2.2| ≤ 1
                exact (show |(v 0).2.2| ≤ ‖(v 0).2‖ from by
                  simpa only [Real.norm_eq_abs] using norm_snd_le (v 0).2).trans
                    (hphysical 0)
            | succ n =>
                simp only [continuousLinearJets, ContinuousMultilinearMap.zero_apply,
                  abs_zero, zero_le_one]
      let A : SmoothDirections U (fun x => (F x).2) :=
        (smoothDirections_postcompCLM J (ContinuousLinearMap.snd ℝ ℝ ℝ)).congrOn
          (fun _ _ => rfl)
      let B : SmoothDirections U (fun x => (F x).2) :=
        (smoothDirectionsAdd JA T).congrOn (fun x _ => by
          change (F x).2 - x.2.2 + x.2.2 = (F x).2
          exact sub_add_cancel _ _)
      have he := congrArg (fun A : (E × PolarPoint) [×n]→L[ℝ] ℝ => A v)
        (B.unique A n x hx)
      change JA.D n x v + T.D n x v =
        (smoothDirections_postcompCLM J (ContinuousLinearMap.snd ℝ ℝ ℝ)).D n x v at he
      have he' : (J.D n x v).2 = JA.D n x v + T.D n x v := by
        simpa only [smoothDirections_postcompCLM_D_apply,
          ContinuousLinearMap.coe_snd'] using he.symm
      have hQ₁ : 1 ≤ Q := by
        dsimp only [Q]
        rw [parameterHeightWeight, if_pos hk, one_mul]
        exact one_le_pow₀ ht
      have hCQ₁ : 1 ≤ C * Q := one_le_mul_of_one_le_of_one_le hC hQ₁
      rw [he']
      exact ((abs_add_le _ _).trans (add_le_add ha' hT)).trans (by linarith)
    · have he := n04NegativeInverse_angleDefect_jet J JA w (Nat.pos_of_ne_zero hk) hx v
        hspatial
      rw [← he]
      exact ha'.trans (by linarith)
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hradial' : |(J.D n x v).1| ≤ (2 + |span|) * (C * Q) :=
    hradial.trans (mul_le_mul_of_nonneg_right (by linarith) hCQ)
  have hangle' : |(J.D n x v).2| ≤ (2 + |span|) * (C * Q) :=
    hangle.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hCQ)
  exact (max_le hradial' hangle').trans_eq (by dsimp only [Q]; ring)

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem negativeInverse_physical_chartRadial
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter G.W.S)
    (m : ℕ) (p : PolarPoint) :
    G.negativeInversePhysicalAtomFamily η .chartRadial z m p =
      (((G.V η).chart (G.lift η z) m p).1 - (G.V η).left m) /
        ((G.V η).right m - (G.V η).left m) := by
  have lengths := G.negativeInverse_length_values
  have hl := lengths.choose_spec.2
  have hp := n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData (G.V η))
    (sub_pos.mp (hl η m).1) p
  change (((G.V η).chart (G.lift η z) m
    (physicalUnitPoint (G.V η) m
      (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) m p))).1 -
        (G.V η).left m) / ((G.V η).right m - (G.V η).left m) = _
  exact congrArg (fun q : PolarPoint =>
    (((G.V η).chart (G.lift η z) m q).1 - (G.V η).left m) /
      ((G.V η).right m - (G.V η).left m)) hp

theorem negativeInverse_physical_chartAngleDefect
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter G.W.S)
    (m : ℕ) (p : PolarPoint) :
    G.negativeInversePhysicalAtomFamily η .chartAngleDefect z m p =
      ((G.V η).chart (G.lift η z) m p).2 - p.2 := by
  have lengths := G.negativeInverse_length_values
  have hl := lengths.choose_spec.2
  have hp := n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData (G.V η))
    (sub_pos.mp (hl η m).1) p
  change ((G.V η).chart (G.lift η z) m
    (physicalUnitPoint (G.V η) m
      (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) m p))).2 -
        (physicalUnitPoint (G.V η) m
          (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) m p)).2 = _
  exact congrArg (fun q : PolarPoint =>
    ((G.V η).chart (G.lift η z) m q).2 - q.2) hp

theorem negativeInverse_physical_height
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter G.W.S)
    (m : ℕ) (p : PolarPoint) :
    G.negativeInversePhysicalAtomFamily η .height z m p =
      (G.V η).height (G.lift η z) m p := by
  have lengths := G.negativeInverse_length_values
  have hl := lengths.choose_spec.2
  have hp := n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData (G.V η))
    (sub_pos.mp (hl η m).1) p
  change (G.V η).height (G.lift η z) m
    (physicalUnitPoint (G.V η) m
      (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) m p)) = _
  exact congrArg ((G.V η).height (G.lift η z) m) hp

/-- Actual whole-component scalar atom bounds give the vector forward
bound required by the genuine implicit recurrence. -/
theorem negativeInverse_vector_forward_bound
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ)
    {U : Set (Parameter G.W.S × PolarPoint)}
    (J : SmoothDirections U
      (fun x : Parameter G.W.S × PolarPoint => (G.V η).chart (G.lift η x.1) m x.2))
    (JR : SmoothDirections U
      (fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily η .chartRadial x.1 m x.2))
    (JA : SmoothDirections U
      (fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily η .chartAngleDefect x.1 m x.2))
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (shift : ℕ)
    {x : Parameter G.W.S × PolarPoint} (hx : x ∈ U)
    (v : Fin n → Parameter G.W.S × PolarPoint)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0)
    {C H t : ℝ} (hC : 1 ≤ C) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hr : |JR.D n x v| ≤ C * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1))
    (ha : |JA.D n x v| ≤ C * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1)) :
    ‖J.D n x v‖ ≤ (2 + |(G.V η).right m - (G.V η).left m|) * C *
      parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) := by
  have lengths := G.negativeInverse_length_values
  have hl := lengths.choose_spec.2
  exact n04NegativeInverse_vector_of_normalizedAtoms J
    ((G.V η).left m) ((G.V η).right m - (G.V η).left m) (hl η m).2.1.ne'
    (JR.congrOn (fun x _ => G.negativeInverse_physical_chartRadial η x.1 m x.2))
    (JA.congrOn (fun x _ => G.negativeInverse_physical_chartAngleDefect η x.1 m x.2))
    hn w shift hx v hphysical hspatial hC hH ht hr ha

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_vector_forward_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_vector_forward_bound
