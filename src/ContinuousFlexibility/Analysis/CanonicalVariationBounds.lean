import ContinuousFlexibility.Analysis.StateNeighborhood
import ContinuousFlexibility.Analysis.MaterialSampleBounds
import ContinuousFlexibility.Analysis.N01JetBounds
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Values controlled by genuine first variations

The zeroth tame bound contains a constant term and does not imply that a
coefficient is small near the reference state.  The first directional jet
does: its actual derivative along the segment from the reference state
controls the change in value.  The estimates retain the low seminorm
factor explicitly before reducing to a linear high seminorm bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section FirstVariation

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A bound on the genuine first jet along a convex segment bounds the
change in value.  No norm is imposed on the source space. -/
theorem norm_sub_le_of_smoothDirections_first_bound
    {U : Set E} {f : E → G} (J : SmoothDirections U f) (hU : Convex ℝ U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖J.D 1 (x + t • (y - x)) (Fin.cons (y - x) Fin.elim0)‖ ≤ M) :
    ‖f y - f x‖ ≤ M := by
  have hJ : HasProjectiveJetsOn f J.D U :=
    ⟨J.zero, J.continuous, fun n z hz w v => J.derivative n z hz v w⟩
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u : ℝ => f (x + u • (y - x)))
        (J.D 1 (x + t • (y - x)) (Fin.cons (y - x) Fin.elim0)) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have h := hJ.hasLineDerivAt J.open_domain
      (hU.add_smul_sub_mem hx hy ht) (y - x)
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      projectiveFirstJetValue, zero_add, zero_smul, add_zero, add_smul, add_assoc] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => hM t (Ico_subset_Icc_self ht))
  have hxy : x + (y - x) = y := by abel
  simpa only [one_smul, zero_smul, add_zero, hxy] using h

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- At arity one, there are exactly two terms in the tame weight. -/
theorem oneHighVariationWeight_one (p : ℕ → Seminorm ℝ E)
    (base high : ℕ) (x : E) (v : Fin 1 → E) :
    oneHighVariationWeight p base high x v =
      (1 + p high x) * p base (v 0) + p high (v 0) := by
  simp [oneHighVariationWeight]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- On a reference segment the nonlinear high-low product retains the
small low displacement factor. -/
theorem oneHighVariationWeight_segment_le (p : ℕ → Seminorm ℝ E)
    (base high : ℕ) (d : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    oneHighVariationWeight p base high (t • d) (Fin.cons d Fin.elim0) ≤
      p base d + (1 + p base d) * p high d := by
  rw [oneHighVariationWeight_one]
  simp only [Fin.cons_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have h := mul_le_mul_of_nonneg_right ht.2
    (mul_nonneg (apply_nonneg (p high) d) (apply_nonneg (p base) d))
  nlinarith

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Increasing the high order to the maximum with the base order turns
the displacement expression into a linear bound. -/
theorem oneHigh_displacement_le_linear_high
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (base high : ℕ) (d : E)
    {η : ℝ} (hlow : p base d ≤ η) :
    p base d + (1 + p base d) * p high d ≤ (2 + η) * p (max base high) d := by
  have hbase := hp (Nat.le_max_left base high) d
  have hhigh := hp (Nat.le_max_right base high) d
  have hproduct := mul_le_mul_of_nonneg_left hhigh
    (add_nonneg zero_le_one (apply_nonneg (p base) d))
  have hsmall := mul_le_mul_of_nonneg_right hlow (apply_nonneg (p (max base high)) d)
  nlinarith

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The weighted scalar consequence is proved before specializing to the
projective state space, so no large concrete term needs rewriting. -/
theorem weighted_oneHigh_displacement_le_linear_high
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (base high : ℕ) (d : E)
    {A η V : ℝ} (hA : 0 ≤ A) (hlow : p base d ≤ η)
    (hV : V ≤ A * (p base d + (1 + p base d) * p high d)) :
    V ≤ A * (2 + η) * p (max base high) d := by
  have h := hV.trans (mul_le_mul_of_nonneg_left
    (oneHigh_displacement_le_linear_high p hp base high d hlow) hA)
  simpa only [mul_assoc] using h

/-- Integrating a one-high-factor first-variation estimate removes the
constant term from the value bound. -/
theorem abs_sub_le_of_oneHigh_first_bound
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f) (hU : Convex ℝ U)
    (p : ℕ → Seminorm ℝ E) (base high : ℕ)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ z ∈ U, ∀ v : Fin 1 → E,
      |J.D 1 z v| ≤ A * oneHighVariationWeight p base high (z - x) v) :
    |f y - f x| ≤ A *
      (p base (y - x) + (1 + p base (y - x)) * p high (y - x)) := by
  apply norm_sub_le_of_smoothDirections_first_bound J hU hx hy
  intro t ht
  have h := hD (x + t • (y - x)) (hU.add_smul_sub_mem hx hy ht)
    (Fin.cons (y - x) Fin.elim0)
  have heq : x + t • (y - x) - x = t • (y - x) := by abel
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (oneHighVariationWeight_segment_le p base high (y - x) ht) hA)

/-- The reference value vanishes, so the variation estimate is a value
estimate with an explicit small low factor. -/
theorem abs_le_of_oneHigh_first_bound
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f) (hU : Convex ℝ U)
    (p : ℕ → Seminorm ℝ E) (base high : ℕ)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hzero : f x = 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ z ∈ U, ∀ v : Fin 1 → E,
      |J.D 1 z v| ≤ A * oneHighVariationWeight p base high (z - x) v) :
    |f y| ≤ A *
      (p base (y - x) + (1 + p base (y - x)) * p high (y - x)) := by
  simpa only [hzero, sub_zero] using
    abs_sub_le_of_oneHigh_first_bound J hU p base high hx hy hA hD

/-- A first-variation tower may be supplied existentially, as it is in
N01.  Its elimination takes place over an abstract source space. -/
theorem abs_le_of_exists_oneHigh_first_bound
    {U : Set E} {f : E → ℝ} (hU : Convex ℝ U)
    (p : ℕ → Seminorm ℝ E) (base high : ℕ)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hzero : f x = 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hJ : ∃ J : SmoothDirections U f, ∀ z ∈ U, ∀ v : Fin 1 → E,
      |J.D 1 z v| ≤ A * oneHighVariationWeight p base high (z - x) v) :
    |f y| ≤ A *
      (p base (y - x) + (1 + p base (y - x)) * p high (y - x)) := by
  obtain ⟨J, hD⟩ := hJ
  exact abs_le_of_oneHigh_first_bound J hU p base high hx hy hzero hA hD

/-- A low displacement bound gives a linear high displacement estimate,
with the size of the low neighborhood still explicit. -/
theorem abs_le_of_oneHigh_first_bound_low
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f) (hU : Convex ℝ U)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    {base high : ℕ} (hbh : base ≤ high)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hzero : f x = 0)
    {A η : ℝ} (hA : 0 ≤ A) (hlow : p base (y - x) ≤ η)
    (hD : ∀ z ∈ U, ∀ v : Fin 1 → E,
      |J.D 1 z v| ≤ A * oneHighVariationWeight p base high (z - x) v) :
    |f y| ≤ A * (2 + η) * p high (y - x) := by
  apply (abs_le_of_oneHigh_first_bound J hU p base high hx hy hzero hA hD).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hA
  have hsmall := mul_le_mul_of_nonneg_right hlow (apply_nonneg (p high) (y - x))
  have hbase := hp hbh (y - x)
  nlinarith

end FirstVariation

/-- The coefficient family was defined as an actual mixed derivative of
the difference from the reference coefficients. -/
@[simp] theorem coefficientFamily_reference (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 3) (a b : ℕ) (p : PolarPoint) :
    coefficientFamily D S C i a b p (C.referenceState, 0) = 0 := by
  simp only [coefficientFamily, sub_self, mixedDerivative, iteratedDeriv_fun_const_zero]

/-- The two separate low conditions in the state neighborhood control the
actual product grading of the displacement. -/
theorem pairGrading_displacement_le_two_mul_radius
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    pairGrading (stateGrading S) realGrading base (z - (C.referenceState, 0)) ≤ 2 * ε := by
  simp only [pairGrading_apply, realGrading, coe_normSeminorm, Real.norm_eq_abs,
    Prod.fst_sub, Prod.snd_sub, sub_zero]
  have h₁ := hz.1
  have h₂ := hz.2
  linarith

/-- One coefficient-value order, with its low and high displacement factors kept explicit.
Naming the body keeps existential elimination independent of state-space expansion. -/
def N01CoefficientDisplacementBoundAtOrder (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ m i a b p,
      a + b ≤ s → p.1 ∈ D.cells m → ∀ z ∈ stateNeighborhood S C base ε,
      |coefficientFamily D S C i a b p z| ≤
        B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          (pairGrading (stateGrading S) realGrading base (z - (C.referenceState, 0)) +
            (1 + pairGrading (stateGrading S) realGrading base (z - (C.referenceState, 0))) *
              pairGrading (stateGrading S) realGrading (s + loss)
                (z - (C.referenceState, 0)))

/-- One coefficient-value order with linear high-displacement control.
Naming the body keeps existential elimination independent of state-space expansion. -/
def N01CoefficientLinearHighBoundAtOrder (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ m i a b p,
      a + b ≤ s → p.1 ∈ D.cells m → ∀ z ∈ stateNeighborhood S C base ε,
      |coefficientFamily D S C i a b p z| ≤
        B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          (2 + 2 * ε) * pairGrading (stateGrading S) realGrading
            (max base (s + loss)) (z - (C.referenceState, 0))

/-- One angular flow-value order, without a radial collar weight.
Naming the body keeps existential elimination independent of state-space expansion. -/
def N01FlowDisplacementBoundAtOrder (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ)
    (s : ℕ) (B : ℝ) : Prop :=
  ∀ m b p,
      b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      ∀ z ∈ stateNeighborhood S C base ε,
      |ordinaryFlowFamily S C m 0 b p z| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
          (pairGrading (stateGrading S) realGrading base (z - (C.referenceState, 0)) +
            (1 + pairGrading (stateGrading S) realGrading base (z - (C.referenceState, 0))) *
              pairGrading (stateGrading S) realGrading (s + loss)
                (z - (C.referenceState, 0)))

/-- One angular flow-value order with linear high-displacement control.
Naming the body keeps existential elimination independent of state-space expansion. -/
def N01FlowLinearHighBoundAtOrder (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ)
    (s : ℕ) (B : ℝ) : Prop :=
  ∀ m b p,
      b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      ∀ z ∈ stateNeighborhood S C base ε,
      |ordinaryFlowFamily S C m 0 b p z| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
          (2 + 2 * ε) * pairGrading (stateGrading S) realGrading
            (max base (s + loss)) (z - (C.referenceState, 0))

/-- N01's first derivative estimate gives a value estimate with no
constant displacement term, at every physical coefficient order. -/
theorem coefficientFamily_le_displacement_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ N01CoefficientDisplacementBoundAtOrder D T S C base loss ε s B := by
  obtain ⟨B, hB, hbound⟩ := (n01CoefficientJetBounds_of_properties hN) 1 s
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp z hz
  exact abs_le_of_exists_oneHigh_first_bound (convex_stateNeighborhood S C base ε)
    (pairGrading (stateGrading S) realGrading) base (s + loss)
    (reference_mem_stateNeighborhood S C base hN.2.1) hz
    (coefficientFamily_reference D S C i a b p)
    (materialSample_factor_nonneg hN.1.1 hT hB.le m) (hbound m i a b p hab hp)

/-- The same N01 estimate is linear in a high displacement seminorm.
The explicit factor `2 + 2 * ε` is bounded by three when `ε ≤ 1 / 2`. -/
theorem coefficientFamily_le_linear_high_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ N01CoefficientLinearHighBoundAtOrder D T S C base loss ε s B := by
  obtain ⟨B, hB, hbound⟩ := coefficientFamily_le_displacement_of_n01 hT hN s
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp z hz
  have hgrade : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  exact weighted_oneHigh_displacement_le_linear_high
    (pairGrading (stateGrading S) realGrading) hgrade base (s + loss)
    (z - (C.referenceState, 0))
    (A := B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)
    (η := 2 * ε) (V := |coefficientFamily D S C i a b p z|)
    (materialSample_factor_nonneg hN.1.1 hT hB.le m)
    (pairGrading_displacement_le_two_mul_radius hz) (hbound m i a b p hab hp z hz)

/-- The ordinary flow family is also the actual difference from its
reference value, including at every angular derivative order. -/
@[simp] theorem ordinaryFlowFamily_reference (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (m a b : ℕ) (p : PolarPoint) :
    ordinaryFlowFamily S C m a b p (C.referenceState, 0) = 0 := by
  simp only [ordinaryFlowFamily, sub_self, mixedDerivative, iteratedDeriv_fun_const_zero]

/-- At radial order zero N01 has no collar weight.  Its genuine first
variations control all angular orders by the state displacement, with one
parameter-order loss chosen before the angular order. -/
theorem ordinaryFlowFamily_le_displacement_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) :
    ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      N01FlowDisplacementBoundAtOrder T S C base (loss + parameterLoss) ε s B := by
  obtain ⟨parameterLoss, horders⟩ := (n01FlowJetBounds_of_properties hN) 1
  refine ⟨parameterLoss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := horders s
  refine ⟨B, hB, ?_⟩
  intro m b p hb hp z hz
  apply abs_le_of_exists_oneHigh_first_bound (convex_stateNeighborhood S C base ε)
    (pairGrading (stateGrading S) realGrading) base (s + (loss + parameterLoss))
    (reference_mem_stateNeighborhood S C base hN.2.1) hz
    (ordinaryFlowFamily_reference S C m 0 b p)
    (materialSample_factor_nonneg hN.1.1 hT hB.le (C.cell m))
  simpa only [pow_zero, one_mul, Nat.add_assoc] using
    hbound m 0 b p (by simpa only [Nat.zero_add] using hb) hp

/-- The angular flow difference has a uniform linear high-displacement
bound with the same sampled material weights as the original N01 jet. -/
theorem ordinaryFlowFamily_le_linear_high_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) :
    ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      N01FlowLinearHighBoundAtOrder T S C base (loss + parameterLoss) ε s B := by
  obtain ⟨parameterLoss, horders⟩ := ordinaryFlowFamily_le_displacement_of_n01 hT hN
  refine ⟨parameterLoss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := horders s
  refine ⟨B, hB, ?_⟩
  intro m b p hb hp z hz
  have hgrade : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  exact weighted_oneHigh_displacement_le_linear_high
    (pairGrading (stateGrading S) realGrading) hgrade base (s + (loss + parameterLoss))
    (z - (C.referenceState, 0))
    (A := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B)
    (η := 2 * ε) (V := |ordinaryFlowFamily S C m 0 b p z|)
    (materialSample_factor_nonneg hN.1.1 hT hB.le (C.cell m))
    (pairGrading_displacement_le_two_mul_radius hz) (hbound m b p hb hp z hz)

end ContinuousFlexibility.Analysis
