module

public import ContinuousFlexibility.Analysis.StateKappaBounds
public import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# State seminorms and restriction to a common neighbourhood

The estimates here use the actual graded norms of the decoded circle
space.  In particular, the constant in the control-mean estimate is
independent of the state and of the component.  Increasing the low order
and decreasing the radius produces a smaller open state neighbourhood;
an existing directional tower restricts to that neighbourhood without
changing any of its derivatives.

No coefficient or flow estimate is assumed or asserted in this module.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The state grading is the sum of its actual height, scalar and circle gradings. -/
theorem stateGrading_apply (S : PhysicalSpacesData) (n : ℕ) (x : AnnularState S) :
    stateGrading S n x =
      ((S.height (3 / 4 : ℝ)).grading n x.1.1 + ‖x.1.2‖) +
        (‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading n x.2.2.1 +
          (S.circle (3 / 4 : ℝ)).grading n x.2.2.2)) := by
  simp only [stateGrading, heightPairGrading, pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, realGrading, coe_normSeminorm]

theorem stateGrading_monotone (S : PhysicalSpacesData) : Monotone (stateGrading S) := by
  have hheight : Monotone ((S.height (3 / 4 : ℝ)).grading) :=
    gradedSeminorm_monotone (fun n => (S.height (3 / 4 : ℝ)).level n)
      (S.height (3 / 4 : ℝ)).bond
  have hcircle : Monotone ((S.circle (3 / 4 : ℝ)).grading) :=
    gradedSeminorm_monotone (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond
  have hreal : Monotone realGrading := fun _ _ _ => le_rfl
  have hpair : Monotone (heightPairGrading S) :=
    tamePairGrading_monotone hheight hreal
  have htail : Monotone (pairGrading realGrading
      (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading)) :=
    tamePairGrading_monotone hreal (tamePairGrading_monotone hcircle hcircle)
  exact tamePairGrading_monotone hpair htail

theorem jointStateGrading_monotone (S : PhysicalSpacesData) :
    Monotone (pairGrading (stateGrading S) realGrading) :=
  tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)

theorem continuous_stateGrading (S : PhysicalSpacesData) (n : ℕ) :
    Continuous (stateGrading S n) := by
  have hheight : Continuous ((S.height (3 / 4 : ℝ)).grading n) :=
    continuous_gradedSeminorm _ _ n
  have hcircle : Continuous ((S.circle (3 / 4 : ℝ)).grading n) :=
    continuous_gradedSeminorm _ _ n
  have heq : (stateGrading S n : AnnularState S → ℝ) =
      (fun x =>
        ((S.height (3 / 4 : ℝ)).grading n x.1.1 + ‖x.1.2‖) +
          (‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading n x.2.2.1 +
            (S.circle (3 / 4 : ℝ)).grading n x.2.2.2))) := by
    funext x
    exact stateGrading_apply S n x
  rw [heq]
  exact ((hheight.comp (continuous_fst.comp continuous_fst)).add
      (continuous_snd.comp continuous_fst).norm).add
    ((continuous_fst.comp continuous_snd).norm.add
      ((hcircle.comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).add
        (hcircle.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

/-- Translation is checked separately in the normed projective coordinates. -/
private theorem continuous_projective_sub_const
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    (bond : ∀ n, E (n + 1) →L[ℝ] E n) (y : ProjectiveLimit E bond) :
    Continuous (fun x : ProjectiveLimit E bond => x - y) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (tendsto_projectiveLimit_iff E bond).mpr
  intro n
  change Filter.Tendsto (fun z => projectiveCoordinate E bond n (z - y)) (𝓝 x)
    (𝓝 (projectiveCoordinate E bond n (x - y)))
  simp only [map_sub]
  exact ((projectiveCoordinate E bond n).continuous.sub continuous_const).tendsto x

set_option backward.isDefEq.respectTransparency true in
/-- Product continuity uses only scalar and projective-coordinate translations. -/
private theorem continuous_annularState_sub_const (S : PhysicalSpacesData)
    (y : AnnularState S) : Continuous (fun x : AnnularState S => x - y) := by
  have hheight : Continuous (fun x : AnnularState S => x.1.1 - y.1.1) :=
    (continuous_projective_sub_const
      (E := fun n => (S.height (3 / 4 : ℝ)).level n)
      (S.height (3 / 4 : ℝ)).bond y.1.1).comp
      (continuous_fst.comp continuous_fst)
  have hc : Continuous (fun x : AnnularState S => x.1.2 - y.1.2) :=
    (continuous_snd.comp continuous_fst).sub continuous_const
  have hν : Continuous (fun x : AnnularState S => x.2.1 - y.2.1) :=
    (continuous_fst.comp continuous_snd).sub continuous_const
  have hκ : Continuous (fun x : AnnularState S => x.2.2.1 - y.2.2.1) :=
    (continuous_projective_sub_const
      (E := fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond y.2.2.1).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have hchart : Continuous (fun x : AnnularState S => x.2.2.2 - y.2.2.2) :=
    (continuous_projective_sub_const
      (E := fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond y.2.2.2).comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  exact (hheight.prodMk hc).prodMk (hν.prodMk (hκ.prodMk hchart))

theorem isOpen_stateNeighborhood (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) : IsOpen (stateNeighborhood S C base ε) := by
  have hsubtract : Continuous (fun z : AnnularState S × ℝ =>
      z.1 - C.referenceState) :=
    (continuous_annularState_sub_const S C.referenceState).comp continuous_fst
  have hstate : Continuous (fun z : AnnularState S × ℝ =>
      stateGrading S base (z.1 - C.referenceState)) :=
    (continuous_stateGrading S base).comp hsubtract
  have hrealProjection : Continuous (fun z : AnnularState S × ℝ => z.2) :=
    continuous_snd
  have hparameter : Continuous (fun z : AnnularState S × ℝ => |z.2|) :=
    hrealProjection.abs
  have hradius : Continuous (fun _ : AnnularState S × ℝ => ε) := continuous_const
  exact (isOpen_lt hstate hradius).inter (isOpen_lt hparameter hradius)

set_option backward.isDefEq.respectTransparency true in
/-- The same reference belongs to every positive-radius state neighbourhood. -/
theorem reference_mem_stateNeighborhood (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  constructor
  · have hzero : C.referenceState - C.referenceState = (0 : AnnularState S) :=
      sub_self C.referenceState
    have hgrade : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
      (congrArg (fun x : AnnularState S => stateGrading S base x) hzero).trans
        (stateGrading S base).map_zero'
    exact hgrade.trans_lt hε
  · simpa only [abs_zero] using hε

/-- Increasing the controlling order and decreasing the radius preserves
every condition already known on the old state neighbourhood. -/
theorem stateNeighborhood_subset {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base base' : ℕ} {ε ε' : ℝ} (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨((stateGrading_monotone S hb _).trans_lt hz.1).trans_le hε,
    hz.2.trans_le hε⟩

theorem stateNeighborhood_max_min_subset_left (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base₁ base₂ : ℕ) (ε₁ ε₂ : ℝ) :
    stateNeighborhood S C (max base₁ base₂) (min ε₁ ε₂) ⊆
      stateNeighborhood S C base₁ ε₁ :=
  stateNeighborhood_subset (le_max_left _ _) (min_le_left _ _)

theorem stateNeighborhood_max_min_subset_right (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base₁ base₂ : ℕ) (ε₁ ε₂ : ℝ) :
    stateNeighborhood S C (max base₁ base₂) (min ε₁ ε₂) ⊆
      stateNeighborhood S C base₂ ε₂ :=
  stateNeighborhood_subset (le_max_right _ _) (min_le_right _ _)

/-- A circle level is controlled by the increasing circle grading. -/
theorem circleNorm_decode_le_grading {T : MaterialData} {γ : ℝ}
    {M : CircleModelData} (hM : IsCircleModel T γ M) (u : M.Space) {s n : ℕ}
    (hsn : s ≤ n) : circleNorm T γ s (M.decode u) ≤ M.grading n u := by
  obtain ⟨_, _, _, _, _, _, _, hnorm⟩ := hM
  calc
    circleNorm T γ s (M.decode u) = ‖u.val s‖ := (hnorm u s).symm
    _ ≤ M.grading n u := norm_coordinate_le_graded _ _ hsn u

/-- The control-circle grading is one nonnegative summand of the state grading. -/
theorem state_controlCircle_grading_le (S : PhysicalSpacesData) (n : ℕ)
    (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).grading n x.2.2.1 ≤ stateGrading S n x := by
  rw [stateGrading_apply]
  have hheight := apply_nonneg ((S.height (3 / 4 : ℝ)).grading n) x.1.1
  have hchart := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.2
  have hc := norm_nonneg x.1.2
  have hν := norm_nonneg x.2.1
  linarith

/-- The quantitative mean estimate, with an explicit constant and a real
state seminorm instead of a state-dependent existential constant. -/
theorem abs_stateKappa_le_stateGrading {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b) (x : AnnularState S) (n m : ℕ) :
    |stateKappa S x m| ≤
      (((1 / Real.pi) * Real.sqrt Real.pi) * stateGrading S n x) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have hmodel : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) :=
    hS.2.1 (3 / 4 : ℝ)
  have hmember : CircleMember T (3 / 4 : ℝ)
      ((S.circle (3 / 4 : ℝ)).decode x.2.2.1) := hmodel.2.2.2.1 x.2.2.1
  have hH (i : ℕ) : 0 < T.H (T.sample i) := (hT.2.1 _ (hsample i)).2.1
  have hnorm : circleNorm T (3 / 4 : ℝ) 0
      ((S.circle (3 / 4 : ℝ)).decode x.2.2.1) ≤ stateGrading S n x :=
    (circleNorm_decode_le_grading hmodel x.2.2.1 (Nat.zero_le n)).trans
      (state_controlCircle_grading_le S n x)
  have hconstant : 0 ≤ (1 / Real.pi) * Real.sqrt Real.pi :=
    mul_nonneg (div_nonneg zero_le_one Real.pi_pos.le) (Real.sqrt_nonneg _)
  exact (circleMember_angularMean_bound hmember hH m).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hconstant)
      (Real.rpow_nonneg (hH m).le _))

theorem abs_stateKappa_le_stateGrading_of_accumulatingProfile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (x : AnnularState S) (n m : ℕ) :
    |stateKappa S x m| ≤
      (((1 / Real.pi) * Real.sqrt Real.pi) * stateGrading S n x) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  obtain ⟨_, hbounds⟩ := hRef
  exact abs_stateKappa_le_stateGrading hS hT
    (materialSample_mem_radialCore hT hbounds.2.1) x n m

/-- The decoded mean depends only on the control-circle component. -/
theorem stateKappa_eq_of_controlComponent_eq {S : PhysicalSpacesData}
    {x y : AnnularState S} (h : x.2.2.1 = y.2.2.1) (m : ℕ) :
    stateKappa S x m = stateKappa S y m := by
  exact congrArg (fun u : CircleSpace S =>
    angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) h

private theorem nestedProd_control_sub {A B C D E : Type*}
    [Sub A] [Sub B] [Sub C] [Sub D] [Sub E]
    (x y : (A × B) × (C × (D × E))) :
    (x - y).2.2.1 = x.2.2.1 - y.2.2.1 := by
  rw [Prod.snd_sub, Prod.snd_sub, Prod.fst_sub]

set_option backward.isDefEq.respectTransparency true in
/-- The displacement has the same control component because the reference
control sequence is zero. -/
theorem stateKappa_sub_reference {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    (x : AnnularState S) (m : ℕ) :
    stateKappa S (x - C.referenceState) m = stateKappa S x m := by
  have hkappa : C.referenceState.2.2.1 = 0 := href.2.2.2.1
  have hcomponent : (x - C.referenceState).2.2.1 = x.2.2.1 :=
    (nestedProd_control_sub
      (A := (S.height (3 / 4 : ℝ)).Space) (B := ℝ) (C := ℝ)
      (D := CircleSpace S) (E := CircleSpace S) x C.referenceState).trans
      ((congrArg (fun u : CircleSpace S => x.2.2.1 - u) hkappa).trans (sub_zero x.2.2.1))
  exact stateKappa_eq_of_controlComponent_eq
    (x := x - C.referenceState) (y := x) hcomponent m

set_option backward.isDefEq.respectTransparency true in
/-- A common low-order state ball gives one uniform smallness bound for
every actual control mean. -/
theorem abs_stateKappa_le_radius {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (href : referenceStateConditions D S C)
    {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ) :
    |stateKappa S z.1 m| ≤
      (((1 / Real.pi) * Real.sqrt Real.pi) * ε) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have h := abs_stateKappa_le_stateGrading_of_accumulatingProfile hS hT hRef
    (z.1 - C.referenceState) base m
  have hmean : |stateKappa S z.1 m| = |stateKappa S (z.1 - C.referenceState) m| :=
    congrArg abs (stateKappa_sub_reference href z.1 m).symm
  have hconstant : 0 ≤ (1 / Real.pi) * Real.sqrt Real.pi :=
    mul_nonneg (div_nonneg zero_le_one Real.pi_pos.le) (Real.sqrt_nonneg _)
  obtain ⟨_, hbounds⟩ := hRef
  have hH : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hbounds.2.1 m)).2.1
  exact hmean.trans_le (h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hz.1.le hconstant) (Real.rpow_nonneg hH.le _)))

section Restriction

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- A genuine directional tower restricts to any smaller open domain. -/
def SmoothDirections.restrict {U V : Set E} {f : E → F}
    (J : SmoothDirections U f) (hV : IsOpen V) (hVU : V ⊆ U) :
    SmoothDirections V f where
  open_domain := hV
  D := J.D
  zero := fun x hx => J.zero x (hVU hx)
  continuous := fun n => (J.continuous n).mono (fun _ hx => ⟨hVU hx.1, hx.2⟩)
  derivative := fun n x hx v w => J.derivative n x (hVU hx) v w

end Restriction

section VariationWeights

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem oneHighVariationWeight_nonneg (p : ℕ → Seminorm ℝ E)
    (base high : ℕ) (x : E) {k : ℕ} (v : Fin k → E) :
    0 ≤ oneHighVariationWeight p base high x v := by
  unfold oneHighVariationWeight
  positivity

/-- Combining two estimates on one stronger low-order neighbourhood does
not worsen the one-high-factor expression on their right-hand sides. -/
theorem oneHighVariationWeight_mono {p : ℕ → Seminorm ℝ E}
    (hp : Monotone p) {base base' high high' : ℕ}
    (hb : base ≤ base') (hh : high ≤ high') (x : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p base high x v ≤
      oneHighVariationWeight p base' high' x v := by
  unfold oneHighVariationWeight
  apply add_le_add
  · apply mul_le_mul
    · exact add_le_add (le_refl 1) (hp hh x)
    · exact Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
        (fun i _ => hp hb (v i))
    · positivity
    · positivity
  · apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul
    · exact hp hh (v i)
    · exact Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
        (fun j _ => hp hb (v j))
    · positivity
    · exact apply_nonneg _ _

end VariationWeights

/-- Restricting the parameter set leaves the defining ordinary ODE and
all its initial, continuity and circle-lift properties unchanged. -/
theorem ordinaryFlowConditions_mono {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {U V : Set (AnnularState S × ℝ)}
    (h : ordinaryFlowConditions D S C U) (hVU : V ⊆ U) :
    ordinaryFlowConditions D S C V := fun z hz => h z (hVU hz)

end ContinuousFlexibility.Statements
