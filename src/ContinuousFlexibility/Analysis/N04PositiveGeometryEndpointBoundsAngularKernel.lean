import ContinuousFlexibility.Analysis.N04PositiveGeometryFiniteKernelBounds
import ContinuousFlexibility.Analysis.N01cStateAngleSelections
import ContinuousFlexibility.Analysis.N01cPhysicalGraphJets
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Actual state-angle slots in the finite endpoint kernel

Each partition block is identified with the original angular-state jet
of each scalar input. Its parameter arity and angular cost are then
summed by the exact word identities. This provides the finite-kernel
consumer for root radial traces and for their finite recurrences.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set E} {ι : Type*} [Fintype ι] {f : ι → E × ℝ → ℝ}

/-- The bound concerns any genuine output tower. Its inputs are the
literal scalar angular traces, in the order selected by the original
joint word. The scale exponent is the sum of their assigned orders. -/
theorem n04PositiveGeometry_angularKernel_weighted_bound
    (hU : IsOpen U)
    (J : ∀ i, SmoothDirections (U ×ˢ (univ : Set ℝ)) (f i))
    (JA : ∀ i b θ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => f i (x, η)) θ))
    {V : Set (ι → ℝ)} (hV : IsOpen V) {g : (ι → ℝ) → G}
    (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo (fun z i => f i z) (U ×ˢ univ) V)
    (Q : SmoothDirections (U ×ˢ univ) (fun z => g (fun i => f i z)))
    {n : ℕ} (w : StateAngleWord n) (shift : ℕ)
    (x : E) (hx : x ∈ U) (θ : ℝ) (v : Fin n → E × ℝ) (hv : w.IsPure v)
    (P : E → Prop) (hP : ∀ i, P (v i).1)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (houter : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (fun i => f i (x, θ))‖ ≤ C)
    (hinputs : ∀ i k b, k ≤ w.stateArity → b ≤ w.angleArity →
      ∀ u : Fin k → E, (∀ j, P (u j)) →
      ‖(JA i b θ).D k x u‖ ≤
        M * parameterHeightWeight H k * t ^ (b + shift * k)) :
    ‖Q.D n (x, θ) v‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) *
      C * M ^ n * L ^ n * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity) := by
  let JT := smoothDirectionsScalarPi (hU.prod isOpen_univ) J
  let κ : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
    fun c j => (w.restrict (c.emb j)).stateArity
  let cost : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
    fun c j => (w.restrict (c.emb j)).angleArity + shift * κ c j
  have hκ (c : OrderedFinpartition n) : ∑ j, κ c j = w.stateArity :=
    w.sum_restrict_stateArity c
  have hcost (c : OrderedFinpartition n) :
      ∑ j, cost c j ≤ w.angleArity + shift * w.stateArity := by
    dsimp only [cost, κ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      w.sum_restrict_angleArity c, w.sum_restrict_stateArity c]
  have hinner (c : OrderedFinpartition n) (j : Fin c.length) :
      ‖JT.D (c.partSize j) (x, θ) (v ∘ c.emb j)‖ ≤
        M * parameterHeightWeight H (κ c j) * t ^ cost c j := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg
      (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))).mpr
    intro i
    simp only [JT, smoothDirectionsScalarPi, ContinuousMultilinearMap.pi_apply]
    let wj := w.restrict (c.emb j)
    let u := wj.stateDirections (v ∘ c.emb j)
    have hu (a : Fin wj.stateArity) : P (u a) := by
      obtain ⟨l, _, he⟩ := wj.stateDirections_mem_range (v ∘ c.emb j) a
      change P (wj.stateDirections (v ∘ c.emb j) a)
      rw [he]
      exact hP (c.emb j l)
    have hpure : wj.pureSlots u = v ∘ c.emb j :=
      wj.pureSlots_stateDirections _ (hv.restrict (c.emb j))
    have he := smoothDirections_joint_pureSlots (J i) (JA i) wj hx θ u
    have hk : wj.stateArity ≤ w.stateArity :=
      (Finset.single_le_sum (fun l _ => Nat.zero_le (w.restrict (c.emb l)).stateArity)
        (Finset.mem_univ j)).trans_eq (w.sum_restrict_stateArity c)
    have hb : wj.angleArity ≤ w.angleArity :=
      (Finset.single_le_sum (fun l _ => Nat.zero_le (w.restrict (c.emb l)).angleArity)
        (Finset.mem_univ j)).trans_eq (w.sum_restrict_angleArity c)
    have hbound := hinputs i wj.stateArity wj.angleArity hk hb u hu
    exact (congrArg norm ((congrArg (fun z => (J i).D (c.partSize j) (x, θ) z)
      hpure.symm).trans he)).trans_le hbound
  exact n04PositiveGeometry_finiteKernel_weighted_bound JT hV hg hmap Q
    n w.stateArity (w.angleArity + shift * w.stateArity) (x, θ) ⟨hx, mem_univ _⟩ v
    κ cost hκ hcost hC hM hH hHL hL ht houter hinner

private theorem pureSlots_fst_property {n : ℕ} (w : StateAngleWord n)
    (P : E → Prop) (hzero : P 0) (v : Fin w.stateArity → E)
    (hv : ∀ j, P (v j)) : ∀ j, P (w.pureSlots v j).1 := by
  induction w with
  | nil => intro j; exact j.elim0
  | state w ih =>
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hv 0
      · exact ih (Fin.tail v) (fun i => hv i.succ) i
  | angle w ih =>
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hzero
      · exact ih v hv i

/-- The same estimate for an arbitrary genuine angular parameter tower.
The two arities are simplified only after the whole direction family
has been quantified, so no parameter tuple is recast or reordered. -/
theorem n04PositiveGeometry_angularKernel_parameter_bound
    (hU : IsOpen U)
    (J : ∀ i, SmoothDirections (U ×ˢ (univ : Set ℝ)) (f i))
    (JA : ∀ i b θ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => f i (x, η)) θ))
    {V : Set (ι → ℝ)} (hV : IsOpen V) {g : (ι → ℝ) → ℝ}
    (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo (fun z i => f i z) (U ×ˢ univ) V)
    (Q : SmoothDirections (U ×ˢ univ) (fun z => g (fun i => f i z)))
    (k b shift : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ)
    (P : E → Prop) (hzero : P 0)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (houter : ∀ j, j ≤ b + k → ‖iteratedFDeriv ℝ j g (fun i => f i (x, θ))‖ ≤ C)
    (hinputs : ∀ i e u, e ≤ k → u ≤ b →
      ∀ v : Fin e → E, (∀ j, P (v j)) →
        ‖(JA i u θ).D e x v‖ ≤ M * parameterHeightWeight H e * t ^ (u + shift * e))
    (Qout : SmoothDirections U
      (fun y => iteratedDeriv b (fun η => g (fun i => f i (y, η))) θ))
    (v : Fin k → E) (hv : ∀ j, P (v j)) :
    ‖Qout.D k x v‖ ≤ (Fintype.card (OrderedFinpartition (b + k)) : ℝ) *
      C * M ^ (b + k) * L ^ (b + k) * parameterHeightWeight H k * t ^ (b + shift * k) := by
  let w := StateAngleWord.stateThenAngle k b
  have hs : ∀ z : Fin w.stateArity → E, (∀ j, P (z j)) →
      ‖(smoothDirections_angularStateSlice Q w.angleArity θ).D w.stateArity x z‖ ≤
        (Fintype.card (OrderedFinpartition (b + k)) : ℝ) *
          C * M ^ (b + k) * L ^ (b + k) * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + shift * w.stateArity) := by
    intro z hz
    rw [← smoothDirections_joint_pureSlots Q
      (fun a η => smoothDirections_angularStateSlice Q a η) w hx θ z]
    apply n04PositiveGeometry_angularKernel_weighted_bound hU J JA hV hg hmap Q
      w shift x hx θ (w.pureSlots z) (w.isPure_pureSlots z) P
      (pureSlots_fst_property w P hzero z hz) hC hM hH hHL hL ht houter
    intro i e u he hu
    exact hinputs i e u
      (by simpa only [w, StateAngleWord.stateThenAngle_stateArity] using he)
      (by simpa only [w, StateAngleWord.stateThenAngle_angleArity] using hu)
  have hwk : w.stateArity = k := StateAngleWord.stateThenAngle_stateArity k b
  have hwb : w.angleArity = b := StateAngleWord.stateThenAngle_angleArity k b
  rw [hwk, hwb] at hs
  have he : Qout.D k x v = (smoothDirections_angularStateSlice Q b θ).D k x v :=
    congrArg (fun A : E [×k]→L[ℝ] ℝ => A v)
      (Qout.unique (smoothDirections_angularStateSlice Q b θ) k x hx)
  exact (congrArg norm he).trans_le (hs v hv)

end ContinuousFlexibility.Analysis
