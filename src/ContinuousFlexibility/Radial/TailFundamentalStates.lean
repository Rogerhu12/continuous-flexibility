import ContinuousFlexibility.Radial.TailNaturalInitialExtension
import ContinuousFlexibility.Radial.TailActualSolutionNodes

/-!
# A Dirichlet left state paired with the natural state

The forward node recurrence constructs an independent actual solution.
Subtracting the appropriate multiple of the natural solution sets its
entrance value to zero. The two states have Wronskian one throughout the
tail, which fixes the normalization of the Green kernel.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- Conservation of the actual physical Wronskian is the discrete
Casoratian identity for the same canonical edge coefficients. -/
theorem tailActualState_discrete_wronskian {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u v w z : ℝ → ℝ}
    (h : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (h' : TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint))
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, z x * u x - w x * v x = 1) (n : ℕ) :
    tailActualNodeCoupling T hT n *
      (u (T.node n) * w (T.node (n + 1)) - u (T.node (n + 1)) * w (T.node n)) = 1 := by
  have hs := tailActualEdge_interval_subset hT n
  have hf := (tailActualEdge_solution_flux_endpoints hT n
    (HasDerivAt.continuousOn (fun x hx => (h x (hs hx)).1))
    (HasDerivAt.continuousOn (fun x hx => (h x (hs hx)).2))
    (h.mono (Ioo_subset_Icc_self.trans hs))).1
  have hg := (tailActualEdge_solution_flux_endpoints hT n
    (HasDerivAt.continuousOn (fun x hx => (h' x (hs hx)).1))
    (HasDerivAt.continuousOn (fun x hx => (h' x (hs hx)).2))
    (h'.mono (Ioo_subset_Icc_self.trans hs))).1
  have hnode := hW (T.node n) ⟨deepTail_entrance_le_node hT n, deepTail_node_lt_endpoint hT n⟩
  rw [hf, hg] at hnode
  nlinarith only [hnode]

def tailForwardNodes (b c : ℕ → ℝ) (A B : ℝ) : ℕ → ℝ
  | 0 => A
  | 1 => B
  | n + 2 => (-b n * tailForwardNodes b c A B (n + 1) -
      c n * tailForwardNodes b c A B n) / c (n + 1)

theorem tailForwardNodes_recurrence {b c : ℕ → ℝ} (hc : ∀ n, c n ≠ 0)
    (A B : ℝ) (n : ℕ) :
    -b n * tailForwardNodes b c A B (n + 1) =
      c n * tailForwardNodes b c A B n + c (n + 1) * tailForwardNodes b c A B (n + 2) := by
  rw [tailForwardNodes]
  field_simp [hc (n + 1)]
  ring

theorem tailFirstOrderSystem_wronskian_const_Ico
    {p u v U V : ℝ → ℝ} {Λ a b : ℝ}
    (hu : ContinuousOn u (Ico a b)) (hv : ContinuousOn v (Ico a b))
    (hU : ContinuousOn U (Ico a b)) (hV : ContinuousOn V (Ico a b))
    (h : TailFirstOrderSystem p Λ u v (Ico a b))
    (h' : TailFirstOrderSystem p Λ U V (Ico a b))
    {x y : ℝ} (hx : x ∈ Ico a b) (hy : y ∈ Ico a b) :
    tailFirstOrderWronskian u v U V x = tailFirstOrderWronskian u v U V y := by
  have hs : Icc a (max x y) ⊆ Ico a b :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt (max_lt hx.2 hy.2)⟩
  have hxs : x ∈ Icc a (max x y) := ⟨hx.1, le_max_left _ _⟩
  have hys : y ∈ Icc a (max x y) := ⟨hy.1, le_max_right _ _⟩
  have hc (t : ℝ) (ht : t ∈ Icc a (max x y)) :=
    tailFirstOrderSystem_wronskian_const_Icc
      (hu.mono hs) (hv.mono hs) (hU.mono hs) (hV.mono hs)
      (h.mono (Ioo_subset_Icc_self.trans hs)) (h'.mono (Ioo_subset_Icc_self.trans hs)) ht
  exact (hc x hxs).trans (hc y hys).symm

theorem exists_tailDirichletLeftState {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u v : ℝ → ℝ} (hu : ContDiffOn ℝ ∞ u (Iio T.endpoint))
    (hv : ContDiffOn ℝ ∞ v (Iio T.endpoint))
    (h : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1) (hua : u T.entrance ≠ 0) :
    ∃ w z : ℝ → ℝ,
      ContDiffOn ℝ ∞ w (Iio T.endpoint) ∧ ContDiffOn ℝ ∞ z (Iio T.endpoint) ∧
      TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint) ∧
      w T.entrance = 0 ∧
      ∀ x ∈ Ico T.entrance T.endpoint, z x * u x - w x * v x = 1 := by
  let a : ℕ → ℝ := tailForwardNodes (tailActualInteriorDiagonal T hT)
    (tailActualNodeCoupling T hT) 0 (tailActualNodeCoupling T hT 0)⁻¹
  have ha₀ : a 0 = 0 := rfl
  have ha₁ : a 1 = (tailActualNodeCoupling T hT 0)⁻¹ := rfl
  have hrec (n : ℕ) : -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2) :=
    tailForwardNodes_recurrence (fun n => (tailActualNodeCoupling_pos hT n).ne') _ _ n
  obtain ⟨U, V, hU, hV, h', hUeq, hVeq⟩ := exists_tailSmoothNaturalState hT hrec
  have hnode : T.node 0 ∈ Ico T.entrance T.endpoint :=
    ⟨hT.2.1, deepTail_node_lt_endpoint hT 0⟩
  have hnode' : T.node 0 ∈ Ico (T.node 0) T.endpoint :=
    ⟨le_rfl, deepTail_node_lt_endpoint hT 0⟩
  have hU₀ : U (T.node 0) = 0 := by
    rw [hUeq hnode', tailPoissonInterpolation_node, ha₀]
  have hV₀ : V (T.node 0) = 1 := by
    rw [hVeq hnode', tailPoissonInterpolationFlux_first_node, ha₀, ha₁,
      mul_zero, zero_add, mul_inv_cancel₀ (tailActualNodeCoupling_pos hT 0).ne']
  have hW (x : ℝ) (hx : x ∈ Ico T.entrance T.endpoint) :
      tailFirstOrderWronskian u v U V x = 1 := by
    have heq := tailFirstOrderSystem_wronskian_const_Ico
      (hu.continuousOn.mono (fun _ ht => ht.2))
      (hv.continuousOn.mono (fun _ ht => ht.2))
      (hU.continuousOn.mono (fun _ ht => ht.2))
      (hV.continuousOn.mono (fun _ ht => ht.2)) h h' hx hnode
    simpa only [tailFirstOrderWronskian, hu₀, hU₀, hV₀, mul_one, mul_zero, sub_zero] using heq
  let k : ℝ := U T.entrance / u T.entrance
  let w : ℝ → ℝ := fun x => U x - k * u x
  let z : ℝ → ℝ := fun x => V x - k * v x
  have hw : ContDiffOn ℝ ∞ w (Iio T.endpoint) := hU.sub (contDiffOn_const.mul hu)
  have hz : ContDiffOn ℝ ∞ z (Iio T.endpoint) := hV.sub (contDiffOn_const.mul hv)
  have hsys : TailFirstOrderSystem T.p T.Λ w z (Ico T.entrance T.endpoint) := by
    intro x hx
    constructor
    · exact (((h' x hx).1).fun_sub (((h x hx).1).const_mul k)).congr_deriv (by
        dsimp only [z]; ring)
    · exact (((h' x hx).2).fun_sub (((h x hx).2).const_mul k)).congr_deriv (by
        dsimp only [w]; ring)
  refine ⟨w, z, hw, hz, hsys, ?_, ?_⟩
  · dsimp only [w, k]
    field_simp [hua] <;> ring
  · intro x hx
    have heq := hW x hx
    dsimp only [tailFirstOrderWronskian] at heq
    dsimp only [w, z]
    nlinarith only [heq]

end ContinuousFlexibility.Radial
