module

public import ContinuousFlexibility.Radial.OuterPhysicalTailInitialBounds
public import ContinuousFlexibility.Radial.TailFundamentalNodeBounds
public import ContinuousFlexibility.Radial.TailFundamentalStates

/-!
# The uniform node Green bound for the same actual basis

The actual initial-edge estimate starts the diagonal recurrence at
eight over Lambda. Its affine contraction preserves that bound, so
the two-point node estimate has an explicit constant independent of
frequency, transition depth, orientation and height choices.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped BigOperators
open ContinuousFlexibility.Statements

/-- The public node recurrence gives an explicit bound when its actual
initial diagonal product is at most eight over Lambda. -/
theorem outer_tail_node_green_bound_of_initial {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {P ZP Q ZQ : ℝ → ℝ}
    (hP : TailFirstOrderSystem T.p T.Λ P ZP (Ico T.entrance T.endpoint))
    (hQ : TailFirstOrderSystem T.p T.Λ Q ZQ (Ico T.entrance T.endpoint))
    (hW : ∀ x ∈ Ico T.entrance T.endpoint, ZQ x * P x - Q x * ZP x = 1)
    (hPnode : ∀ n, P (T.node n) ≠ 0)
    (hstep : ∀ n, |P (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |P (T.node n)|)
    (hinit : tailMass T 0 * |P (T.node 0) * Q (T.node 0)| ≤ 8 / T.Λ) :
    ∀ m n, m ≤ n →
      |Q (T.node m) * P (T.node n)| ≤ ((8 / T.Λ) / tailMass T m) *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  have hsub : Ico (T.node 0) T.endpoint ⊆ Ico T.entrance T.endpoint :=
    fun _ hx => ⟨hT.2.1.trans hx.1, hx.2⟩
  have hPc : ContinuousOn P (Ico T.entrance T.endpoint) :=
    HasDerivAt.continuousOn (fun x hx => (hP x hx).1)
  have hZPc : ContinuousOn ZP (Ico T.entrance T.endpoint) :=
    HasDerivAt.continuousOn (fun x hx => (hP x hx).2)
  have hrec := tailActualSolution_node_recurrence hT
    (hPc.mono hsub) (hZPc.mono hsub) (hP.mono (Ioo_subset_Ico_self.trans hsub))
  have hcross := tailActualState_discrete_wronskian hT hP hQ hW
  have hdiagStep (n : ℕ) :
      tailMass T (n + 1) * |P (T.node (n + 1)) * Q (T.node (n + 1))| ≤
        tailMass T n * |P (T.node n) * Q (T.node n)| / 4 + 4 / T.Λ :=
    tailNode_green_diagonal_step (tailMass_pos hT n).le (tailMass_pos hT (n + 1)).le
      (hPnode n) (tailActualNodeCoupling_pos hT n).ne' (hcross n)
      (tailNaturalNode_weighted_ratio_sq hT hK hPnode hstep n)
      (tailNaturalNode_backward_ratio hT hη hK hPnode hrec hstep n)
  have hdiag (n : ℕ) :
      tailMass T n * |P (T.node n) * Q (T.node n)| ≤ 8 / T.Λ := by
    induction n with
    | zero => exact hinit
    | succ n ih =>
      have h := hdiagStep n
      have hpos : 0 ≤ 4 / T.Λ := div_nonneg (by norm_num) hT.2.2.1.le
      have heq : 8 / T.Λ = 2 * (4 / T.Λ) := by ring
      linarith only [h, ih, hpos, heq]
  intro m n hmn
  have hprod := tailNode_ratio_le_prod (fun k => abs_pos.mpr (hPnode k))
    (fun k => div_nonneg (by norm_num)
      (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (k + 1)))
        (tailResistance_pos hT k)).le)
    hstep hmn
  have hdm : |Q (T.node m) * P (T.node m)| ≤ (8 / T.Λ) / tailMass T m := by
    apply (le_div_iff₀ (tailMass_pos hT m)).mpr
    simpa only [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hdiag m
  have heq : |Q (T.node m) * P (T.node n)| =
      |Q (T.node m) * P (T.node m)| *
        (|P (T.node n)| / |P (T.node m)|) := by
    rw [abs_mul, abs_mul]
    field_simp [(abs_pos.mpr (hPnode m)).ne']
  rw [heq]
  exact mul_le_mul hdm hprod
    (div_nonneg (abs_nonneg _) (abs_nonneg _))
    (div_nonneg (div_nonneg (by norm_num) hT.2.2.1.le) (tailMass_pos hT m).le)

/-- The same constructed logarithmic pair has B = 8 / Lambda in the
fundamental Green-node estimate. No additional node estimate is assumed. -/
theorem MorsePhysicalTailBasis.log_node_green_bound
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K : ℝ}
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    ∀ m n, m ≤ n →
      |F.logQ (T.node m) * F.logP (T.node n)| ≤ ((8 / T.Λ) / tailMass T m) *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) :=
  outer_tail_node_green_bound_of_initial hT hη hK F.P_log_system F.Q_log_system
    F.log_wronskian F.P_node_ne F.P_node_step (F.log_initial_product_bound hT)

end ContinuousFlexibility.Radial

