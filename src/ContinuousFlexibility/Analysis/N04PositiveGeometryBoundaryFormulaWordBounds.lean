import ContinuousFlexibility.Analysis.N04PositiveGeometryFiniteKernelBounds
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFiniteCalculus
import ContinuousFlexibility.Analysis.N01cAngularJetTowers
import ContinuousFlexibility.Analysis.N01cStateAngleSelections
import ContinuousFlexibility.Analysis.FlowJetLinearization
import ContinuousFlexibility.Analysis.SmoothDirectionsFixedLast
import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition

/-!
# A finite angular reserve for the actual boundary formulas

The reserve is spent only on the finitely many derivatives already in
the boundary recursion. Product partitions distribute every remaining
angular order exactly once and retain the original parameter arity.
The constants below precede every function and every material value.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_sum_sub_reserve_le
    {ι : Type*} (s : Finset ι) (a : ι → ℕ) (d : ℕ) :
    (∑ i ∈ s, (a i - d)) ≤ (∑ i ∈ s, a i) - d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Nat.zero_sub, le_refl]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        (a i - d) + (∑ j ∈ s, (a j - d)) ≤
            (a i - d) + ((∑ j ∈ s, a j) - d) := Nat.add_le_add_left ih _
        _ ≤ (a i + ∑ j ∈ s, a j) - d := by omega

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E}

section NormedBounds

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f g : E × ℝ → F}

/-- Bounds for actual ordered pure slots, with a finite intrinsic
angular reserve. They include the true zeroth value. -/
def N04BoundaryWordBounds
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (K s d : ℕ) (x : E) (θ : ℝ) (P : E → Prop)
    (M H t : ℝ) (shift : ℕ) : Prop :=
  ∀ n : ℕ, ∀ w : StateAngleWord n,
    w.stateArity ≤ K → w.angleArity ≤ s + d →
    ∀ v : Fin n → E × ℝ, w.IsPure v → (∀ i, P (v i).1) →
      ‖J.D n (x, θ) v‖ ≤ M * parameterHeightWeight H w.stateArity *
        t ^ ((w.angleArity - d) + shift * w.stateArity)

namespace N04BoundaryWordBounds

variable {J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f}
  {Q : SmoothDirections (U ×ˢ (univ : Set ℝ)) g}
  {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop}
  {M M' H t : ℝ} {shift : ℕ}

theorem enlarge (h : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hH : 0 ≤ H) (ht : 0 ≤ t) (hMM : M ≤ M') :
    N04BoundaryWordBounds J K s d x θ P M' H t shift := by
  intro n w hk ha v hv hp
  exact (h n w hk ha v hv hp).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMM (parameterHeightWeight_nonneg hH _))
      (pow_nonneg ht _))

theorem reserve (h : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t) {d' : ℕ} (hdd : d' ≤ d) :
    N04BoundaryWordBounds J K s d' x θ P M H t shift := by
  intro n w hk ha v hv hp
  exact (h n w hk (by omega) v hv hp).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega))
      (mul_nonneg hM (parameterHeightWeight_nonneg hH _)))

theorem congr (h : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hx : x ∈ U) (he : ∀ z ∈ U ×ˢ (univ : Set ℝ), f z = g z) :
    N04BoundaryWordBounds Q K s d x θ P M H t shift := by
  intro n w hk ha v hv hp
  have hq := (J.congr he).unique Q n (x, θ) ⟨hx, mem_univ _⟩
  exact (congrArg norm (congrArg (fun A : (E × ℝ) [×n]→L[ℝ] F => A v)
    hq.symm)).trans_le (h n w hk ha v hv hp)

theorem add (hf : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hg : N04BoundaryWordBounds Q K s d x θ P M' H t shift) :
    N04BoundaryWordBounds (smoothDirectionsAdd J Q) K s d x θ P
      (M + M') H t shift := by
  intro n w hk ha v hv hp
  change ‖J.D n (x, θ) v + Q.D n (x, θ) v‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add
    (hf n w hk ha v hv hp) (hg n w hk ha v hv hp)).trans_eq (by ring))

end N04BoundaryWordBounds

end NormedBounds

section ScalarBounds

variable {f g : E × ℝ → ℝ}

namespace N04BoundaryWordBounds

variable {J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f}
  {Q : SmoothDirections (U ×ˢ (univ : Set ℝ)) g}
  {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop}
  {M M' H t : ℝ} {shift : ℕ}

theorem scale (hf : N04BoundaryWordBounds J K s d x θ P M H t shift) (a : ℝ) :
    N04BoundaryWordBounds
      (smoothDirections_postcompCLM J (a • ContinuousLinearMap.id ℝ ℝ))
      K s d x θ P (|a| * M) H t shift := by
  intro n w hk ha v hv hp
  rw [smoothDirections_postcompCLM_D_apply]
  change ‖a * J.D n (x, θ) v‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf n w hk ha v hv hp) (abs_nonneg a)).trans_eq
    (by ring)

/-- One actual angular differentiation uses one reserved order. -/
theorem angular (h : N04BoundaryWordBounds J K s (d + 1) x θ P M H t shift)
    (hx : x ∈ U) (hU : Convex ℝ U) (hP : P 0) :
    N04BoundaryWordBounds (smoothDirections_angularIterate J 1)
      K s d x θ P M H t shift := by
  intro n w hk ha v hv hp
  have hpure : (StateAngleWord.angle w).IsPure (Fin.cons (0, 1) v) := by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [StateAngleWord.isState, Fin.cons_zero, Bool.false_eq_true,
          false_implies]
      · exact hv.1 j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro _
        rfl
      · exact hv.2 j
  have hdirs : ∀ i, P (Fin.cons (α := fun _ => E × ℝ) (0, 1) v i).1 :=
    Fin.cases hP hp
  have hb := h (n + 1) (.angle w) hk (by
    change w.angleArity + 1 ≤ s + (d + 1)
    omega) (Fin.cons (0, 1) v) hpure hdirs
  have he : (smoothDirections_angularIterate J 1).D n (x, θ) v =
      J.D (n + 1) (x, θ) (Fin.cons (0, 1) v) := by
    change J.D (n + 1) (x, θ) (Fin.snoc v (0, 1)) = _
    exact (J.cons_eq_snoc (hU.prod convex_univ) n (x, θ)
      ⟨hx, mem_univ _⟩ (0, 1) v).symm
  rw [he]
  simpa only [StateAngleWord.stateArity, StateAngleWord.angleArity,
    Nat.add_sub_add_right] using hb

end N04BoundaryWordBounds

private theorem boundary_mul_outer_prefix
    (N : ℕ) {M : ℝ} (hM : 1 ≤ M) (z : ℝ × ℝ)
    (h₁ : ‖z.1‖ ≤ M) (h₂ : ‖z.2‖ ≤ M) (k : ℕ) (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × ℝ => y.1 * y.2) z‖ ≤
      (2 : ℝ) ^ N * M ^ 2 := by
  have hcoord (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
      (hz : ‖L z‖ ≤ M) (j : ℕ) : ‖iteratedFDeriv ℝ j L z‖ ≤ M := by
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hz
    | succ j =>
        exact (flowJet_norm_iteratedFDeriv_clm_le L (Nat.succ_pos j) z).trans
          (hL.trans hM)
  exact n04PositiveGeometry_product_prefix_bound (zero_le_one.trans hM)
    contDiff_fst.contDiffAt contDiff_snd.contDiffAt
    (fun j _ => hcoord (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) h₁ j)
    (fun j _ => hcoord (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) h₂ j) hk

/-- Multiplication keeps the complete angular reserve. Its cost is a
fixed polynomial in the common material bound. -/
theorem n04PositiveGeometry_boundaryWord_mul (N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U : Set E} {f g : E × ℝ → ℝ},
      ∀ J : SmoothDirections (U ×ˢ univ) f,
      ∀ Q : SmoothDirections (U ×ˢ univ) g,
      ∀ K s d, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift,
      N04BoundaryWordBounds J K s d x θ P M H t shift →
      N04BoundaryWordBounds Q K s d x θ P M H t shift →
      N04BoundaryWordBounds (J.mul Q) K s d x θ P
        (C * M ^ (N + 2)) H t shift := by
  classical
  let A : ℝ := 1 + ∑ j ∈ Finset.range (N + 1),
    (Fintype.card (OrderedFinpartition j) : ℝ)
  have hA : 1 ≤ A := le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  let C : ℝ := A * (2 : ℝ) ^ N * L ^ N
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by norm_num)))
    (one_le_pow₀ hL)
  refine ⟨C, hC, ?_⟩
  intro U f g J Q K s d hN x hx θ P M H t hM hH hHL ht shift hf hg
  have hvalue (F : E × ℝ → ℝ) (JF : SmoothDirections (U ×ˢ univ) F)
      (hF : N04BoundaryWordBounds JF K s d x θ P M H t shift) :
      ‖F (x, θ)‖ ≤ M := by
    have hb := hF 0 .nil (Nat.zero_le _) (Nat.zero_le _) Fin.elim0
      ⟨fun i => i.elim0, fun i => i.elim0⟩ (fun i => i.elim0)
    simpa only [JF.zero (x, θ) ⟨hx, mem_univ _⟩,
      StateAngleWord.stateArity, StateAngleWord.angleArity, Nat.zero_sub,
      Nat.mul_zero, Nat.add_zero, parameterHeightWeight, ite_true, pow_zero,
      mul_one] using hb
  intro n w hk ha v hv hp
  have hn : n ≤ N := by have hs := w.arity_sum; omega
  let JT := smoothDirectionsProd J Q
  let κ : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
    fun c i => (w.restrict (c.emb i)).stateArity
  let cost : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
    fun c i => ((w.restrict (c.emb i)).angleArity - d) + shift * κ c i
  have hcost (c : OrderedFinpartition n) :
      ∑ i, cost c i ≤ (w.angleArity - d) + shift * w.stateArity := by
    dsimp only [cost, κ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, w.sum_restrict_stateArity c]
    have hs := n04PositiveGeometry_sum_sub_reserve_le Finset.univ
      (fun i => (w.restrict (c.emb i)).angleArity) d
    rw [w.sum_restrict_angleArity c] at hs
    exact Nat.add_le_add_right hs _
  have hinner (c : OrderedFinpartition n) (i : Fin c.length) :
      ‖JT.D (c.partSize i) (x, θ) (v ∘ c.emb i)‖ ≤
        M * parameterHeightWeight H (κ c i) * t ^ cost c i := by
    have hk' : (w.restrict (c.emb i)).stateArity ≤ K :=
      ((Finset.single_le_sum
        (fun j _ => Nat.zero_le (w.restrict (c.emb j)).stateArity)
        (Finset.mem_univ i)).trans_eq (w.sum_restrict_stateArity c)).trans hk
    have ha' : (w.restrict (c.emb i)).angleArity ≤ s + d :=
      ((Finset.single_le_sum
        (fun j _ => Nat.zero_le (w.restrict (c.emb j)).angleArity)
        (Finset.mem_univ i)).trans_eq (w.sum_restrict_angleArity c)).trans ha
    change max ‖J.D (c.partSize i) (x, θ) (v ∘ c.emb i)‖
      ‖Q.D (c.partSize i) (x, θ) (v ∘ c.emb i)‖ ≤ _
    exact max_le (hf _ _ hk' ha' _ (hv.restrict _) (fun j => hp _))
      (hg _ _ hk' ha' _ (hv.restrict _) (fun j => hp _))
  have hb := n04PositiveGeometry_finiteKernel_weighted_bound JT isOpen_univ
    (contDiff_fst.mul contDiff_snd).contDiffOn (fun _ _ => mem_univ _)
    (J.mul Q) n w.stateArity ((w.angleArity - d) + shift * w.stateArity)
    (x, θ) ⟨hx, mem_univ _⟩ v κ cost (fun c => w.sum_restrict_stateArity c)
    hcost (by positivity : 0 ≤ (2 : ℝ) ^ N * M ^ 2) hM hH hHL hL ht
    (fun j hj => boundary_mul_outer_prefix N hM (f (x, θ), g (x, θ))
      (hvalue f J hf) (hvalue g Q hg) j (hj.trans hn)) hinner
  have hc : (Fintype.card (OrderedFinpartition n) : ℝ) ≤ A :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg
      (Fintype.card (OrderedFinpartition j)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hmat : (Fintype.card (OrderedFinpartition n) : ℝ) *
      ((2 : ℝ) ^ N * M ^ 2) * M ^ n * L ^ n ≤ C * M ^ (N + 2) := by
    calc
      _ = ((Fintype.card (OrderedFinpartition n) : ℝ) * (2 : ℝ) ^ N * L ^ n) *
          M ^ (n + 2) := by rw [pow_add]; ring
      _ ≤ (A * (2 : ℝ) ^ N * L ^ N) * M ^ (N + 2) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity))
          (pow_le_pow_right₀ hL hn) (by positivity)
          (mul_nonneg (zero_le_one.trans hA) (by positivity)))
          (pow_le_pow_right₀ hM (by omega)) (by positivity)
          (zero_le_one.trans hC)
      _ = _ := rfl
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmat (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _))

end ScalarBounds

end ContinuousFlexibility.Analysis
