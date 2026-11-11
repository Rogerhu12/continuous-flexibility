import ContinuousFlexibility.Analysis.ProjectiveCurveIteratedChain
import ContinuousFlexibility.Analysis.ProjectiveParameterDerivativeDecay
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Parameter derivative growth of the fixed Newton iteration

The geometric increase of the smoothing index absorbs the linear
recurrence for the highest parameter derivative at each order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter Set
open scoped BigOperators Topology Uniformity

set_option backward.isDefEq.respectTransparency false

/-- At a fixed grade an affine one-step bound gives a single exponential
bound on the entire sequence, uniformly in the parameter. -/
theorem newtonParameterGrowth_of_affine_recurrence
    {I : Set ℝ} {N₀ : ℕ} (hN₀ : 0 < N₀) (a : ℕ → ℝ → ℝ)
    {B C γ : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (ha : ∀ n t, t ∈ I → 0 ≤ a n t)
    (hinit : ∀ t ∈ I, a 0 t ≤ B)
    (hstep : ∀ n t, t ∈ I →
      a (n + 1) t ≤ a n t + C * Real.exp (γ * (newtonSmoothingIndex N₀ n : ℝ)) *
        (1 + a n t)) :
    ∀ n t, t ∈ I →
      1 + a n t ≤ (1 + B) * Real.exp (2 * (C + γ) * (newtonSmoothingIndex N₀ n : ℝ)) := by
  let N := newtonSmoothingIndex N₀
  let κ : ℝ := 2 * (C + γ)
  have hκ : 0 ≤ κ := mul_nonneg (by norm_num) (add_nonneg hC hγ)
  intro n t ht
  change 1 + a n t ≤ (1 + B) * Real.exp (κ * (N n : ℝ))
  induction n with
  | zero =>
    have hE : 1 ≤ Real.exp (κ * (N 0 : ℝ)) :=
      Real.one_le_exp (mul_nonneg hκ (Nat.cast_nonneg _))
    calc
      1 + a 0 t ≤ 1 + B := add_le_add_left (hinit t ht) _
      _ = (1 + B) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)
  | succ n ih =>
    have hN : (1 : ℝ) ≤ N n := by
      exact_mod_cast (show 1 ≤ N n from (by omega : 1 ≤ N₀ + n).trans
        (newtonSmoothingIndex_ge_add hN₀ n))
    have hExp : 1 ≤ Real.exp (γ * (N n : ℝ)) :=
      Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg _))
    have hcoef : 1 + C * Real.exp (γ * (N n : ℝ)) ≤ Real.exp ((C + γ) * (N n : ℝ)) := by
      calc
        _ ≤ (1 + C) * Real.exp (γ * (N n : ℝ)) := by nlinarith only [hExp]
        _ ≤ Real.exp C * Real.exp (γ * (N n : ℝ)) :=
          mul_le_mul_of_nonneg_right (by simpa only [add_comm C 1] using Real.add_one_le_exp C)
            (Real.exp_pos _).le
        _ = Real.exp (C + γ * (N n : ℝ)) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hN hC])
    have hscale : (3 / 2 : ℝ) * N n ≤ N (n + 1) :=
      (newtonSmoothingIndex_succ_bounds N₀ n).1
    have hpower : κ * (N n : ℝ) + (C + γ) * (N n : ℝ) ≤ κ * (N (n + 1) : ℝ) := by
      calc
        _ = κ * ((3 / 2 : ℝ) * N n) := by dsimp only [κ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale hκ
    calc
      1 + a (n + 1) t ≤ (1 + a n t) * (1 + C * Real.exp (γ * (N n : ℝ))) := by
        calc
          _ ≤ 1 + (a n t + C * Real.exp (γ * (N n : ℝ)) * (1 + a n t)) :=
            add_le_add_left (hstep n t ht) _
          _ = _ := by ring
      _ ≤ (1 + a n t) * Real.exp ((C + γ) * (N n : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoef (by linarith only [ha n t ht])
      _ ≤ ((1 + B) * Real.exp (κ * (N n : ℝ))) * Real.exp ((C + γ) * (N n : ℝ)) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = (1 + B) * Real.exp (κ * (N n : ℝ) + (C + γ) * (N n : ℝ)) := by
        rw [Real.exp_add, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpower) (by positivity)

section JetBounds

variable {Z W : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
  {p : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ W}
  {U : Set Z} {g : Z → W}

private abbrev HasLocalJetTameBounds (p : ℕ → Seminorm ℝ Z) (q : ℕ → Seminorm ℝ W)
    (J : Statements.SmoothDirections U g) : Prop :=
  ∀ k z₀, z₀ ∈ U →
    ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U,
        p base (z - z₀) < ε → ∀ v : Fin k → Z,
        q s (J.D k z v) ≤ C *
          ((1 + p (s + loss) z) * ∏ i, p base (v i) +
            ∑ i : Fin k, p (s + loss) (v i) * ∏ l ∈ Finset.univ.erase i, p base (v l))

/-- At a fixed output grade, a local tame bound gives a product bound
using a single input grade for every direction. -/
private theorem exists_local_jet_product_bound
    (hp : Monotone p) (hq : Monotone q) (hpc : ∀ s, Continuous (p s))
    (J : Statements.SmoothDirections U g) (k s : ℕ) (z₀ : Z)
    (hlocal : ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ j : ℕ, base ≤ j → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U,
        p base (z - z₀) < ε → ∀ v : Fin k → Z,
        q j (J.D k z v) ≤ C *
          ((1 + p (j + loss) z) * ∏ i, p base (v i) +
            ∑ i : Fin k, p (j + loss) (v i) * ∏ l ∈ Finset.univ.erase i, p base (v l))) :
    ∃ O ∈ 𝓝 z₀, ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U, z ∈ O →
      ∀ v : Fin k → Z, q s (J.D k z v) ≤ C * ∏ i, p d (v i) := by
  obtain ⟨loss, b, ε, hε, H⟩ := hlocal
  let j := max s b
  let d := max b (j + loss)
  let O := {z : Z | p d (z - z₀) < min ε 1}
  obtain ⟨C, hC, hbound⟩ := H j (le_max_right s b)
  have hbd : b ≤ d := le_max_left _ _
  have hjd : j + loss ≤ d := le_max_right _ _
  have hO : O ∈ 𝓝 z₀ := by
    apply IsOpen.mem_nhds (isOpen_lt ((hpc d).comp (continuous_id.sub continuous_const))
      continuous_const)
    change p d (z₀ - z₀) < min ε 1
    rw [sub_self, map_zero]
    exact lt_min hε zero_lt_one
  have hcoef : 0 ≤ C * (2 + p d z₀ + k) :=
    mul_nonneg hC (by linarith only [apply_nonneg (p d) z₀, Nat.cast_nonneg (α := ℝ) k])
  refine ⟨O, hO, d, C * (2 + p d z₀ + k), hcoef, ?_⟩
  intro z hz hzO v
  change p d (z - z₀) < min ε 1 at hzO
  have hnear : p b (z - z₀) < ε :=
    (hp hbd _).trans_lt (hzO.trans_le (min_le_left _ _))
  have hstate : p (j + loss) z ≤ p d z₀ + 1 := by
    calc
      _ ≤ p d z := hp hjd z
      _ = p d ((z - z₀) + z₀) := by rw [sub_add_cancel]
      _ ≤ p d (z - z₀) + p d z₀ := map_add_le_add (p d) _ _
      _ ≤ _ := by linarith only [hzO.trans_le (min_le_right _ _)]
  let P := ∏ i, p d (v i)
  have hprod : (∏ i, p b (v i)) ≤ P :=
    Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun _ _ => hp hbd _)
  have hsplit (i : Fin k) :
      p (j + loss) (v i) * (∏ l ∈ Finset.univ.erase i, p b (v l)) ≤ P := by
    calc
      _ ≤ p d (v i) * (∏ l ∈ Finset.univ.erase i, p d (v l)) :=
        mul_le_mul (hp hjd _) (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
          (fun _ _ => hp hbd _)) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
          (apply_nonneg _ _)
      _ = P := by
        rw [mul_comm]
        exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hsum : (∑ i : Fin k, p (j + loss) (v i) *
      ∏ l ∈ Finset.univ.erase i, p b (v l)) ≤ (k : ℝ) * P := by
    calc
      _ ≤ ∑ _ : Fin k, P := Finset.sum_le_sum (fun i _ => hsplit i)
      _ = _ := by simp
  have hmain : (1 + p (j + loss) z) * (∏ i, p b (v i)) ≤ (2 + p d z₀) * P :=
    mul_le_mul (by linarith only [hstate]) hprod
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
      (by linarith only [apply_nonneg (p d) z₀])
  calc
    q s (J.D k z v) ≤ q j (J.D k z v) := hq (le_max_left _ _) _
    _ ≤ _ := hbound z hz hnear v
    _ ≤ C * ((2 + p d z₀) * P + (k : ℝ) * P) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain hsum) hC
    _ = (C * (2 + p d z₀ + k)) * P := by ring

/-- On a compact subset of the domain the input grade and constant can
be chosen independently of the point. -/
private theorem exists_compact_jet_product_bound
    (hp : Monotone p) (hq : Monotone q) (hpc : ∀ s, Continuous (p s))
    (J : Statements.SmoothDirections U g) (k s : ℕ) {K : Set Z}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hlocal : ∀ z₀ ∈ K, ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ j : ℕ, base ≤ j → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U,
        p base (z - z₀) < ε → ∀ v : Fin k → Z,
        q j (J.D k z v) ≤ C *
          ((1 + p (j + loss) z) * ∏ i, p base (v i) +
            ∑ i : Fin k, p (j + loss) (v i) * ∏ l ∈ Finset.univ.erase i, p base (v l))) :
    ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
      ∀ v : Fin k → Z, q s (J.D k z v) ≤ C * ∏ i, p d (v i) := by
  classical
  choose O hO d C hC H using fun z (hz : z ∈ K) =>
    exists_local_jet_product_bound hp hq hpc J k s z (hlocal z hz)
  obtain ⟨T, hT⟩ := hK.elim_nhds_subcover' O hO
  let D := T.sup (fun z => d z z.2)
  let M := ∑ z ∈ T, C z z.2
  refine ⟨D, M, Finset.sum_nonneg (fun z _ => hC z z.2), ?_⟩
  intro z hz v
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp (hT hz)
  obtain ⟨hwT, hzw⟩ := Set.mem_iUnion.mp hw
  have hd : d w w.2 ≤ D := Finset.le_sup hwT
  have hm : C w w.2 ≤ M := Finset.single_le_sum (fun x _ => hC x x.2) hwT
  exact (H w w.2 z (hKU hz) hzw v).trans
    (mul_le_mul hm (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
      (fun _ _ => hp hd _)) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
      (Finset.sum_nonneg (fun x _ => hC x x.2)))

private theorem exists_compact_jet_product_bounds_through
    (hp : Monotone p) (hq : Monotone q) (hpc : ∀ s, Continuous (p s))
    (J : Statements.SmoothDirections U g) (hJ : HasLocalJetTameBounds p q J)
    (m s : ℕ) {K : Set Z} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k ≤ m → ∀ z ∈ K,
      ∀ v : Fin k → Z, q s (J.D k z v) ≤ C * ∏ i, p d (v i) := by
  classical
  choose d C hC H using fun k : Fin (m + 1) =>
    exists_compact_jet_product_bound hp hq hpc J k.1 s hK hKU
      (fun z hz => hJ k.1 z (hKU hz))
  let D := Finset.univ.sup d
  let M := ∑ k, C k
  have hM : 0 ≤ M := Finset.sum_nonneg (fun k _ => hC k)
  refine ⟨D, M, hM, ?_⟩
  intro k hk z hz v
  let i : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hd : d i ≤ D := Finset.le_sup (Finset.mem_univ i)
  have hCi : C i ≤ M := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  exact (H i z hz v).trans (mul_le_mul hCi
    (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun _ _ => hp hd _))
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) hM)

end JetBounds

private abbrev HasNewtonExponentialBound
    (N : ℕ → ℕ) (I : Set ℝ) (u : ℕ → ℝ → ℝ) : Prop :=
  ∃ A γ : ℝ, 0 ≤ A ∧ 0 ≤ γ ∧ ∀ n t, t ∈ I →
    u n t ≤ A * Real.exp (γ * (N n : ℝ))

private theorem hasNewtonExponentialBound_add
    {N : ℕ → ℕ} {I : Set ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : HasNewtonExponentialBound N I u) (hv : HasNewtonExponentialBound N I v) :
    HasNewtonExponentialBound N I (fun n t => u n t + v n t) := by
  obtain ⟨A, α, hA, hα, hu⟩ := hu
  obtain ⟨B, β, hB, hβ, hv⟩ := hv
  refine ⟨A + B, α + β, add_nonneg hA hB, add_nonneg hα hβ, ?_⟩
  intro n t ht
  have hN : 0 ≤ (N n : ℝ) := Nat.cast_nonneg _
  have ha : Real.exp (α * (N n : ℝ)) ≤ Real.exp ((α + β) * (N n : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hβ) hN)
  have hb : Real.exp (β * (N n : ℝ)) ≤ Real.exp ((α + β) * (N n : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hα) hN)
  rw [add_mul]
  exact add_le_add ((hu n t ht).trans (mul_le_mul_of_nonneg_left ha hA))
    ((hv n t ht).trans (mul_le_mul_of_nonneg_left hb hB))

private theorem hasNewtonExponentialBound_of_affine
    {N : ℕ → ℕ} {I : Set ℝ} {u v : ℕ → ℝ → ℝ}
    {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (huv : ∀ n t, t ∈ I → u n t ≤ C * Real.exp (γ * (N n : ℝ)) * (1 + v n t))
    (hv : HasNewtonExponentialBound N I v) :
    HasNewtonExponentialBound N I u := by
  obtain ⟨A, α, hA, hα, hv⟩ := hv
  refine ⟨C * (1 + A), γ + α, by positivity, add_nonneg hγ hα, ?_⟩
  intro n t ht
  have hE : 1 ≤ Real.exp (α * (N n : ℝ)) :=
    Real.one_le_exp (mul_nonneg hα (Nat.cast_nonneg _))
  calc
    _ ≤ C * Real.exp (γ * (N n : ℝ)) * (1 + v n t) := huv n t ht
    _ ≤ C * Real.exp (γ * (N n : ℝ)) * ((1 + A) * Real.exp (α * (N n : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.exp_pos _).le)
      rw [add_mul, one_mul]
      exact add_le_add hE (hv n t ht)
    _ = _ := by rw [add_mul γ α, Real.exp_add]; ring

section ChainBounds

variable {Z W : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

private theorem seminorm_parameterChainSum_le
    (q : Seminorm ℝ W) (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z)
    (L : List ParameterChainTerm) (t A : ℝ)
    (h : ∀ a ∈ L, q (parameterChainTermEval J c a t) ≤ A) :
    q (parameterChainSum J c L t) ≤ (L.length : ℝ) * A := by
  induction L with
  | nil => simp [parameterChainSum]
  | cons a L ih =>
    change q (parameterChainTermEval J c a t + parameterChainSum J c L t) ≤
      ((L.length + 1 : ℕ) : ℝ) * A
    calc
      _ ≤ q (parameterChainTermEval J c a t) + q (parameterChainSum J c L t) :=
        map_add_le_add q _ _
      _ ≤ A + (L.length : ℝ) * A :=
        add_le_add (h a (List.mem_cons_self ..)) (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))
      _ = _ := by push_cast; ring

/-- Positive parameter order in each slot and the sum-of-orders rule
leave only a linear dependence on the highest derivative. -/
private theorem seminorm_compositionTower_le
    (p : Seminorm ℝ Z) (q : Seminorm ℝ W) (g : Z → W)
    (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z) {m : ℕ} (hm : 0 < m) (t : ℝ)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hJ : ∀ k, k ≤ m → ∀ v : Fin k → Z,
      q (J k (c 0 t) v) ≤ C * ∏ i, p (v i))
    (hlower : ∀ j, 0 < j → j < m → p (c j t) ≤ B) :
    q (projectiveCurveCompositionTower g J c m t) ≤
      ((parameterChainTerms m).length : ℝ) * C * (B ^ m + p (c m t)) := by
  have he : projectiveCurveCompositionTower g J c m t = parameterChainEval J c m t := by
    cases m with
    | zero => omega
    | succ m => rfl
  rw [he]
  calc
    _ ≤ ((parameterChainTerms m).length : ℝ) * (C * (B ^ m + p (c m t))) := by
      apply seminorm_parameterChainSum_le
      intro a ha
      have hk := parameterChainTerm_arity_le ha
      apply (hJ a.1 hk _).trans
      apply mul_le_mul_of_nonneg_left _ hC
      by_cases htop : ∃ i : Fin a.1, a.2 i = m
      · obtain ⟨i, hi⟩ := htop
        have hone : (∏ j, p (c (a.2 j) t)) = p (c m t) := by
          rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i), hi]
          intro j _ hj
          exact (hj (parameterChainTerm_highest_order_unique ha hi j)).elim
        rw [hone]
        linarith only [pow_nonneg (zero_le_one.trans hB) m]
      · have hprod : (∏ i, p (c (a.2 i) t)) ≤ B ^ a.1 := by
          calc
            _ ≤ ∏ _ : Fin a.1, B := by
              apply Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
              intro i _
              exact hlower _ ((parameterChainTerm_positive_and_weight ha).1 i)
                (lt_of_le_of_ne (parameterChainTerm_order_le ha i) (fun h => htop ⟨i, h⟩))
            _ = _ := by simp
        exact hprod.trans ((pow_le_pow_right₀ hB hk).trans
          (le_add_of_nonneg_right (apply_nonneg p (c m t))))
    _ = _ := by ring

/-- A family of genuine chain-rule expressions has an affine bound at
the highest order whenever the lower derivatives grow exponentially. -/
private theorem exists_exponential_compositionTower_bound
    [IsTopologicalAddGroup Z]
    {p : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ W}
    (hp : Monotone p) (hq : Monotone q) (hpc : ∀ s, Continuous (p s))
    {U K : Set Z} {g : Z → W}
    (J : Statements.SmoothDirections U g) (hJ : HasLocalJetTameBounds p q J)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {I : Set ℝ} (N : ℕ → ℕ) (c : ℕ → ℕ → ℝ → Z)
    (hc : ∀ n t, t ∈ I → c n 0 t ∈ K) {m : ℕ} (hm : 0 < m) (s : ℕ)
    (hlower : ∀ k, k < m → ∀ d,
      HasNewtonExponentialBound N I (fun n t => p d (c n k t))) :
    ∃ d : ℕ, ∃ A γ : ℝ, 0 ≤ A ∧ 0 ≤ γ ∧ ∀ n t, t ∈ I →
      q s (projectiveCurveCompositionTower g J.D (c n) m t) ≤
        A * Real.exp (γ * (N n : ℝ)) * (1 + p d (c n m t)) := by
  classical
  obtain ⟨d, C, hC, H⟩ := exists_compact_jet_product_bounds_through hp hq hpc J hJ m s hK hKU
  choose L β hL hβ Hlow using fun k : Fin m => hlower k.1 k.2 d
  let B := 1 + ∑ k, L k
  let Γ := ∑ k, β k
  let A := ((parameterChainTerms m).length : ℝ) * C * B ^ m
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => hL k))
  have hΓ : 0 ≤ Γ := Finset.sum_nonneg (fun k _ => hβ k)
  refine ⟨d, A, (m : ℝ) * Γ, ?_, mul_nonneg (Nat.cast_nonneg _) hΓ, ?_⟩
  · dsimp only [A]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (pow_nonneg (zero_le_one.trans hB) _)
  intro n t ht
  let K₀ := B * Real.exp (Γ * (N n : ℝ))
  have hK₀ : 1 ≤ K₀ :=
    one_le_mul_of_one_le_of_one_le hB (Real.one_le_exp (mul_nonneg hΓ (Nat.cast_nonneg _)))
  have hl (k : ℕ) (_ : 0 < k) (hk : k < m) : p d (c n k t) ≤ K₀ := by
    let i : Fin m := ⟨k, hk⟩
    have hLi : L i ≤ B := (Finset.single_le_sum (fun j _ => hL j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
    have hβi : β i ≤ Γ := Finset.single_le_sum (fun j _ => hβ j) (Finset.mem_univ i)
    exact (Hlow i n t ht).trans (mul_le_mul hLi
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβi (Nat.cast_nonneg _)))
      (Real.exp_pos _).le (zero_le_one.trans hB))
  have hpow : 1 ≤ K₀ ^ m := one_le_pow₀ hK₀
  have hfin : K₀ ^ m + p d (c n m t) ≤ K₀ ^ m * (1 + p d (c n m t)) := by
    rw [mul_add, mul_one]
    exact add_le_add_left
      (le_mul_of_one_le_left (apply_nonneg (p d) (c n m t)) hpow) _
  calc
    _ ≤ ((parameterChainTerms m).length : ℝ) * C * (K₀ ^ m + p d (c n m t)) :=
      seminorm_compositionTower_le (p d) (q s) g J.D (c n) hm t hC hK₀
        (fun k hk v => H k hk _ (hc n t ht) v) hl
    _ ≤ ((parameterChainTerms m).length : ℝ) * C * (K₀ ^ m * (1 + p d (c n m t))) :=
      mul_le_mul_of_nonneg_left hfin (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = _ := by
      dsimp only [K₀, A]
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (m : ℝ) * (Γ * (N n : ℝ)) = (m : ℝ) * Γ * (N n : ℝ) by ring]
      ring

end ChainBounds

section CompactTrajectories

variable {E : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, CompleteSpace (E n)]
  {e : ∀ n, E (n + 1) →L[ℝ] E n}

/-- The summable grade majorants of the actual differences promote
pointwise convergence to uniform convergence in the projective space. -/
theorem tendstoUniformlyOn_projectiveLimit_of_summable_increments
    {I : Set ℝ} {x : ℕ → ℝ → ProjectiveLimit E e} {f : ℝ → ProjectiveLimit E e}
    (hlim : ∀ t ∈ I, Tendsto (fun n => x n t) atTop (𝓝 (f t)))
    (D : ℕ → ℕ → ℝ) (hD : ∀ s, Summable (D s))
    (hinc : ∀ s n t, t ∈ I → gradedSeminorm E e s (x (n + 1) t - x n t) ≤ D s n) :
    TendstoUniformlyOn x f atTop I := by
  have hcoord (s : ℕ) : TendstoUniformlyOn (fun n t => (x n t).1 s)
      (fun t => (f t).1 s) atTop I := by
    let δ (n : ℕ) (t : ℝ) := (x (n + 1) t).1 s - (x n t).1 s
    have hδ (n : ℕ) (t : ℝ) (ht : t ∈ I) : ‖δ n t‖ ≤ D s n :=
      (norm_coordinate_le_graded E e le_rfl (x (n + 1) t - x n t)).trans (hinc s n t ht)
    have hsum (n : ℕ) (t : ℝ) :
        (∑ j ∈ Finset.range n, δ j t) = (x n t).1 s - (x 0 t).1 s :=
      Finset.sum_range_sub (fun j => (x j t).1 s) n
    have hsub : TendstoUniformlyOn (fun n t => (x n t).1 s - (x 0 t).1 s)
        (fun t => ∑' j, δ j t) atTop I := by
      simpa only [hsum] using tendstoUniformlyOn_tsum_nat (hD s) hδ
    have hsub' := hsub.congr_right (g := fun t => (f t).1 s - (x 0 t).1 s) (by
      intro t ht
      have h := (tendsto_projectiveLimit_iff E e).mp (hlim t ht) s
      exact tendsto_nhds_unique (hsub.tendsto_at ht) (h.sub tendsto_const_nhds))
    rw [Metric.tendstoUniformlyOn_iff] at hsub' ⊢
    simpa only [dist_sub_right] using hsub'
  rw [tendstoUniformlyOn_iff_tendsto, uniformity_subtype, tendsto_comap_iff,
    Pi.uniformity, tendsto_iInf]
  intro s
  rw [tendsto_comap_iff]
  exact (tendstoUniformlyOn_iff_tendsto.mp (hcoord s))

/-- A compact parameter set and uniform convergence yield a compact
set containing every point of every curve and the limit curve. -/
private theorem exists_compact_trajectory_of_tendstoUniformlyOn
    {Z : Type*} [UniformSpace Z] {I : Set ℝ} (hI : IsCompact I)
    {z : ℕ → ℝ → Z} {f : ℝ → Z} {U : Set Z}
    (hz : ∀ n, ContinuousOn (z n) I) (hlim : TendstoUniformlyOn z f atTop I)
    (hiter : ∀ n t, t ∈ I → z n t ∈ U) (hlimit : ∀ t ∈ I, f t ∈ U) :
    ∃ K : Set Z, IsCompact K ∧ K ⊆ U ∧ ∀ n t, t ∈ I → z n t ∈ K := by
  letI : CompactSpace I := isCompact_iff_compactSpace.mp hI
  have hf : ContinuousOn f I := hlim.continuousOn (Eventually.of_forall hz).frequently
  let G (n : ℕ) : C(I, Z) := ⟨I.domRestrict (z n), (hz n).domRestrict⟩
  let g : C(I, Z) := ⟨I.domRestrict f, hf.domRestrict⟩
  have hG : Tendsto G atTop (𝓝 g) :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
      (fun _ _ => (tendstoUniformlyOn_iff_restrict.mp hlim).tendstoUniformlyOn)
  let K := (fun w : C(I, Z) × I => w.1 w.2) '' ((insert g (range G)) ×ˢ (univ : Set I))
  refine ⟨K, (hG.isCompact_insert_range.prod isCompact_univ).image continuous_eval, ?_, ?_⟩
  · rintro _ ⟨⟨h, t⟩, hh, rfl⟩
    rcases mem_insert_iff.mp hh.1 with rfl | hh
    · exact hlimit t t.2
    · obtain ⟨n, rfl⟩ := hh
      exact hiter n t t.2
  · intro n t ht
    exact ⟨(G n, ⟨t, ht⟩), ⟨mem_insert_of_mem _ (mem_range_self n), mem_univ _⟩, rfl⟩

end CompactTrajectories

section GrowthOfUpdates

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- Use one fixed input grade for smoothing. The chain-rule loss only
enters the grade used to close the scalar recurrence. -/
private theorem newton_update_exponential_bounds
    (p : ℕ → Seminorm ℝ X) (S : ℕ → X →L[ℝ] X) {I : Set ℝ}
    {N₀ : ℕ} (hN₀ : 0 < N₀) (b d : ℕ)
    (hS : ∀ s, ∃ K γ : ℝ, 0 ≤ K ∧ 0 ≤ γ ∧ ∀ (N : ℕ) u,
      p s (S N u) ≤ K * Real.exp (γ * (N : ℝ)) * p b u)
    (x w : ℕ → ℝ → X)
    (hstep : ∀ n t, x (n + 1) t = x n t - S (newtonSmoothingIndex N₀ n) (w n t))
    (hinit : ∀ s, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, p s (x 0 t) ≤ B)
    {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hw : ∀ n t, t ∈ I → p b (w n t) ≤
      C * Real.exp (γ * (newtonSmoothingIndex N₀ n : ℝ)) * (1 + p d (x n t))) :
    (∀ s, HasNewtonExponentialBound (newtonSmoothingIndex N₀) I (fun n t => p s (x n t))) ∧
    (∀ s, HasNewtonExponentialBound (newtonSmoothingIndex N₀) I
      (fun n t => p s (x (n + 1) t - x n t))) := by
  let N := newtonSmoothingIndex N₀
  have hdiff (s n : ℕ) (t : ℝ) :
      p s (x (n + 1) t - x n t) = p s (S (N n) (w n t)) := by
    rw [hstep n t, show x n t - S (N n) (w n t) - x n t = -S (N n) (w n t) by abel,
      map_neg_eq_map]
  have hsmoothed (s : ℕ) : ∃ K κ : ℝ, 0 ≤ K ∧ 0 ≤ κ ∧ ∀ n t, t ∈ I →
      p s (x (n + 1) t - x n t) ≤ K * Real.exp (κ * (N n : ℝ)) * (1 + p d (x n t)) := by
    obtain ⟨K, κ, hK, hκ, H⟩ := hS s
    refine ⟨K * C, κ + γ, mul_nonneg hK hC, add_nonneg hκ hγ, ?_⟩
    intro n t ht
    rw [hdiff s n t]
    calc
      _ ≤ K * Real.exp (κ * (N n : ℝ)) * p b (w n t) := H (N n) (w n t)
      _ ≤ K * Real.exp (κ * (N n : ℝ)) *
          (C * Real.exp (γ * (N n : ℝ)) * (1 + p d (x n t))) :=
        mul_le_mul_of_nonneg_left (hw n t ht) (mul_nonneg hK (Real.exp_pos _).le)
      _ = _ := by rw [add_mul κ γ, Real.exp_add]; ring
  have htriangle (s n : ℕ) (t : ℝ) :
      p s (x (n + 1) t) ≤ p s (x n t) + p s (x (n + 1) t - x n t) := by
    calc
      _ = p s (x n t + (x (n + 1) t - x n t)) := congrArg (p s) (by abel)
      _ ≤ _ := map_add_le_add (p s) _ _
  obtain ⟨A, α, hA, hα, HA⟩ := hsmoothed d
  obtain ⟨B, hB, HB⟩ := hinit d
  have hcontrol : HasNewtonExponentialBound N I (fun n t => p d (x n t)) := by
    refine ⟨1 + B, 2 * (A + α), by positivity, by positivity, ?_⟩
    intro n t ht
    exact (le_add_of_nonneg_left zero_le_one).trans
      (newtonParameterGrowth_of_affine_recurrence hN₀ (fun n t => p d (x n t))
        hB hA hα (fun n t _ => apply_nonneg _ _) HB
        (fun n t ht => (htriangle d n t).trans (add_le_add_left (HA n t ht) _))
        n t ht)
  have hinc (s : ℕ) : HasNewtonExponentialBound N I
      (fun n t => p s (x (n + 1) t - x n t)) := by
    obtain ⟨K, κ, hK, hκ, H⟩ := hsmoothed s
    exact hasNewtonExponentialBound_of_affine hK hκ H hcontrol
  refine ⟨?_, hinc⟩
  intro s
  obtain ⟨K, κ, hK, hκ, H⟩ := hinc s
  obtain ⟨B, hB, HB⟩ := hinit s
  refine ⟨1 + B, 2 * (K + κ), by positivity, by positivity, ?_⟩
  intro n t ht
  apply (le_add_of_nonneg_left zero_le_one).trans
  refine newtonParameterGrowth_of_affine_recurrence hN₀ (fun n t => p s (x n t))
    hB hK hκ (fun n t _ => apply_nonneg _ _) HB ?_ n t ht
  intro n t ht
  have hcoef : 0 ≤ K * Real.exp (κ * (N n : ℝ)) := mul_nonneg hK (Real.exp_pos _).le
  have hp : 1 ≤ 1 + p s (x n t) := le_add_of_nonneg_right (apply_nonneg _ _)
  exact (htriangle s n t).trans (add_le_add_left ((H n t ht).trans
    (le_mul_of_one_le_right hcoef hp)) _)

end GrowthOfUpdates

/-- One pair of actual derivative towers works on the entire parameter
domain. On each compact subset, every state and increment derivative has
an exponential majorant in every grade along the original smoothing
schedule. -/
theorem exists_projectiveNewtonParameterTower_exponential_bounds
    {E F : ℕ → Type*}
    [∀ s, NormedAddCommGroup (E s)] [∀ s, NormedSpace ℝ (E s)] [∀ s, CompleteSpace (E s)]
    [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℝ (F s)] [∀ s, CompleteSpace (F s)]
    {e : ∀ s, E (s + 1) →L[ℝ] E s} {f : ∀ s, F (s + 1) →L[ℝ] F s}
    {U : Set (ProjectiveLimit E e × ℝ)} (hUc : Convex ℝ U)
    (R : ProjectiveLimit E e × ℝ → ProjectiveLimit F f)
    (V : ProjectiveLimit E e × ℝ → ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit E e)
    (S : ℕ → ProjectiveLimit E e →L[ℝ] ProjectiveLimit E e)
    (x₀ : ProjectiveLimit E e) {N₀ : ℕ} (hN₀ : 0 < N₀) (b : ℕ)
    {I : Set ℝ} (xlim : ℝ → ProjectiveLimit E e) (D : ℕ → ℕ → ℝ) :
    let p := gradedSeminorm E e
    let q := gradedSeminorm F f
    let a := Statements.pairGrading p Statements.realGrading
    let V' := fun z : (ProjectiveLimit E e × ℝ) × ProjectiveLimit F f => V z.1 z.2
    let N := newtonSmoothingIndex N₀
    let z := fun n t => projectiveSmoothedNewtonIterates R V S N (x₀, t) n
    (∀ s, ∃ C γ : ℝ, 0 ≤ C ∧ 0 ≤ γ ∧ ∀ (L : ℕ) u,
      p s (S L u) ≤ C * Real.exp (γ * (L : ℝ)) * p b u) →
    Statements.SmoothTameOn a q U R →
    Statements.SmoothTameOn (Statements.pairGrading a q) p (U ×ˢ univ) V' →
    (∀ n t, t ∈ I → z n t ∈ U) →
    (∀ t ∈ I, Tendsto (fun n => z n t) atTop (𝓝 (xlim t, t)) ∧ (xlim t, t) ∈ U) →
    (∀ s, Summable (D s)) →
    (∀ s n t, t ∈ I → p s ((z (n + 1) t).1 - (z n t).1) ≤ D s n) →
    ∃ JR : ProjectiveJetFamily (ProjectiveLimit E e × ℝ) (ProjectiveLimit F f),
    ∃ JV : ProjectiveJetFamily ((ProjectiveLimit E e × ℝ) × ProjectiveLimit F f)
        (ProjectiveLimit E e),
      let x := projectiveNewtonParameterTower R V JR JV S N x₀
      (∀ n m t, t ∈ I → HasProjectiveCurveDerivAt (x n m) (x n (m + 1) t) t) ∧
      ∀ J : Set ℝ, IsCompact J → J ⊆ I → ∀ m s, ∃ C γ : ℝ, 0 ≤ C ∧ 0 ≤ γ ∧
        ∀ n t, t ∈ J →
          p s (x n m t) ≤ C * Real.exp (γ * (N n : ℝ)) ∧
          p s (x (n + 1) m t - x n m t) ≤ C * Real.exp (γ * (N n : ℝ)) := by
  dsimp only
  intro hS hR hV hiter hlim hD hinc
  let X := ProjectiveLimit E e
  let Y := ProjectiveLimit F f
  let p := gradedSeminorm E e
  let q := gradedSeminorm F f
  let a := Statements.pairGrading p Statements.realGrading
  let aV := Statements.pairGrading a q
  let V' := fun z : (X × ℝ) × Y => V z.1 z.2
  let N := newtonSmoothingIndex N₀
  obtain ⟨JR, HR⟩ := hR
  obtain ⟨JV, HV⟩ := hV
  have hJR : HasProjectiveJetsOn R JR.D U :=
    ⟨JR.zero, JR.continuous, fun k z hz v vs => JR.derivative k z hz vs v⟩
  have hJV : HasProjectiveJetsOn V' JV.D (U ×ˢ univ) :=
    ⟨JV.zero, JV.continuous, fun k z hz v vs => JV.derivative k z hz vs v⟩
  let x := projectiveNewtonParameterTower R V JR.D JV.D S N x₀
  let z := fun n k t => (x n k t, realParameterTower k t)
  let r := fun n => projectiveCurveCompositionTower R JR.D (z n)
  let w := fun n k t => (z n k t, r n k t)
  let v := fun n => projectiveCurveCompositionTower V' JV.D (w n)
  have hxzero (n : ℕ) (t : ℝ) :
      x n 0 t = (projectiveSmoothedNewtonIterates R V S N (x₀, t) n).1 :=
    projectiveNewtonParameterTower_zero R V JR.D JV.D S N x₀ n t
  have hzzero (n : ℕ) (t : ℝ) :
      z n 0 t = projectiveSmoothedNewtonIterates R V S N (x₀, t) n :=
    Prod.ext (hxzero n t) (projectiveSmoothedNewtonIterates_parameter R V S N (x₀, t) n).symm
  have hderiv (n m : ℕ) (t : ℝ) (ht : t ∈ I) :
      HasProjectiveCurveDerivAt (x n m) (x n (m + 1) t) t :=
    hasProjectiveCurveDerivAt_projectiveNewtonParameterTower R V JR.open_domain hUc
      hJR hJV S N x₀ hiter n m ht
  refine ⟨JR.D, JV.D, hderiv, ?_⟩
  intro J hJ hJI m s
  have huni : TendstoUniformlyOn (fun n => x n 0) xlim atTop J := by
    apply tendstoUniformlyOn_projectiveLimit_of_summable_increments (D := D) _ hD
    · intro t ht
      have h := (continuous_fst.tendsto (xlim t, t)).comp (hlim t (hJI ht)).1
      exact h.congr' (Eventually.of_forall fun n => (hxzero n t).symm)
    · intro s n t ht
      simpa only [hxzero] using hinc s n t (hJI ht)
  have hparam : TendstoUniformlyOn (fun _ : ℕ => id) id atTop J := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun _ t _ => by simpa only [id_eq, dist_self] using hε
  have hzcont (n : ℕ) : ContinuousOn (z n 0) J := by
    intro t ht
    exact ((hderiv n 0 t (hJI ht)).continuousAt_topological.prodMk
      continuousAt_id).continuousWithinAt
  have hpair : TendstoUniformlyOn (fun n => z n 0) (fun t => (xlim t, t)) atTop J :=
    (huni.prodMk hparam).seq_tendstoUniformlyOn (fun n : ℕ => (n, n))
      (tendsto_id.prodMk tendsto_id)
  obtain ⟨K, hK, hKU, hzk⟩ := exists_compact_trajectory_of_tendstoUniformlyOn hJ hzcont hpair
    (fun n t ht => by rw [hzzero]; exact hiter n t (hJI ht))
    (fun t ht => (hlim t (hJI ht)).2)
  have hRcont : ContinuousOn R U := by
    have hc : Continuous (fun z : X × ℝ => (z, (Fin.elim0 : Fin 0 → X × ℝ))) :=
      continuous_id.prodMk continuous_const
    exact ((JR.continuous 0).comp hc.continuousOn
      (fun z hz => ⟨hz, mem_univ _⟩)).congr (fun z hz => (JR.zero z hz).symm)
  let K' := (fun z => (z, R z)) '' K
  have hK' : IsCompact K' :=
    hK.image_of_continuousOn (continuous_id.continuousOn.prodMk (hRcont.mono hKU))
  have hK'U : K' ⊆ U ×ˢ univ := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hKU hz, mem_univ _⟩
  have hwk (n : ℕ) (t : ℝ) (ht : t ∈ J) : w n 0 t ∈ K' :=
    mem_image_of_mem _ (hzk n t ht)
  have hp := gradedSeminorm_monotone E e
  have hq := gradedSeminorm_monotone F f
  have ha : Monotone a := pairGrading_monotone hp monotone_const
  have haV : Monotone aV := pairGrading_monotone ha hq
  have hac (s : ℕ) : Continuous (a s) := by
    change Continuous (fun z : X × ℝ => p s z.1 + ‖z.2‖)
    exact ((continuous_gradedSeminorm E e s).comp continuous_fst).add
      (continuous_norm.comp continuous_snd)
  have haVc (s : ℕ) : Continuous (aV s) := by
    change Continuous (fun z : (X × ℝ) × Y => a s z.1 + q s z.2)
    exact ((hac s).comp continuous_fst).add ((continuous_gradedSeminorm F f s).comp continuous_snd)
  have hrealOne (k : ℕ) (hk : 0 < k) (t : ℝ) : ‖realParameterTower k t‖ ≤ 1 := by
    cases k with
    | zero => omega
    | succ k =>
      cases k <;> simp [realParameterTower]
  have hreal (k : ℕ) : HasNewtonExponentialBound N J (fun _ t => ‖realParameterTower k t‖) := by
    obtain ⟨B, hB⟩ := hJ.bddAbove_image (continuous_norm.continuousOn (s := J))
    refine ⟨max B 1, 0, zero_le_one.trans (le_max_right _ _), le_rfl, ?_⟩
    intro n t ht
    simp only [zero_mul, Real.exp_zero, mul_one]
    cases k with
    | zero => exact (hB (mem_image_of_mem _ ht)).trans (le_max_left _ _)
    | succ k => exact (hrealOne (k + 1) (Nat.zero_lt_succ k) t).trans (le_max_right _ _)
  have hX₀ (s : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n t, t ∈ J → p s (x n 0 t) ≤ B := by
    obtain ⟨B, hB⟩ := hK.bddAbove_image
      (((continuous_gradedSeminorm E e s).comp continuous_fst).continuousOn (s := K))
    exact ⟨max B 0, le_max_right _ _, fun n t ht =>
      (hB (mem_image_of_mem _ (hzk n t ht))).trans (le_max_left _ _)⟩
  have hR₀ (s : ℕ) : HasNewtonExponentialBound N J (fun n t => q s (r n 0 t)) := by
    obtain ⟨B, hB⟩ := hK'.bddAbove_image
      (((continuous_gradedSeminorm F f s).comp continuous_snd).continuousOn (s := K'))
    refine ⟨max B 0, 0, le_max_right _ _, le_rfl, ?_⟩
    intro n t ht
    simpa only [zero_mul, Real.exp_zero, mul_one] using
      (hB (mem_image_of_mem _ (hwk n t ht))).trans (le_max_left B 0)
  have hAll (k : ℕ) :
      (∀ s, HasNewtonExponentialBound N J (fun n t => p s (x n k t))) ∧
      (∀ s, HasNewtonExponentialBound N J (fun n t => p s (x (n + 1) k t - x n k t))) ∧
      (∀ s, HasNewtonExponentialBound N J (fun n t => q s (r n k t))) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk : k = 0
      · subst k
        refine ⟨?_, ?_, hR₀⟩
        · intro s
          obtain ⟨B, hB, HB⟩ := hX₀ s
          exact ⟨B, 0, hB, le_rfl, fun n t ht => by
            simpa only [zero_mul, Real.exp_zero, mul_one] using HB n t ht⟩
        · intro s
          obtain ⟨B, hB, HB⟩ := hX₀ s
          refine ⟨B + B, 0, add_nonneg hB hB, le_rfl, ?_⟩
          intro n t ht
          simpa only [zero_mul, Real.exp_zero, mul_one] using
            (map_sub_le_add (p s) (x (n + 1) 0 t) (x n 0 t)).trans
              (add_le_add (HB (n + 1) t ht) (HB n t ht))
      · have hk' : 0 < k := Nat.pos_of_ne_zero hk
        have hzlower (j : ℕ) (hj : j < k) (s : ℕ) :
            HasNewtonExponentialBound N J (fun n t => a s (z n j t)) :=
          hasNewtonExponentialBound_add ((ih j hj).1 s) (hreal j)
        have hwlower (j : ℕ) (hj : j < k) (s : ℕ) :
            HasNewtonExponentialBound N J (fun n t => aV s (w n j t)) :=
          hasNewtonExponentialBound_add (hzlower j hj s) ((ih j hj).2.2 s)
        have hexpR (s : ℕ) := exists_exponential_compositionTower_bound
          ha hq hac JR HR hK hKU N z hzk hk' s hzlower
        obtain ⟨dV, A, α, hA, hα, HA⟩ := exists_exponential_compositionTower_bound
          haV hp haVc JV HV hK' hK'U N w hwk hk' b hwlower
        obtain ⟨dR, B, β, hB, hβ, HB⟩ := hexpR dV
        let d := max dV dR
        have hbound (n : ℕ) (t : ℝ) (ht : t ∈ J) :
            p b (v n k t) ≤ A * (2 + 2 * B) * Real.exp ((α + β) * (N n : ℝ)) *
              (1 + p d (x n k t)) := by
          let P := p d (x n k t)
          have hP : 0 ≤ P := apply_nonneg _ _
          have hzle (s : ℕ) (hs : s ≤ d) : a s (z n k t) ≤ P + 1 :=
            add_le_add (hp hs _) (hrealOne k hk' t)
          have hE : 1 ≤ Real.exp (β * (N n : ℝ)) :=
            Real.one_le_exp (mul_nonneg hβ (Nat.cast_nonneg _))
          have hr : q dV (r n k t) ≤ 2 * B * Real.exp (β * (N n : ℝ)) * (1 + P) := by
            calc
              _ ≤ B * Real.exp (β * (N n : ℝ)) * (1 + a dR (z n k t)) := HB n t ht
              _ ≤ B * Real.exp (β * (N n : ℝ)) * (2 * (1 + P)) :=
                mul_le_mul_of_nonneg_left (by linarith only [hzle dR (le_max_right _ _), hP])
                  (mul_nonneg hB (Real.exp_pos _).le)
              _ = _ := by ring
          have hw₁ : 1 + a dV (z n k t) ≤ 2 * Real.exp (β * (N n : ℝ)) * (1 + P) := by
            calc
              _ ≤ 2 * (1 + P) := by linarith only [hzle dV (le_max_left _ _), hP]
              _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hE]) (by positivity)
          have hw₂ : 1 + aV dV (w n k t) ≤ (2 + 2 * B) * Real.exp (β * (N n : ℝ)) * (1 + P) := by
            change 1 + (a dV (z n k t) + q dV (r n k t)) ≤ _
            calc
              _ = (1 + a dV (z n k t)) + q dV (r n k t) := by ring
              _ ≤ _ := (add_le_add hw₁ hr).trans_eq (by ring)
          calc
            _ ≤ A * Real.exp (α * (N n : ℝ)) * (1 + aV dV (w n k t)) := HA n t ht
            _ ≤ A * Real.exp (α * (N n : ℝ)) *
                ((2 + 2 * B) * Real.exp (β * (N n : ℝ)) * (1 + P)) :=
              mul_le_mul_of_nonneg_left hw₂ (mul_nonneg hA (Real.exp_pos _).le)
            _ = _ := by rw [add_mul α β, Real.exp_add]; ring
        have hinit (s : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ J, p s (x 0 k t) ≤ B := by
          refine ⟨0, le_rfl, ?_⟩
          intro t _
          cases k with
          | zero => contradiction
          | succ k => exact (map_zero (p s)).le
        obtain ⟨hx, hxinc⟩ := newton_update_exponential_bounds p S hN₀ b d hS
          (fun n => x n k) (fun n => v n k) (fun _ _ => rfl) hinit
          (show 0 ≤ A * (2 + 2 * B) by positivity) (add_nonneg hα hβ) hbound
        refine ⟨hx, hxinc, ?_⟩
        intro s
        obtain ⟨d, A, α, hA, hα, HA⟩ := hexpR s
        exact hasNewtonExponentialBound_of_affine hA hα HA
          (hasNewtonExponentialBound_add (hx d) (hreal k))
  obtain ⟨C, γ, hC, hγ, HC⟩ := hasNewtonExponentialBound_add ((hAll m).1 s) ((hAll m).2.1 s)
  refine ⟨C, γ, hC, hγ, fun n t ht => ⟨?_, ?_⟩⟩
  · exact (le_add_of_nonneg_right (apply_nonneg _ _)).trans (HC n t ht)
  · exact (le_add_of_nonneg_left (apply_nonneg _ _)).trans (HC n t ht)

end ContinuousFlexibility.Analysis
