module

public import ContinuousFlexibility.Analysis.N01cMixedPowerAlgebra

/-!
# Compact scalar composition with distributed spatial orders

The spatial Faà di Bruno formula uses the actual scalar derivatives.
Its parameter derivatives are bounded before the spatial factors are
multiplied. A nonempty collection of positive parameter factors retains
one full height weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def coordinateRadialOrder {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ i, if w i = 0 then 1 else 0

def coordinateAngularOrder {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ i, if w i = 0 then 0 else 1

theorem coordinateOrders_sum {n : ℕ} (w : Fin n → Fin 2) :
    coordinateRadialOrder w + coordinateAngularOrder w = n := by
  rw [coordinateRadialOrder, coordinateAngularOrder, ← Finset.sum_add_distrib]
  have he : (fun i => (if w i = 0 then 1 else 0) + (if w i = 0 then 0 else 1)) =
      (fun _ : Fin n => (1 : ℕ)) := by
    funext i
    by_cases hi : w i = 0 <;> simp only [hi, if_true, if_false] <;> omega
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one]

/-- Exact scalar form of the actual spatial partition formula. -/
theorem mixedDerivative_scalarComp_ordered
    {Ω : Set PolarPoint} {V : Set ℝ} {f : PolarPoint → ℝ} {g : ℝ → ℝ}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f Ω)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f Ω V)
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b (g ∘ f) q =
      ∑ c : OrderedFinpartition (a + b), iteratedDeriv c.length g (f q) *
        ∏ i : Fin c.length,
          mixedDerivative (coordinateRadialOrder (cylinderMixedWord a b ∘ c.emb i))
            (coordinateAngularOrder (cylinderMixedWord a b ∘ c.emb i)) f q := by
  rw [mixedDerivative_eq_iteratedFDeriv_word hΩ (hg.comp hf hmap) a b hq,
    iteratedFDeriv_comp_ordered_apply hΩ hV hf hg hmap (a + b) hq
      (fun i => cylinderBasisVector (cylinderMixedWord a b i))]
  apply Finset.sum_congr rfl
  intro c _
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact iteratedFDeriv_cylinderBasis_eq_mixedDerivative hΩ hf
    (c.partSize i) hq (cylinderMixedWord a b ∘ c.emb i)

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- A numerical bound for a genuine scalar parameter composition.
Only the positive inner jets need the small height weight. -/
theorem scalarComposition_parameterJet_power_bound
    {U : Set X} {V : Set ℝ} {f : X → ℝ} {g : ℝ → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U (g ∘ f))
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    {N k : ℕ} (hk : k ≤ N) {x : X} (hx : x ∈ U)
    {B P M H RH : ℝ} (hB : 1 ≤ B) (hP : 1 ≤ P)
    (hcard : (Fintype.card (OrderedFinpartition k) : ℝ) ≤ P)
    (hM : 1 ≤ M) (hH : 0 ≤ H) (hHR : H ≤ RH)
    (houter : ∀ j : ℕ, j ≤ k → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B)
    (v : Fin k → X)
    (hinner : ∀ c : OrderedFinpartition k, ∀ i : Fin c.length,
      ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ ≤ H * M) :
    ‖K.D k x v‖ ≤ B * P * (max 1 RH) ^ N * M ^ N * parameterHeightWeight H k := by
  let JK := smoothDirections_contDiff_comp J hV hg hmap
  have heq := HasProjectiveJetsOn.unique K.open_domain
    K.hasProjectiveJetsOn JK.hasProjectiveJetsOn k x hx
  have heval : K.D k x v = JK.D k x v :=
    congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
  have hRH : 1 ≤ max 1 RH := le_max_left _ _
  have hMP : 1 ≤ P * (max 1 RH) ^ N * M ^ N :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hP (one_le_pow₀ hRH)) (one_le_pow₀ hM)
  by_cases hk0 : k = 0
  · subst k
    have hb : ‖g (f x)‖ ≤ B := by
      simpa only [norm_iteratedFDeriv_zero] using houter 0 le_rfl
    rw [smoothDirections_D_zero_apply K hx v]
    simpa only [Function.comp_def, parameterHeightWeight, ite_true, mul_one, mul_assoc] using
      hb.trans (le_mul_of_one_le_right (zero_le_one.trans hB) hMP)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hterm (c : OrderedFinpartition k) :
        (∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖) ≤
          (max 1 RH) ^ N * M ^ N * H := by
      have hpH : H ^ c.length ≤ (max 1 RH) ^ N * H :=
        (nonempty_weight_power_le hH (hHR.trans (le_max_right _ _))
          (c.length_pos hkpos)).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hRH ((Nat.sub_le c.length 1).trans (c.length_le.trans hk))) hH)
      have hpM : M ^ c.length ≤ M ^ N := pow_le_pow_right₀ hM (c.length_le.trans hk)
      calc
        _ ≤ ∏ _i : Fin c.length, H * M :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hinner c i)
        _ = H ^ c.length * M ^ c.length := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
        _ ≤ ((max 1 RH) ^ N * H) * M ^ N :=
          mul_le_mul hpH hpM (pow_nonneg (zero_le_one.trans hM) _)
            (mul_nonneg (pow_nonneg (zero_le_one.trans hRH) _) hH)
        _ = _ := by ring
    calc
      _ = ‖JK.D k x v‖ := congrArg norm heval
      _ ≤ B * ∑ c : OrderedFinpartition k,
          ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ :=
        smoothDirections_contDiff_comp_D_norm_le_of_outer_bound
          J hV hg hmap k x B houter v
      _ ≤ B * ∑ _c : OrderedFinpartition k, (max 1 RH) ^ N * M ^ N * H :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hterm c))
          (zero_le_one.trans hB)
      _ ≤ B * (P * ((max 1 RH) ^ N * M ^ N * H)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcard (by positivity)) (zero_le_one.trans hB)
      _ = _ := by simp only [parameterHeightWeight, if_neg hk0]; ring

/-- Compact scalar composition preserves the same spatial loss. -/
theorem MixedPowerBounds.scalarComp
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
    {f : X → PolarPoint → ℝ}
    (hf : MixedPowerBounds p center base loss U Ω H E f)
    (F : MixedJetRegularity U Ω f)
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hE : ∀ q ∈ Ω, 1 ≤ E q) {RH : ℝ} (hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH)
    {V K : Set ℝ} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g V)
    (hmap : ∀ x ∈ U, MapsTo (f x) Ω K) :
    MixedPowerBounds p center base loss U Ω H E (fun x q => g (f x q)) := by
  classical
  intro N s
  obtain ⟨Cf, Af, hCf, hAf, hfb⟩ := hf N s
  choose cg hcg hcgb using (fun m : Fin (s + 1) =>
    compact_iteratedFDeriv_bound hK
      (fun y hy => (contDiffOn_iteratedDeriv_open hV hg m.val).contDiffAt
        (hV.mem_nhds (hKV hy))) N)
  let Cg : ℝ := 1 + ∑ m : Fin (s + 1), cg m
  have hCg : 1 ≤ Cg := by
    have hh : 0 ≤ ∑ m : Fin (s + 1), cg m :=
      Finset.sum_nonneg (fun m _ => (hcg m).le)
    dsimp only [Cg]
    linarith
  have houter (m : ℕ) (hm : m ≤ s) (j : ℕ) (hj : j ≤ N) (y : ℝ) (hy : y ∈ K) :
      ‖iteratedFDeriv ℝ j (iteratedDeriv m g) y‖ ≤ Cg := by
    let i : Fin (s + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    exact (hcgb i j hj y hy).trans
      ((Finset.single_le_sum (fun l _ => (hcg l).le) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one))
  let P : ℝ := 1 + ∑ j : Fin (N + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)
  let Q : ℝ := 1 + ∑ n : Fin (s + 1), (Fintype.card (OrderedFinpartition n.val) : ℝ)
  have hP : 1 ≤ P := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg (α := ℝ) _))
  have hQ : 1 ≤ Q := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg (α := ℝ) _))
  have hcardP (j : ℕ) (hj : j ≤ N) :
      (Fintype.card (OrderedFinpartition j) : ℝ) ≤ P := by
    have hh : (Fintype.card (OrderedFinpartition j) : ℝ) ≤
        ∑ i : Fin (N + 1), (Fintype.card (OrderedFinpartition i.val) : ℝ) :=
      Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin (N + 1)))) =>
          Nat.cast_nonneg (α := ℝ) (Fintype.card (OrderedFinpartition i.val)))
        (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (N + 1)))
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  have hcardQ (n : ℕ) (hn : n ≤ s) :
      (Fintype.card (OrderedFinpartition n) : ℝ) ≤ Q := by
    have hh : (Fintype.card (OrderedFinpartition n) : ℝ) ≤
        ∑ i : Fin (s + 1), (Fintype.card (OrderedFinpartition i.val) : ℝ) :=
      Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin (s + 1)))) =>
          Nat.cast_nonneg (α := ℝ) (Fintype.card (OrderedFinpartition i.val)))
        (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (s + 1)))
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  choose cp hcp hcpb using (fun i : Fin (s + 2) × Fin (N + 1) =>
    exists_finiteProduct_allParameterJet_bound (X := X) i.1.val i.2.val RH)
  let Cp : ℝ := 1 + ∑ i : Fin (s + 2) × Fin (N + 1), cp i
  have hCp : 1 ≤ Cp := by
    have hh : 0 ≤ ∑ i : Fin (s + 2) × Fin (N + 1), cp i :=
      Finset.sum_nonneg (fun i _ => (hcp i).le)
    dsimp only [Cp]
    linarith
  have hcpCp (i : Fin (s + 2) × Fin (N + 1)) : cp i ≤ Cp :=
    (Finset.single_le_sum (fun j _ => (hcp j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  let C0 : ℝ := Cg * P * (max 1 RH) ^ N * Cf ^ N
  have hC0 : 1 ≤ C0 := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCg hP)
      (one_le_pow₀ (le_max_left _ _))) (one_le_pow₀ hCf)
  let C : ℝ := Cp * C0 * Cf ^ s * Q
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCp hC0) (one_le_pow₀ hCf)) hQ
  refine ⟨C, Af * (N + s), hC, by positivity, ?_⟩
  intro k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  have hEpos : 0 < E q := zero_lt_one.trans_le (hE q hq)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let J0 : SmoothDirections U (fun y => f y q) :=
    (F.parameter 0 0 q hq).congr
      (fun y _ => by simp only [mixedDerivative, iteratedDeriv_zero])
  let JO (m : ℕ) : SmoothDirections U (fun y => iteratedDeriv m g (f y q)) :=
    smoothDirections_contDiff_comp J0 hV (contDiffOn_iteratedDeriv_open hV hg m)
      (fun y hy => hKV (hmap y hy hq))
  let B0 : ℝ := C0 * E q ^ (Af * N)
  have hB0 : 0 < B0 :=
    mul_pos (zero_lt_one.trans_le hC0) (Real.rpow_pos_of_pos hEpos _)
  have hOJ (m : ℕ) (hm : m ≤ s) (j : ℕ) (hj : j ≤ N)
      (w : Fin j → X) (hw : ∀ i, p base (w i) ≤ 1)
      (hwhigh : ∀ i, p (s + loss) (w i) ≤ R) :
      ‖(JO m).D j x w‖ ≤ B0 * parameterHeightWeight (H q) j := by
    have hM : 1 ≤ Cf * E q ^ Af :=
      one_le_mul_of_one_le_of_one_le hCf (Real.one_le_rpow (hE q hq) hAf)
    have hb := scalarComposition_parameterJet_power_bound
      (f := fun y => f y q) (g := iteratedDeriv m g)
      J0 (JO m) hV (contDiffOn_iteratedDeriv_open hV hg m)
      (fun y hy => hKV (hmap y hy hq)) hj hx hCg hP (hcardP j hj) hM
      (hH q hq).1 (hH q hq).2
      (fun l hl => houter m hm l (hl.trans hj) _ (hmap x hx hq)) w
      (fun d i => by
        have hh := hfb (d.partSize i) ((d.partSize_le i).trans hj) 0 0
          (Nat.zero_le s) q hq (F.parameter 0 0 q hq) x hx hlow
          (w ∘ d.emb i) (fun l => hw _) R hR hhigh (fun l => hwhigh _)
        simpa only [J0, SmoothDirections.congr, Nat.add_zero, Nat.cast_zero, zero_div,
          Real.rpow_zero, mul_one,
          parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos i)),
          mul_comm, mul_left_comm, mul_assoc] using hh)
    simpa only [B0, C0, mul_pow, Real.rpow_mul_natCast hEpos.le,
      mul_assoc] using hb
  let ra (c : OrderedFinpartition (a + b)) (i : Fin c.length) : ℕ :=
    coordinateRadialOrder (cylinderMixedWord a b ∘ c.emb i)
  let an (c : OrderedFinpartition (a + b)) (i : Fin c.length) : ℕ :=
    coordinateAngularOrder (cylinderMixedWord a b ∘ c.emb i)
  have horder (c : OrderedFinpartition (a + b)) (i : Fin c.length) :
      ra c i + an c i = c.partSize i := coordinateOrders_sum _
  let ff (c : OrderedFinpartition (a + b)) : Fin (c.length + 1) → X → ℝ :=
    Fin.cons (fun y => iteratedDeriv c.length g (f y q))
      (fun i y => mixedDerivative (ra c i) (an c i) (f y) q)
  let JJ (c : OrderedFinpartition (a + b)) :
      ∀ i, SmoothDirections U (ff c i) :=
    Fin.cases (JO c.length) (fun i => F.parameter (ra c i) (an c i) q hq)
  let JT (c : OrderedFinpartition (a + b)) :=
    smoothDirections_finiteProduct hU (JJ c)
  let W : ℝ := E q ^ (Af * (N + s)) * parameterHeightWeight (H q) k *
    R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hEpos.le _)
      (parameterHeightWeight_nonneg (hH q hq).1 k))
    (Real.rpow_nonneg hRpos.le _)
  have hterm (c : OrderedFinpartition (a + b)) :
      ‖(JT c).D k x v‖ ≤ Cp * C0 * Cf ^ s * W := by
    have hm : c.length ≤ s := c.length_le.trans hab
    let B : Fin (c.length + 1) → ℝ := Fin.cons B0
      (fun i => Cf * E q ^ Af * R ^ ((c.partSize i : ℝ) / ((s : ℝ) + 1)))
    have hB : ∀ i, 0 < B i := Fin.cases hB0 (fun i =>
      mul_pos (mul_pos (zero_lt_one.trans_le hCf) (Real.rpow_pos_of_pos hEpos _))
        (Real.rpow_pos_of_pos hRpos _))
    have hbase : ∀ i, ‖ff c i x‖ ≤ B i := by
      refine Fin.cases ?_ (fun i => ?_)
      · have hh := hOJ c.length hm 0 (Nat.zero_le N) Fin.elim0
          (fun i => i.elim0) (fun i => i.elim0)
        rw [(JO c.length).zero x hx] at hh
        simpa only [ff, B, Fin.cons_zero,
          parameterHeightWeight, ite_true, mul_one] using hh
      · have hh := hfb 0 (Nat.zero_le N) (ra c i) (an c i)
          ((horder c i).le.trans ((c.partSize_le i).trans hab))
          q hq (F.parameter (ra c i) (an c i) q hq) x hx hlow
          Fin.elim0 (fun j => j.elim0) R hR hhigh (fun j => j.elim0)
        rw [(F.parameter (ra c i) (an c i) q hq).zero x hx] at hh
        simpa only [ff, B, Fin.cons_succ, horder, parameterHeightWeight,
          ite_true, mul_one] using hh
    have hjet : ∀ i (d : OrderedFinpartition k) (j : Fin d.length),
        ‖(JJ c i).D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H q * B i := by
      refine Fin.cases ?_ (fun i => ?_)
      · intro d j
        have hh := hOJ c.length hm (d.partSize j) ((d.partSize_le j).trans hk)
          (v ∘ d.emb j) (fun i => hv _) (fun i => hvhigh _)
        simpa only [JJ, Fin.cases_zero, B, Fin.cons_zero,
          parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
          mul_comm] using hh
      · intro d j
        have hh := hfb (d.partSize j) ((d.partSize_le j).trans hk) (ra c i) (an c i)
          ((horder c i).le.trans ((c.partSize_le i).trans hab))
          q hq (F.parameter (ra c i) (an c i) q hq) x hx hlow
          (v ∘ d.emb j) (fun l => hv _) R hR hhigh (fun l => hvhigh _)
        simpa only [JJ, Fin.cases_succ, B, Fin.cons_succ, horder,
          parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
          mul_comm, mul_left_comm, mul_assoc] using hh
    have hsum : (∑ i : Fin c.length, (c.partSize i : ℝ) / ((s : ℝ) + 1)) =
        ((a + b : ℕ) : ℝ) / ((s : ℝ) + 1) := by
      rw [← Finset.sum_div, ← Nat.cast_sum, orderedFinpartition_sum_partSize]
    have hprodEq : (∏ i, B i) =
        C0 * Cf ^ c.length * E q ^ (Af * N + Af * c.length) *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      rw [Fin.prod_univ_succ]
      simp only [B, Fin.cons_zero, Fin.cons_succ]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
      rw [← Real.rpow_sum_of_pos hRpos, hsum, ← Real.rpow_mul_natCast hEpos.le]
      dsimp only [B0]
      rw [Real.rpow_add hEpos]
      ring
    have hprod :
        (∏ i, B i) ≤ C0 * Cf ^ s * E q ^ (Af * (N + s)) *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      rw [hprodEq]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hRpos.le _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hCf hm) (zero_le_one.trans hC0)
      · apply Real.rpow_le_rpow_of_exponent_le (hE q hq)
        have hh : (c.length : ℝ) ≤ s := by exact_mod_cast hm
        nlinarith
      · exact Real.rpow_nonneg hEpos.le _
      · positivity
    let idx : Fin (s + 2) × Fin (N + 1) :=
      (⟨c.length + 1, by omega⟩, ⟨k, Nat.lt_succ_of_le hk⟩)
    have hb := hcpb idx (JJ c) (JT c) x hx (H q) (hH q hq).1 (hH q hq).2
      B hB hbase v hjet
    have hprod0 : 0 ≤ ∏ i, B i := Finset.prod_nonneg (fun i _ => (hB i).le)
    calc
      _ ≤ cp idx * parameterHeightWeight (H q) k * ∏ i, B i := hb
      _ ≤ Cp * parameterHeightWeight (H q) k *
          (C0 * Cf ^ s * E q ^ (Af * (N + s)) *
            R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (hcpCp idx) (parameterHeightWeight_nonneg (hH q hq).1 k))
          hprod hprod0
          (mul_nonneg (zero_le_one.trans hCp) (parameterHeightWeight_nonneg (hH q hq).1 k))
      _ = _ := by dsimp only [W]; ring
  have hd := smoothDirections_D_eq_linearCombination J JT (fun _ => 1)
    (fun y hy => by
      simp only [one_mul, ff, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      exact mixedDerivative_scalarComp_ordered hΩ hV (F.spatial y hy) hg
        (fun z hz => hKV (hmap y hy hz)) a b hq)
    k hx v
  calc
    _ ≤ ∑ c : OrderedFinpartition (a + b), ‖(JT c).D k x v‖ := by
      rw [hd]
      simpa only [one_mul] using
        (norm_sum_le (Finset.univ : Finset (OrderedFinpartition (a + b)))
          (fun c : OrderedFinpartition (a + b) => (1 : ℝ) * (JT c).D k x v))
    _ ≤ ∑ _c : OrderedFinpartition (a + b), Cp * C0 * Cf ^ s * W :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ ≤ Q * (Cp * C0 * Cf ^ s * W) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hcardQ (a + b) hab)
        (mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hCp)
          (zero_le_one.trans hC0)) (pow_nonneg (zero_le_one.trans hCf) _)) hW)
    _ = _ := by dsimp only [C, W]; ring


end ContinuousFlexibility.Analysis
