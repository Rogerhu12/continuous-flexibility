import ContinuousFlexibility.Analysis.TameUniformGrowth

/-!
# Uniform bounded-low-seminorm estimates for indexed actual maps

The index may be an arbitrary radius selector. The low order and loss
precede the radius and output order, and the numerical constant precedes
the selector. These are estimates of specified functions on a specified
domain, with no smoothness or derivative hypotheses hidden in the
definition. Finite algebra and composition retain this order of choices.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

def HasUniformFamilyLowGrowthOn
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (f : I → E → F) : Prop :=
  ∃ base loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ i x, x ∈ U → p base x ≤ R → q s (f i x) ≤ C * (1 + p (s + loss) x)

theorem HasUniformLowGrowth.uniformFamilyOn
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {f : E → F}
    (hf : HasUniformLowGrowth p q f) (U : Set E) :
    HasUniformFamilyLowGrowthOn p q U (fun _ : I => f) := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR s
  exact ⟨C, hC, fun _ x _ hx => hc x hx⟩

theorem HasUniformFamilyLowGrowthOn.congr
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : HasUniformFamilyLowGrowthOn p q U f)
    (heq : ∀ i x, x ∈ U → g i x = f i x) :
    HasUniformFamilyLowGrowthOn p q U g := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR s
  exact ⟨C, hC, fun i x hx hlow => (heq i x hx).symm ▸ hc i x hx hlow⟩

theorem HasUniformFamilyLowGrowthOn.mono
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U V : Set E}
    {f : I → E → F} (hf : HasUniformFamilyLowGrowthOn p q U f) (hVU : V ⊆ U) :
    HasUniformFamilyLowGrowthOn p q V f := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR s
  exact ⟨C, hC, fun i x hx hlow => hc i x (hVU hx) hlow⟩

theorem HasUniformFamilyLowGrowthOn.reindex
    {K : Type*} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : HasUniformFamilyLowGrowthOn p q U f) (a : K → I) :
    HasUniformFamilyLowGrowthOn p q U (fun k => f (a k)) := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR s
  exact ⟨C, hC, fun k x hx hlow => hc (a k) x hx hlow⟩

theorem uniformFamilyLowGrowthOn_of_bound
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (U : Set E)
    (f : I → E → F) (loss : ℕ)
    (hb : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U →
      q s (f i x) ≤ C * p (s + loss) x) :
    HasUniformFamilyLowGrowthOn p q U f := by
  refine ⟨0, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb s
  exact ⟨C, hC, fun i x hx _ => (hc i x hx).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hC)⟩

theorem uniformFamilyLowGrowthOn_of_contraction
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (U : Set E)
    (f : I → E → F) (hb : ∀ s i x, x ∈ U → q s (f i x) ≤ p s x) :
    HasUniformFamilyLowGrowthOn p q U f := by
  apply uniformFamilyLowGrowthOn_of_bound p q U f 0
  exact fun s => ⟨1, zero_le_one, fun i x hx => by
    simpa only [Nat.add_zero, one_mul] using hb s i x hx⟩

theorem HasUniformFamilyLowGrowthOn.comp
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {V : Set F} {f : I → E → F} {g : I → F → G}
    (hg : HasUniformFamilyLowGrowthOn q r V g) (hp : Monotone p)
    (hf : HasUniformFamilyLowGrowthOn p q U f) (hmap : ∀ i, MapsTo (f i) U V) :
    HasUniformFamilyLowGrowthOn p r U (fun i x => g i (f i x)) := by
  obtain ⟨bf, lf, hfb⟩ := hf
  obtain ⟨bg, lg, hgb⟩ := hg
  refine ⟨max bf (bg + lf), lf + lg, ?_⟩
  intro R hR
  obtain ⟨D, hD, hd⟩ := hfb R hR bg
  let K : ℝ := D * (1 + R)
  have hK : 0 ≤ K := mul_nonneg hD (add_nonneg zero_le_one hR)
  intro s
  obtain ⟨Cg, hCg, hcg⟩ := hgb K hK s
  obtain ⟨Cf, hCf, hcf⟩ := hfb R hR (s + lg)
  refine ⟨Cg * (1 + Cf), mul_nonneg hCg (add_nonneg zero_le_one hCf), ?_⟩
  intro i x hx hlow
  have hx' : p bf x ≤ R := (hp (le_max_left bf (bg + lf)) x).trans hlow
  have hinnerLow : q bg (f i x) ≤ K := (hd i x hx hx').trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((hp (le_max_right bf (bg + lf)) x).trans hlow)) hD)
  have hinner : q (s + lg) (f i x) ≤ Cf * (1 + p (s + (lf + lg)) x) := by
    simpa only [Nat.add_assoc, Nat.add_comm lg lf] using hcf i x hx hx'
  calc
    r s (g i (f i x)) ≤ Cg * (1 + q (s + lg) (f i x)) :=
      hcg i (f i x) (hmap i hx) hinnerLow
    _ ≤ Cg * (1 + Cf * (1 + p (s + (lf + lg)) x)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hinner) hCg
    _ ≤ Cg * ((1 + Cf) * (1 + p (s + (lf + lg)) x)) := by
      apply mul_le_mul_of_nonneg_left _ hCg
      nlinarith [apply_nonneg (p (s + (lf + lg))) x]
    _ = _ := by ring

theorem HasUniformFamilyLowGrowthOn.add
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : HasUniformFamilyLowGrowthOn p q U f)
    (hp : Monotone p) (hg : HasUniformFamilyLowGrowthOn p q U g) :
    HasUniformFamilyLowGrowthOn p q U (fun i x => f i x + g i x) := by
  obtain ⟨bf, lf, hfb⟩ := hf
  obtain ⟨bg, lg, hgb⟩ := hg
  refine ⟨max bf bg, max lf lg, fun R hR s => ?_⟩
  obtain ⟨Cf, hCf, hcf⟩ := hfb R hR s
  obtain ⟨Cg, hCg, hcg⟩ := hgb R hR s
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun i x hx hlow => ?_⟩
  have hf' : q s (f i x) ≤ Cf * (1 + p (s + max lf lg) x) :=
    (hcf i x hx ((hp (le_max_left bf bg) x).trans hlow)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_left lf lg) s) x)) hCf)
  have hg' : q s (g i x) ≤ Cg * (1 + p (s + max lf lg) x) :=
    (hcg i x hx ((hp (le_max_right bf bg) x).trans hlow)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right lf lg) s) x)) hCg)
  exact (map_add_le_add (q s) (f i x) (g i x)).trans
    ((add_le_add hf' hg').trans_eq (by ring))

theorem HasUniformFamilyLowGrowthOn.prodMk
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} {g : I → E → G}
    (hf : HasUniformFamilyLowGrowthOn p q U f) (hp : Monotone p)
    (hg : HasUniformFamilyLowGrowthOn p r U g) :
    HasUniformFamilyLowGrowthOn p (pairGrading q r) U (fun i x => (f i x, g i x)) := by
  obtain ⟨bf, lf, hfb⟩ := hf
  obtain ⟨bg, lg, hgb⟩ := hg
  refine ⟨max bf bg, max lf lg, fun R hR s => ?_⟩
  obtain ⟨Cf, hCf, hcf⟩ := hfb R hR s
  obtain ⟨Cg, hCg, hcg⟩ := hgb R hR s
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun i x hx hlow => ?_⟩
  rw [pairGrading_apply]
  have hf' : q s (f i x) ≤ Cf * (1 + p (s + max lf lg) x) :=
    (hcf i x hx ((hp (le_max_left bf bg) x).trans hlow)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_left lf lg) s) x)) hCf)
  have hg' : r s (g i x) ≤ Cg * (1 + p (s + max lf lg) x) :=
    (hcg i x hx ((hp (le_max_right bf bg) x).trans hlow)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right lf lg) s) x)) hCg)
  exact (add_le_add hf' hg').trans_eq (by ring)

theorem HasUniformFamilyLowGrowthOn.neg
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : HasUniformFamilyLowGrowthOn p q U f) :
    HasUniformFamilyLowGrowthOn p q U (fun i x => -f i x) := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR s
  exact ⟨C, hC, fun i x hx hlow => by simpa only [map_neg_eq_map] using hc i x hx hlow⟩

theorem HasUniformFamilyLowGrowthOn.pi
    {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℝ (Y i)]
    {p : ℕ → Seminorm ℝ E} {q : ∀ i, ℕ → Seminorm ℝ (Y i)} {U : Set E}
    (hp : Monotone p) {f : ∀ i, I → E → Y i}
    (hf : ∀ i, HasUniformFamilyLowGrowthOn p (q i) U (f i)) :
    HasUniformFamilyLowGrowthOn p (tupleGrading q) U (fun a x i => f i a x) := by
  classical
  choose b l hb using hf
  let base : ℕ := Finset.univ.sup b
  let loss : ℕ := Finset.univ.sup l
  have hbase (i : ι) : b i ≤ base := Finset.le_sup (Finset.mem_univ i)
  have hloss (i : ι) : l i ≤ loss := Finset.le_sup (Finset.mem_univ i)
  refine ⟨base, loss, fun R hR s => ?_⟩
  choose C hC hc using fun i => hb i R hR s
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun a x hx hlow => ?_⟩
  rw [tupleGrading_apply, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact (hc i a x hx ((hp (hbase i) x).trans hlow)).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (Nat.add_le_add_left (hloss i) s) x)) (hC i))

theorem HasUniformFamilyLowGrowthOn.finset_sum
    {ι : Type*} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    (hp : Monotone p) (A : Finset ι) {f : ι → I → E → F}
    (hf : ∀ j ∈ A, HasUniformFamilyLowGrowthOn p q U (f j)) :
    HasUniformFamilyLowGrowthOn p q U (fun i x => ∑ j ∈ A, f j i x) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (uniformLowGrowth_const p q (0 : F)).uniformFamilyOn (I := I) U
  | @insert j A hj ih =>
      simpa only [Finset.sum_insert hj] using
        (hf j (Finset.mem_insert_self j A)).add hp
          (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-- Normalization applies to every member of the actual multilinear
family using one numerical constant chosen before the index. -/
theorem uniformFamilyLowGrowthOn_multilinear_oneHigh
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {n : ℕ} {U : Set E}
    (A : I → E → E [×n]→L[ℝ] F)
    (hg : HasUniformFamilyLowGrowthOn (jetGrading p n) q (U ×ˢ univ)
      (fun i z => A i z.1 z.2)) :
    ∃ base loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ v : Fin n → E,
        q s (A i x v) ≤ C * tameJetSize p n s loss base x v := by
  obtain ⟨base, loss, hb⟩ := hg
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb (R + n) (add_nonneg hR (Nat.cast_nonneg n)) s
  refine ⟨C, hC, fun i x hx hlow v => ?_⟩
  have hlocal (w : Fin n → E) (hw : ∀ j, p base (w j) < 1) :
      q s (A i x w) ≤ C * ((1 + p (s + loss) x) + ∑ j, p (s + loss) (w j)) := by
    have hsum : (∑ j, p base (w j)) ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => (hw j).le)
        _ = _ := by simp
    have hbox : jetGrading p n base (x, w) ≤ R + n := by
      rw [jetGrading_apply]
      exact add_le_add hlow hsum
    simpa only [jetGrading_apply, add_assoc] using hc i (x, w) ⟨hx, mem_univ _⟩ hbox
  exact multilinear_bound_of_unitBall (A i x) (q s) (p base) (p (s + loss)) hC hlocal v

/-- One-high bounds imply joint growth on bounded low boxes, uniformly
in the family index. This is the converse used before finite composition. -/
theorem uniformFamilyLowGrowthOn_of_oneHigh
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {n : ℕ} {U : Set E}
    (A : I → E → (Fin n → E) → F)
    (hb : ∃ base loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ v : Fin n → E,
        q s (A i x v) ≤ C * tameJetSize p n s loss base x v) :
    HasUniformFamilyLowGrowthOn (jetGrading p n) q (U ×ˢ univ)
      (fun i z => A i z.1 z.2) := by
  obtain ⟨base, loss, hb⟩ := hb
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR s
  let M : ℝ := 1 + R
  have hM : 1 ≤ M := le_add_of_nonneg_right hR
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨C * M ^ n, mul_nonneg hC (pow_nonneg hM0 n), ?_⟩
  intro i z hz hlow
  have hlow' : p base z.1 + ∑ j, p base (z.2 j) ≤ R := by
    simpa only [jetGrading_apply] using hlow
  have hx : p base z.1 ≤ R := (le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => apply_nonneg (p base) (z.2 j)))).trans hlow'
  have hv (j : Fin n) : p base (z.2 j) ≤ M := by
    have hs : p base (z.2 j) ≤ ∑ k, p base (z.2 k) :=
      Finset.single_le_sum (f := fun k => p base (z.2 k))
        (fun k _ => apply_nonneg _ _) (Finset.mem_univ j)
    exact (hs.trans ((le_add_of_nonneg_left (apply_nonneg (p base) z.1)).trans hlow')).trans
      (le_add_of_nonneg_left zero_le_one)
  have hprod (A : Finset (Fin n)) : (∏ j ∈ A, p base (z.2 j)) ≤ M ^ n := by
    calc
      _ ≤ ∏ _j ∈ A, M := Finset.prod_le_prod₀
        (fun j _ => apply_nonneg _ _) (fun j _ => hv j)
      _ = M ^ A.card := by simp only [Finset.prod_const]
      _ ≤ M ^ n := pow_le_pow_right₀ hM (by simpa using Finset.card_le_univ A)
  have hsize : tameJetSize p n s loss base z.1 z.2 ≤
      M ^ n * (1 + jetGrading p n (s + loss) z) := by
    unfold tameJetSize
    rw [jetGrading_apply]
    calc
      _ ≤ (1 + p (s + loss) z.1) * M ^ n +
          ∑ j, p (s + loss) (z.2 j) * M ^ n :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hprod Finset.univ)
            (add_nonneg zero_le_one (apply_nonneg _ _)))
          (Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_left (hprod (Finset.univ.erase j)) (apply_nonneg _ _)))
      _ = _ := by rw [← Finset.sum_mul]; ring
  exact (hc i z.1 hz.1 hx z.2).trans
    ((mul_le_mul_of_nonneg_left hsize hC).trans_eq (by ring))

end ContinuousFlexibility.Analysis
