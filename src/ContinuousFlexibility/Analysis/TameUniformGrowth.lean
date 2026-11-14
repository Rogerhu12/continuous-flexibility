module

public import ContinuousFlexibility.Analysis.TameJetLocalBounds

/-!
# Fixed-order growth on arbitrary bounded low-seminorm sets

The low order and derivative loss are chosen before the radius of the
bounded set and before the output order. These quantitative bounds are
closed under finite algebra and composition. For genuine multilinear
jets, normalization recovers a homogeneous one-high-factor estimate
with the same uniform choice of low order and loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- A quantitative value bound; no regularity is assumed by this predicate. -/
def HasUniformLowGrowth (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (f : E → F) : Prop :=
  ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, p base x ≤ K → q s (f x) ≤ C * (1 + p (s + loss) x)

theorem HasUniformLowGrowth.congr
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {f g : E → F}
    (hf : HasUniformLowGrowth p q f) (heq : ∀ x, g x = f x) :
    HasUniformLowGrowth p q g := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb K hK s
  exact ⟨C, hC, fun x hx => (heq x).symm ▸ hc x hx⟩

theorem HasUniformLowGrowth.of_le
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {f g : E → F}
    (hf : HasUniformLowGrowth p q f) (hle : ∀ s x, q s (g x) ≤ q s (f x)) :
    HasUniformLowGrowth p q g := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb K hK s
  exact ⟨C, hC, fun x hx => (hle s x).trans (hc x hx)⟩

theorem uniformLowGrowth_of_grading_contraction
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (f : E → F)
    (hb : ∀ s x, q s (f x) ≤ p s x) : HasUniformLowGrowth p q f := by
  refine ⟨0, 0, fun K hK s => ⟨1, zero_le_one, fun x hx => ?_⟩⟩
  simpa only [Nat.add_zero, one_mul] using
    (hb s x).trans (le_add_of_nonneg_left zero_le_one)

theorem uniformLowGrowth_const
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (y : F) :
    HasUniformLowGrowth p q (fun _ => y) := by
  refine ⟨0, 0, fun K hK s => ⟨q s y, apply_nonneg _ _, fun x hx => ?_⟩⟩
  exact le_mul_of_one_le_right (apply_nonneg _ _)
    (le_add_of_nonneg_right (apply_nonneg _ _))

theorem uniformLowGrowth_of_zeroLoss
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (L : E →L[ℝ] F) (hL : IsTameLinear p q L.toLinearMap 0 0) :
    HasUniformLowGrowth p q L := by
  refine ⟨0, 0, fun K hK s => ?_⟩
  obtain ⟨C, hc⟩ := hL s (Nat.zero_le s)
  refine ⟨C, C.coe_nonneg, fun x hx => ?_⟩
  exact (hc x).trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left zero_le_one) C.coe_nonneg)

theorem HasUniformLowGrowth.comp
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ G} {f : E → F} {g : F → G}
    (hg : HasUniformLowGrowth q r g) (hp : Monotone p)
    (hf : HasUniformLowGrowth p q f) : HasUniformLowGrowth p r (g ∘ f) := by
  obtain ⟨bf, lf, hfb⟩ := hf
  obtain ⟨bg, lg, hgb⟩ := hg
  refine ⟨max bf (bg + lf), lf + lg, ?_⟩
  intro K hK
  obtain ⟨D, hD, hd⟩ := hfb K hK bg
  let L : ℝ := D * (1 + K)
  have hL : 0 ≤ L := mul_nonneg hD (add_nonneg zero_le_one hK)
  intro s
  obtain ⟨Cg, hCg, hcg⟩ := hgb L hL s
  obtain ⟨Cf, hCf, hcf⟩ := hfb K hK (s + lg)
  refine ⟨Cg * (1 + Cf), mul_nonneg hCg (add_nonneg zero_le_one hCf), ?_⟩
  intro x hx
  have hx' : p bf x ≤ K := (hp (le_max_left bf (bg + lf)) x).trans hx
  have hlow : q bg (f x) ≤ L := (hd x hx').trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((hp (le_max_right bf (bg + lf)) x).trans hx)) hD)
  have hinner : q (s + lg) (f x) ≤ Cf * (1 + p (s + (lf + lg)) x) := by
    simpa only [Nat.add_assoc, Nat.add_comm lg lf] using hcf x hx'
  calc
    r s ((g ∘ f) x) ≤ Cg * (1 + q (s + lg) (f x)) := hcg (f x) hlow
    _ ≤ Cg * (1 + Cf * (1 + p (s + (lf + lg)) x)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hinner) hCg
    _ ≤ Cg * ((1 + Cf) * (1 + p (s + (lf + lg)) x)) := by
      apply mul_le_mul_of_nonneg_left _ hCg
      nlinarith [apply_nonneg (p (s + (lf + lg))) x]
    _ = _ := by ring

theorem HasUniformLowGrowth.add
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {f g : E → F} (hf : HasUniformLowGrowth p q f) (hp : Monotone p)
    (hg : HasUniformLowGrowth p q g) :
    HasUniformLowGrowth p q (fun x => f x + g x) := by
  obtain ⟨bf, lf, hfb⟩ := hf
  obtain ⟨bg, lg, hgb⟩ := hg
  refine ⟨max bf bg, max lf lg, fun K hK s => ?_⟩
  obtain ⟨Cf, hCf, hcf⟩ := hfb K hK s
  obtain ⟨Cg, hCg, hcg⟩ := hgb K hK s
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun x hx => ?_⟩
  have hf' : q s (f x) ≤ Cf * (1 + p (s + max lf lg) x) :=
    (hcf x ((hp (le_max_left bf bg) x).trans hx)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_left lf lg) s) x)) hCf)
  have hg' : q s (g x) ≤ Cg * (1 + p (s + max lf lg) x) :=
    (hcg x ((hp (le_max_right bf bg) x).trans hx)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right lf lg) s) x)) hCg)
  exact (map_add_le_add (q s) (f x) (g x)).trans
    ((add_le_add hf' hg').trans_eq (by ring))

theorem HasUniformLowGrowth.prodMk
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ G} {f : E → F} {g : E → G}
    (hf : HasUniformLowGrowth p q f) (hp : Monotone p)
    (hg : HasUniformLowGrowth p r g) :
    HasUniformLowGrowth p (pairGrading q r) (fun x => (f x, g x)) := by
  obtain ⟨bf, lf, hfb⟩ := hf
  obtain ⟨bg, lg, hgb⟩ := hg
  refine ⟨max bf bg, max lf lg, fun K hK s => ?_⟩
  obtain ⟨Cf, hCf, hcf⟩ := hfb K hK s
  obtain ⟨Cg, hCg, hcg⟩ := hgb K hK s
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun x hx => ?_⟩
  rw [pairGrading_apply]
  have hf' : q s (f x) ≤ Cf * (1 + p (s + max lf lg) x) :=
    (hcf x ((hp (le_max_left bf bg) x).trans hx)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_left lf lg) s) x)) hCf)
  have hg' : r s (g x) ≤ Cg * (1 + p (s + max lf lg) x) :=
    (hcg x ((hp (le_max_right bf bg) x).trans hx)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right lf lg) s) x)) hCg)
  exact (add_le_add hf' hg').trans_eq (by ring)

theorem HasUniformLowGrowth.neg
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {f : E → F}
    (hf : HasUniformLowGrowth p q f) : HasUniformLowGrowth p q (fun x => -f x) := by
  obtain ⟨base, loss, hb⟩ := hf
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb K hK s
  exact ⟨C, hC, fun x hx => by simpa only [map_neg_eq_map] using hc x hx⟩

theorem HasUniformLowGrowth.pi
    {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℝ (Y i)]
    {p : ℕ → Seminorm ℝ E} {q : ∀ i, ℕ → Seminorm ℝ (Y i)}
    (hp : Monotone p) {f : ∀ i, E → Y i}
    (hf : ∀ i, HasUniformLowGrowth p (q i) (f i)) :
    HasUniformLowGrowth p (tupleGrading q) (fun x i => f i x) := by
  classical
  choose b l hb using hf
  let base : ℕ := Finset.univ.sup b
  let loss : ℕ := Finset.univ.sup l
  have hbase (i : ι) : b i ≤ base := Finset.le_sup (Finset.mem_univ i)
  have hloss (i : ι) : l i ≤ loss := Finset.le_sup (Finset.mem_univ i)
  refine ⟨base, loss, fun K hK s => ?_⟩
  choose C hC hc using fun i => hb i K hK s
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun x hx => ?_⟩
  rw [tupleGrading_apply, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact (hc i x ((hp (hbase i) x).trans hx)).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (Nat.add_le_add_left (hloss i) s) x)) (hC i))

theorem HasUniformLowGrowth.finset_sum
    {ι : Type*} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (I : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ I, HasUniformLowGrowth p q (f i)) :
    HasUniformLowGrowth p q (fun x => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using uniformLowGrowth_const p q (0 : F)
  | @insert i I hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i I)).add hp
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem uniformLowGrowth_pair_fst
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    HasUniformLowGrowth (pairGrading p q) p (Prod.fst : E × F → E) := by
  apply uniformLowGrowth_of_grading_contraction
  intro s x
  rw [pairGrading_apply]
  exact le_add_of_nonneg_right (apply_nonneg _ _)

theorem uniformLowGrowth_pair_snd
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    HasUniformLowGrowth (pairGrading p q) q (Prod.snd : E × F → F) := by
  apply uniformLowGrowth_of_grading_contraction
  intro s x
  rw [pairGrading_apply]
  exact le_add_of_nonneg_left (apply_nonneg _ _)

theorem uniformLowGrowth_jet_base (p : ℕ → Seminorm ℝ E) (n : ℕ) :
    HasUniformLowGrowth (jetGrading p n) p
      (Prod.fst : E × (Fin n → E) → E) := by
  apply uniformLowGrowth_of_grading_contraction
  intro s x
  rw [jetGrading_apply]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))

theorem uniformLowGrowth_jet_direction (p : ℕ → Seminorm ℝ E) (n : ℕ) (i : Fin n) :
    HasUniformLowGrowth (jetGrading p n) p
      (fun x : E × (Fin n → E) => x.2 i) := by
  apply uniformLowGrowth_of_grading_contraction
  intro s x
  rw [jetGrading_apply]
  exact (Finset.single_le_sum (f := fun j => p s (x.2 j))
    (fun _ _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (apply_nonneg _ _))

/-- Uniform joint growth of an actual multilinear family yields the
homogeneous bound on every bounded low-seminorm set of base points. -/
theorem uniformLowGrowth_multilinear_oneHigh
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {n : ℕ}
    (A : E → E [×n]→L[ℝ] F)
    (hg : HasUniformLowGrowth (jetGrading p n) q (fun z => A z.1 z.2)) :
    ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ K → ∀ v : Fin n → E,
        q s (A x v) ≤ C * tameJetSize p n s loss base x v := by
  obtain ⟨base, loss, hb⟩ := hg
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb (K + n) (add_nonneg hK (Nat.cast_nonneg n)) s
  refine ⟨C, hC, fun x hx v => ?_⟩
  have hlocal (w : Fin n → E) (hw : ∀ i, p base (w i) < 1) :
      q s (A x w) ≤ C * ((1 + p (s + loss) x) + ∑ i, p (s + loss) (w i)) := by
    have hsum : (∑ i, p base (w i)) ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hw i).le)
        _ = _ := by simp
    have hbox : jetGrading p n base (x, w) ≤ K + n := by
      rw [jetGrading_apply]
      exact add_le_add hx hsum
    simpa only [jetGrading_apply, add_assoc] using hc (x, w) hbox
  exact multilinear_bound_of_unitBall (A x) (q s) (p base) (p (s + loss)) hC hlocal v

/-- A globally estimated expression need agree with the genuine jet only
on the actual open domain. Bounds outside that domain are not assumed
for the derivative tower. -/
theorem uniformLowGrowth_multilinear_oneHigh_on
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {n : ℕ} {U : Set E}
    (A : E → E [×n]→L[ℝ] F) {g : E × (Fin n → E) → F}
    (hg : HasUniformLowGrowth (jetGrading p n) q g)
    (heq : ∀ x ∈ U, ∀ v, A x v = g (x, v)) :
    ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, p base x ≤ K → ∀ v : Fin n → E,
        q s (A x v) ≤ C * tameJetSize p n s loss base x v := by
  obtain ⟨base, loss, hb⟩ := hg
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb (K + n) (add_nonneg hK (Nat.cast_nonneg n)) s
  refine ⟨C, hC, fun x hx hlow v => ?_⟩
  have hlocal (w : Fin n → E) (hw : ∀ i, p base (w i) < 1) :
      q s (A x w) ≤ C * ((1 + p (s + loss) x) + ∑ i, p (s + loss) (w i)) := by
    have hsum : (∑ i, p base (w i)) ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hw i).le)
        _ = _ := by simp
    have hbox : jetGrading p n base (x, w) ≤ K + n := by
      rw [jetGrading_apply]
      exact add_le_add hlow hsum
    rw [heq x hx w]
    simpa only [jetGrading_apply, add_assoc] using hc (x, w) hbox
  exact multilinear_bound_of_unitBall (A x) (q s) (p base) (p (s + loss)) hC hlocal v

end ContinuousFlexibility.Analysis
