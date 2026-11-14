module

public import ContinuousFlexibility.Analysis.N07aNormalExpansionBound
public import ContinuousFlexibility.Analysis.N07aFiniteOneHighProduct
public import ContinuousFlexibility.Analysis.N07aSampleJetBounds

/-!
# One fixed tame loss for the complete normal expansion

The terminal estimates concern only the original source and solution
jets with at most one normal derivative. Every coefficient product is
interpolated as a whole. Its sampled envelope is retained until after
the entire finite normal expansion is summed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

theorem n07a_normalExpansion_fixedLoss
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q) (hIp : HasSmoothing p) (hIq : HasSmoothing q)
    (U : Set E) (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 ≤ w c m)
    (A : Fin 6 → E → ℕ → PolarPoint → ℝ)
    (u f : E → F → ℕ → PolarPoint → ℝ) (dA low df : ℕ)
    (hA : ∀ i, N07aSampleJetBounds T K p U (canonicalOpen S K) dA (A i))
    (hAs : ∀ i z, z ∈ U → ∀ m, ContDiffOn ℝ ∞ (A i z m) (canonicalOpen S K m))
    (hus : ∀ z ∈ U, ∀ v m, ContDiffOn ℝ ∞ (u z v m) (canonicalOpen S K m))
    (hfs : ∀ z ∈ U, ∀ v m, ContDiffOn ℝ ∞ (f z v m) (canonicalOpen S K m))
    (heq : ∀ z ∈ U, ∀ v m,
      EqOn (mixedDerivative 2 0 (u z v m))
        (n07aNormalRhs (fun i => A i z m) (u z v m) (f z v m)) (canonicalOpen S K m))
    (hterminal : ∀ source : Bool, ∀ a b : ℕ, (source = false → a ≤ 1) →
      ∀ c : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ v m,
          eLpNorm (mixedDerivative a b (if source then f z v m else u z v m))
            2 (canonicalMeasure S K m) ≤
              ENNReal.ofReal (e m * w c m *
                (q (c + (a + b) + df) v +
                  (1 + p (c + (a + b) + df) z) * q low v))) :
    ∃ low' loss : ℕ, ∀ a b c : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, p low' z ≤ 1 → ∀ v m,
          eLpNorm (mixedDerivative a b (u z v m)) 2 (canonicalMeasure S K m) ≤
            ENNReal.ofReal (e m * w c m *
              (q (c + (a + b) + loss) v +
                (1 + p (c + (a + b) + loss) z) * q low' v)) := by
  classical
  let d := max dA (max df low)
  have hdA : dA ≤ d := le_max_left _ _
  have hdf : df ≤ d := (le_max_left df low).trans (le_max_right _ _)
  have hdl : low ≤ d := (le_max_right df low).trans (le_max_right _ _)
  obtain ⟨low', loss, hprod⟩ := n07a_list_oneHigh_source_product p q hp hq hIp hIq d
  refine ⟨low', loss, fun a b c => ?_⟩
  let J := n07aNormalExpansion a b
  let I := {t : N07aNormalTerm // t ∈ J}
  have hsafe (i : I) : i.val.Safe (a + b) :=
    n07aNormalExpansion_safe a b i.val i.property
  choose eA heA heA0 heAb using fun j : N07aNormalAtom =>
    hA j.coefficient j.radial j.angular
  choose eT heT heT0 heTb using fun i : I =>
    hterminal i.val.source i.val.radial i.val.angular (hsafe i).1 c
  have hbudget (i : I) : c + (i.val.radial + i.val.angular) +
      (i.val.atoms.map (fun j => j.radial + j.angular)).sum ≤ c + (a + b) := by
    have h := (hsafe i).2
    dsimp only [N07aNormalTerm.order] at h
    omega
  choose C hC hCb using fun i : I => hprod
    (i.val.atoms.map (fun j => j.radial + j.angular))
    (c + (i.val.radial + i.val.angular)) (c + (a + b)) (hbudget i)
  let eProd : N07aNormalTerm → ℕ → ℝ :=
    fun t m => (t.atoms.map (fun j => eA j m)).prod
  have heProd (t : N07aNormalTerm) : N07aSampleSubpower T K (eProd t) :=
    N07aSampleSubpower.list_prod hD hT t.atoms eA (fun j _ => heA j)
  have heProd0 (t : N07aNormalTerm) (m : ℕ) : 0 ≤ eProd t m := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact heA0 j m
  let e : I → ℕ → ℝ :=
    fun i m => |i.val.scalar| * eProd i.val m * eT i m * C i
  have he (i : I) : N07aSampleSubpower T K (e i) :=
    N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT
        (N07aSampleSubpower.mul hD hT
          (N07aSampleSubpower.const hD hT |i.val.scalar|) (heProd i.val))
        (heT i)) (N07aSampleSubpower.const hD hT (C i))
  have he0 (i : I) (m : ℕ) : 0 ≤ e i m :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (heProd0 i.val m)) (heT0 i m))
      (hC i)
  refine ⟨fun m => (J.attach.map (fun i => e i m)).sum,
    N07aSampleSubpower.list_sum hD hT J.attach e (fun i _ => he i),
    fun m => List.sum_nonneg (fun x hx => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact he0 i m), ?_⟩
  intro z hz hlow v m
  let B := q (c + (a + b) + loss) v + (1 + p (c + (a + b) + loss) z) * q low' v
  let cb : N07aNormalAtom → ℝ :=
    fun j => eA j m * (1 + p (j.radial + j.angular + d) z)
  have hcb0 (j : N07aNormalAtom) : 0 ≤ cb j :=
    mul_nonneg (heA0 j m) (add_nonneg zero_le_one (apply_nonneg _ _))
  have hcb (j : N07aNormalAtom) (x : PolarPoint) (hx : x ∈ canonicalOpen S K m) :
      |j.value (fun i => A i z m) x| ≤ cb j :=
    (heAb j z hz m x hx).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (Nat.add_le_add_left hdA _) z)) (heA0 j m))
  let N : Bool → ℕ → ℕ → ℝ := fun source ar an =>
    (eLpNorm (mixedDerivative ar an (if source then f z v m else u z v m))
      2 (canonicalMeasure S K m)).toReal
  have hN0 (source : Bool) (ar an : ℕ) : 0 ≤ N source ar an := ENNReal.toReal_nonneg
  have hterminalReal (i : I) : N i.val.source i.val.radial i.val.angular ≤
      eT i m * w c m * (q (c + (i.val.radial + i.val.angular) + d) v +
        (1 + p (c + (i.val.radial + i.val.angular) + d) z) * q d v) := by
    have hbound := heTb i z hz v m
    have hb0 : 0 ≤ eT i m * w c m *
        (q (c + (i.val.radial + i.val.angular) + df) v +
          (1 + p (c + (i.val.radial + i.val.angular) + df) z) * q low v) :=
      mul_nonneg (mul_nonneg (heT0 i m) (hw c m))
        (add_nonneg (apply_nonneg _ _)
          (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _)))
    apply (ENNReal.toReal_le_of_le_ofReal hb0 hbound).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (heT0 i m) (hw c m))
    exact add_le_add (hq (Nat.add_le_add_left hdf _) v)
      (mul_le_mul (add_le_add le_rfl (hp (Nat.add_le_add_left hdf _) z))
        (hq hdl v) (apply_nonneg _ _) (add_nonneg zero_le_one (apply_nonneg _ _)))
  have hmain := n07a_normalExpansion_eLpNorm_bound
    (fun i => hAs i z hz m) (hus z hz v m) (hfs z hz v m) (heq z hz v m)
    cb hcb0 hcb N hN0 a b (fun t ht => by
      have htop := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heTb ⟨t, ht⟩ z hz v m)
      exact (ENNReal.ofReal_toReal htop).symm.le)
  have hterm (i : I) : n07aNormalTermAmplitude cb i.val *
      N i.val.source i.val.radial i.val.angular ≤ e i m * w c m * B := by
    have hpB :
        (q (c + (i.val.radial + i.val.angular) + d) v +
          (1 + p (c + (i.val.radial + i.val.angular) + d) z) * q d v) *
          (i.val.atoms.map (fun j => 1 + p (j.radial + j.angular + d) z)).prod ≤
            C i * B := by
      simpa only [List.map_map, Function.comp_def] using hCb i z hlow v
    calc
      _ ≤ n07aNormalTermAmplitude cb i.val *
          (eT i m * w c m * (q (c + (i.val.radial + i.val.angular) + d) v +
            (1 + p (c + (i.val.radial + i.val.angular) + d) z) * q d v)) :=
        mul_le_mul_of_nonneg_left (hterminalReal i) (n07aNormalTermAmplitude_nonneg cb hcb0 i.val)
      _ = (|i.val.scalar| * eProd i.val m * eT i m * w c m) *
          ((q (c + (i.val.radial + i.val.angular) + d) v +
            (1 + p (c + (i.val.radial + i.val.angular) + d) z) * q d v) *
              (i.val.atoms.map (fun j => 1 + p (j.radial + j.angular + d) z)).prod) := by
        dsimp only [n07aNormalTermAmplitude, cb, eProd]
        rw [List.prod_map_mul]
        ring
      _ ≤ (|i.val.scalar| * eProd i.val m * eT i m * w c m) * (C i * B) :=
        mul_le_mul_of_nonneg_left hpB
          (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (heProd0 i.val m)) (heT0 i m))
            (hw c m))
      _ = _ := by dsimp only [e]; ring
  have hsum := List.sum_le_sum (l := J.attach) (fun i _ => hterm i)
  have hattach : (J.attach.map (fun i => n07aNormalTermAmplitude cb i.val *
      N i.val.source i.val.radial i.val.angular)).sum =
      (J.map (fun t => n07aNormalTermAmplitude cb t * N t.source t.radial t.angular)).sum :=
    congrArg List.sum (List.attach_map_val (l := J)
      (f := fun t : N07aNormalTerm => n07aNormalTermAmplitude cb t *
        N t.source t.radial t.angular))
  rw [hattach] at hsum
  apply hmain.trans (ENNReal.ofReal_le_ofReal (hsum.trans_eq ?_))
  rw [List.sum_map_mul_right, List.sum_map_mul_right]

end ContinuousFlexibility.Analysis
