import ContinuousFlexibility.Analysis.MaterialMixedMultiplier
import ContinuousFlexibility.Analysis.PhysicalGradeEnergy
import ContinuousFlexibility.Analysis.CylinderUniformNorm

/-!
# Multiplier estimates with the full mixed derivative budget

An order-k coefficient jet is paired with height order s-k+d, where d
is the fixed material-weight loss. The finite constants depend only on
the output order. In particular, the estimate does not raise every
height factor to the largest order before interpolation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal

theorem weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp
    {T : MaterialData} {γ : ℝ} {u : PolarPoint → ℝ}
    (hLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure)
    {a b c s : ℕ} (horder : a + b + c ≤ s) :
    eLpNorm (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure ≤
      ENNReal.ofReal (physicalNorm T γ s u) := by
  have hfinite : physicalLevelEnergy T γ s u < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro j _
    rw [pow_two]
    exact ENNReal.mul_lt_top (hLp _ _ _) (hLp _ _ _)
  have heq : physicalLevelEnergy T γ s u = ENNReal.ofReal (physicalNorm T γ s u ^ 2) := by
    rw [physicalNorm, Real.sq_sqrt ENNReal.toReal_nonneg]
    exact (ENNReal.ofReal_toReal hfinite.ne).symm
  have he := (weightedPhysicalJet_energy_le_level u horder).trans_eq heq
  have hsq : (eLpNorm (weightedPhysicalJet T γ a b c u) 2
      materialCylinderMeasure).toReal ^ 2 ≤ physicalNorm T γ s u ^ 2 := by
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (sq_nonneg _)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have hnorm : (eLpNorm (weightedPhysicalJet T γ a b c u) 2
      materialCylinderMeasure).toReal ≤ physicalNorm T γ s u := by
    have hpos : 0 ≤ physicalNorm T γ s u := Real.sqrt_nonneg _
    nlinarith [ENNReal.toReal_nonneg
      (a := eLpNorm (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure)]
  calc
    _ = ENNReal.ofReal (eLpNorm (weightedPhysicalJet T γ a b c u) 2
        materialCylinderMeasure).toReal :=
      (ENNReal.ofReal_toReal (hLp a b c).eLpNorm_ne_top).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnorm

theorem weightedPhysicalJet_eLpNorm_le_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {u : PolarPoint → ℝ}
    (hu : HeightMember D T γ u) {a b c s : ℕ} (horder : a + b + c ≤ s) :
    eLpNorm (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure ≤
      ENNReal.ofReal (physicalNorm T γ s u) :=
  weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp hu.2.2.2.2 horder

private theorem multiplier_weighted_product_abs
    (w f g K : ℝ) (c d : ℕ) (hw : 0 ≤ w) (hK : 0 ≤ K)
    (hf : |f| ≤ K * w ^ d) :
    |w ^ c * f * g| ≤ |K * (w ^ (c + d) * g)| := by
  simp only [abs_mul, abs_of_nonneg hK, pow_add,
    abs_of_nonneg (pow_nonneg hw c), abs_of_nonneg (pow_nonneg hw d)]
  calc
    w ^ c * |f| * |g| ≤ w ^ c * (K * w ^ d) * |g| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf (pow_nonneg hw c)) (abs_nonneg g)
    _ = _ := by ring

private theorem multiplier_eLpNorm_const_mul
    {f : PolarPoint → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hb : eLpNorm f 2 materialCylinderMeasure ≤ ENNReal.ofReal A) :
    eLpNorm (fun p => c * f p) 2 materialCylinderMeasure ≤ ENNReal.ofReal (c * A) := by
  change eLpNorm (c • f) 2 materialCylinderMeasure ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc, ENNReal.ofReal_mul hc]
  exact mul_le_mul_left' hb _

private theorem multiplier_eLpNorm_finset_sum
    {ι : Type*} (I : Finset ι) (f : ι → PolarPoint → ℝ) (A : ι → ℝ)
    (hA : ∀ i ∈ I, 0 ≤ A i)
    (hb : ∀ i ∈ I, eLpNorm (f i) 2 materialCylinderMeasure ≤ ENNReal.ofReal (A i)) :
    eLpNorm (fun p => ∑ i ∈ I, f i p) 2 materialCylinderMeasure ≤
      ENNReal.ofReal (∑ i ∈ I, A i) := by
  classical
  revert hA hb
  induction I using Finset.induction_on with
  | empty => intro hA hb; simp
  | @insert i I hi ih =>
    intro hA hb
    have heq : (fun p => ∑ j ∈ insert i I, f j p) =
        f i + (fun p => ∑ j ∈ I, f j p) := by
      funext p
      simp only [Finset.sum_insert hi, Pi.add_apply]
    rw [heq, Finset.sum_insert hi,
      ENNReal.ofReal_add (hA i (Finset.mem_insert_self i I))
        (Finset.sum_nonneg (fun j hj => hA j (Finset.mem_insert_of_mem hj)))]
    exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add (hb i (Finset.mem_insert_self i I))
        (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
          (fun j hj => hb j (Finset.mem_insert_of_mem hj))))

def materialMultiplierJetConstant (s : ℕ) : ℝ :=
  ∑ J : JetIndex s,
    ∑ j ∈ Finset.range ((J.val 1).val + 1),
      ∑ i ∈ Finset.range ((J.val 0).val + 1),
        ((J.val 1).val.choose j : ℝ) * ((J.val 0).val.choose i : ℝ)

theorem materialMultiplierJetConstant_nonneg (s : ℕ) :
    0 ≤ materialMultiplierJetConstant s := by
  unfold materialMultiplierJetConstant
  positivity

def materialMultiplierNormConstant (s : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (JetIndex s) : ℝ) * materialMultiplierJetConstant s

theorem materialMultiplierNormConstant_nonneg (s : ℕ) :
    0 ≤ materialMultiplierNormConstant s :=
  mul_nonneg (Real.sqrt_nonneg _) (materialMultiplierJetConstant_nonneg s)

private theorem weighted_mixed_product_eLpNorm_le
    {W F G : PolarPoint → ℝ} (hW : Continuous W) (hWpos : ∀ p, 0 ≤ W p)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (a b c d : ℕ) {K N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hcoeff : ∀ i ≤ a, ∀ j ≤ b, ∀ p, |mixedDerivative i j F p| ≤ K * W p ^ d)
    (hinput : ∀ i ≤ a, ∀ j ≤ b,
      eLpNorm (fun p => W p ^ (c + d) * mixedDerivative (a - i) (b - j) G p)
        2 materialCylinderMeasure ≤ ENNReal.ofReal N) :
    eLpNorm (fun p => W p ^ c * mixedDerivative a b (fun q => F q * G q) p)
      2 materialCylinderMeasure ≤ ENNReal.ofReal
        ((∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
          (b.choose j : ℝ) * (a.choose i : ℝ)) * (K * N)) := by
  let P (j i : ℕ) (p : PolarPoint) : ℝ :=
    W p ^ c * mixedDerivative i j F p * mixedDerivative (a - i) (b - j) G p
  let A (j i : ℕ) : ℝ := (b.choose j : ℝ) * (a.choose i : ℝ)
  have hA (j i : ℕ) : 0 ≤ A j i := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (b + 1))
      (i : ℕ) (hi : i ∈ Finset.range (a + 1)) :
      eLpNorm (fun p => A j i * P j i p) 2 materialCylinderMeasure ≤
        ENNReal.ofReal (A j i * (K * N)) := by
    have hjb : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hia : i ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hcont : Continuous (P j i) :=
      ((hW.pow c).mul (contDiff_mixedDerivative hF i j).continuous).mul
        (contDiff_mixedDerivative hG (a - i) (b - j)).continuous
    have hmono : eLpNorm (P j i) 2 materialCylinderMeasure ≤
        eLpNorm (fun p => K * (W p ^ (c + d) *
          mixedDerivative (a - i) (b - j) G p)) 2 materialCylinderMeasure := by
      apply eLpNorm_mono hcont.aestronglyMeasurable
      intro p
      simpa only [P, Real.norm_eq_abs] using
        multiplier_weighted_product_abs (W p) (mixedDerivative i j F p)
          (mixedDerivative (a - i) (b - j) G p) K c d (hWpos p) hK (hcoeff i hia j hjb p)
    exact multiplier_eLpNorm_const_mul (hA j i)
      (hmono.trans (multiplier_eLpNorm_const_mul hK (hinput i hia j hjb)))
  have hsum := multiplier_eLpNorm_finset_sum (Finset.range (b + 1))
    (fun j p => ∑ i ∈ Finset.range (a + 1), A j i * P j i p)
    (fun j => ∑ i ∈ Finset.range (a + 1), A j i * (K * N))
    (fun j _ => Finset.sum_nonneg (fun i _ => mul_nonneg (hA j i) (mul_nonneg hK hN)))
    (fun j hj => multiplier_eLpNorm_finset_sum (Finset.range (a + 1))
      (fun i p => A j i * P j i p) (fun i => A j i * (K * N))
      (fun i _ => mul_nonneg (hA j i) (mul_nonneg hK hN)) (hterm j hj))
  have heq : (fun p => W p ^ c * mixedDerivative a b (fun q => F q * G q) p) =
      (fun p => ∑ j ∈ Finset.range (b + 1),
        ∑ i ∈ Finset.range (a + 1), A j i * P j i p) :=
    funext (weighted_mixedDerivative_mul hF hG W a b c)
  rw [heq]
  simpa only [A, Finset.sum_mul] using hsum

/-- A common bound for all input jets through s+d is retained after
material multiplication, with one order-dependent numerical factor. -/
theorem weightedMixedJets_eLpNorm_mul_bound
    {W F G : PolarPoint → ℝ} (hW : Continuous W) (hWpos : ∀ p, 0 ≤ W p)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (s d : ℕ) {K N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hcoeff : ∀ a b, a + b ≤ s → ∀ p, |mixedDerivative a b F p| ≤ K * W p ^ d)
    (hinput : ∀ a b c, a + b + c ≤ s + d →
      eLpNorm (fun p => W p ^ c * mixedDerivative a b G p) 2 materialCylinderMeasure ≤
        ENNReal.ofReal N) :
    ∀ a b c, a + b + c ≤ s →
      eLpNorm (fun p => W p ^ c * mixedDerivative a b (fun q => F q * G q) p)
        2 materialCylinderMeasure ≤ ENNReal.ofReal (materialMultiplierJetConstant s * K * N) := by
  classical
  intro a b c horder
  have hb := weighted_mixed_product_eLpNorm_le hW hWpos hF hG a b c d hK hN
    (fun i hi j hj p => hcoeff i j (by omega) p)
    (fun i hi j hj => hinput (a - i) (b - j) (c + d) (by omega))
  let J : JetIndex s := ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using horder⟩
  have hc : (∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
      (b.choose j : ℝ) * (a.choose i : ℝ)) ≤ materialMultiplierJetConstant s := by
    exact Finset.single_le_sum (f := fun J : JetIndex s =>
      ∑ j ∈ Finset.range ((J.val 1).val + 1),
        ∑ i ∈ Finset.range ((J.val 0).val + 1),
          ((J.val 1).val.choose j : ℝ) * ((J.val 0).val.choose i : ℝ))
      (fun J _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ =>
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Finset.mem_univ J)
  exact hb.trans (ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_right hc (mul_nonneg hK hN)).trans_eq (mul_assoc _ _ _).symm))

/-- The coefficient growth is needed only through the chosen output
order, and every term retains its complementary height order. -/
theorem physicalNorm_mul_le_order_budget_of_memLp
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f u : PolarPoint → ℝ}
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hu : ContDiffOn ℝ ∞ u (annularOpen D))
    (huLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure)
    (s d : ℕ) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hbound : ∀ a b, a + b ≤ s → ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p| ≤
        K (a + b) * T.M (T.radius p.1) ^ d) :
    physicalNorm T γ s (fun p => f p * u p) ≤
      materialMultiplierNormConstant s *
        ∑ k ∈ Finset.range (s + 1), K k * physicalNorm T γ (s - k + d) u := by
  classical
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let F (p : PolarPoint) : ℝ := f (T.radius p.1, p.2)
  let G : PolarPoint → ℝ := materialPullback T γ u
  let B : ℝ := ∑ k ∈ Finset.range (s + 1), K k * physicalNorm T γ (s - k + d) u
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => mul_nonneg (hK k) (Real.sqrt_nonneg _))
  have hrange (t : ℝ) : T.radius t ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 t).1
  have hW : Continuous W :=
    ((materialRadius_comp_contDiff hT (hT.1 T.M (by simp))).comp contDiff_fst).continuous
  have hWpos (p : PolarPoint) : 0 ≤ W p :=
    zero_le_one.trans (hT.2.1 _ (hrange p.1)).2.2.2
  have hF : ContDiff ℝ ∞ F := hf.comp_contDiff
    ((hT.2.2.2.2.2.2.1.comp contDiff_fst).prodMk contDiff_snd)
    (fun p => ⟨hrange p.1, mem_univ _⟩)
  have hG : ContDiff ℝ ∞ G := contDiff_materialPullback hT hu
  have hpull : materialPullback T γ (fun p => f p * u p) = (fun p => F p * G p) := by
    funext p
    dsimp only [F, G, materialPullback]
    ring
  have hjet (J : JetIndex s) :
      eLpNorm (weightedPhysicalJet T γ (J.val 0).val (J.val 1).val
        (J.val 2).val (fun p => f p * u p)) 2 materialCylinderMeasure ≤
        ENNReal.ofReal (materialMultiplierJetConstant s * B) := by
    let a := (J.val 0).val
    let b := (J.val 1).val
    let c := (J.val 2).val
    have horder : a + b + c ≤ s := J.property
    let P (j i : ℕ) (p : PolarPoint) : ℝ :=
      W p ^ c * mixedDerivative i j F p * mixedDerivative (a - i) (b - j) G p
    let A (j i : ℕ) : ℝ := (b.choose j : ℝ) * (a.choose i : ℝ)
    have hA (j i : ℕ) : 0 ≤ A j i := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hterm (j : ℕ) (hj : j ∈ Finset.range (b + 1))
        (i : ℕ) (hi : i ∈ Finset.range (a + 1)) :
        eLpNorm (fun p => A j i * P j i p) 2 materialCylinderMeasure ≤
          ENNReal.ofReal (A j i * B) := by
      have hjb : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hia : i ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hij : i + j ≤ s := by omega
      have hLp : MemLp (fun p => W p ^ (c + d) *
          mixedDerivative (a - i) (b - j) G p) 2 materialCylinderMeasure :=
        huLp (a - i) (b - j) (c + d)
      have hP : MemLp (P j i) 2 materialCylinderMeasure :=
        memLp_weighted_product_of_power_bound hW hWpos
          (contDiff_mixedDerivative hF i j).continuous
          (contDiff_mixedDerivative hG (a - i) (b - j)).continuous c d
          (hK (i + j)) (hbound i j hij) hLp
      have hmono : eLpNorm (P j i) 2 materialCylinderMeasure ≤
          eLpNorm (K (i + j) • weightedPhysicalJet T γ (a - i) (b - j) (c + d) u)
            2 materialCylinderMeasure := by
        apply eLpNorm_mono hP.aestronglyMeasurable
        intro p
        simpa only [P, Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul,
          weightedPhysicalJet, W, G] using
          multiplier_weighted_product_abs (W p) (mixedDerivative i j F p)
            (mixedDerivative (a - i) (b - j) G p) (K (i + j)) c d
              (hWpos p) (hK (i + j)) (hbound i j hij p)
      have hn : eLpNorm (weightedPhysicalJet T γ (a - i) (b - j) (c + d) u)
          2 materialCylinderMeasure ≤ ENNReal.ofReal (physicalNorm T γ (s - (i + j) + d) u) :=
        weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp huLp (by omega)
      have hpn : eLpNorm (P j i) 2 materialCylinderMeasure ≤
          ENNReal.ofReal (K (i + j) * physicalNorm T γ (s - (i + j) + d) u) := by
        calc
          _ ≤ _ := hmono
          _ = ENNReal.ofReal (K (i + j)) *
              eLpNorm (weightedPhysicalJet T γ (a - i) (b - j) (c + d) u)
                2 materialCylinderMeasure := by
            rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hK (i + j))]
          _ ≤ ENNReal.ofReal (K (i + j)) *
              ENNReal.ofReal (physicalNorm T γ (s - (i + j) + d) u) := mul_le_mul_left' hn _
          _ = _ := (ENNReal.ofReal_mul (hK (i + j))).symm
      have hs : K (i + j) * physicalNorm T γ (s - (i + j) + d) u ≤ B :=
        Finset.single_le_sum
          (f := fun k => K k * physicalNorm T γ (s - k + d) u)
          (fun k _ => mul_nonneg (hK k) (Real.sqrt_nonneg _))
          (Finset.mem_range.mpr (by omega))
      exact multiplier_eLpNorm_const_mul (hA j i)
        (hpn.trans (ENNReal.ofReal_le_ofReal hs))
    have hsum := multiplier_eLpNorm_finset_sum (Finset.range (b + 1))
      (fun j p => ∑ i ∈ Finset.range (a + 1), A j i * P j i p)
      (fun j => ∑ i ∈ Finset.range (a + 1), A j i * B)
      (fun j _ => Finset.sum_nonneg (fun i _ => mul_nonneg (hA j i) hB))
      (fun j hj => multiplier_eLpNorm_finset_sum (Finset.range (a + 1))
        (fun i p => A j i * P j i p) (fun i => A j i * B)
        (fun i _ => mul_nonneg (hA j i) hB) (hterm j hj))
    have hscalar : weightedPhysicalJet T γ a b c (fun p => f p * u p) =
        (fun p => ∑ j ∈ Finset.range (b + 1),
          ∑ i ∈ Finset.range (a + 1), A j i * P j i p) := by
      funext p
      change W p ^ c * mixedDerivative a b
        (materialPullback T γ (fun p => f p * u p)) p = _
      rw [hpull]
      exact weighted_mixedDerivative_mul hF hG W a b c p
    have hcoeff : (∑ j ∈ Finset.range (b + 1),
        ∑ i ∈ Finset.range (a + 1), A j i) ≤ materialMultiplierJetConstant s := by
      exact Finset.single_le_sum (f := fun J : JetIndex s =>
        ∑ j ∈ Finset.range ((J.val 1).val + 1),
          ∑ i ∈ Finset.range ((J.val 0).val + 1),
            ((J.val 1).val.choose j : ℝ) * ((J.val 0).val.choose i : ℝ))
        (fun J _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ =>
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Finset.mem_univ J)
    have hreal : (∑ j ∈ Finset.range (b + 1),
        ∑ i ∈ Finset.range (a + 1), A j i * B) ≤ materialMultiplierJetConstant s * B := by
      simpa only [Finset.sum_mul] using mul_le_mul_of_nonneg_right hcoeff hB
    change eLpNorm (weightedPhysicalJet T γ a b c (fun p => f p * u p))
      2 materialCylinderMeasure ≤ _
    rw [hscalar]
    exact hsum.trans (ENNReal.ofReal_le_ofReal hreal)
  have hnorm := physicalNorm_le_of_common_jet_bound
    (mul_nonneg (materialMultiplierJetConstant_nonneg s) hB) hjet
  exact hnorm.trans_eq (by dsimp only [materialMultiplierNormConstant, B]; ring)

theorem physicalNorm_mul_le_order_budget
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f u : PolarPoint → ℝ}
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (hu : HeightMember D T γ u)
    (s d : ℕ) (K : ℕ → ℝ) (hK : ∀ k, 0 ≤ K k)
    (hbound : ∀ a b, a + b ≤ s → ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p| ≤
        K (a + b) * T.M (T.radius p.1) ^ d) :
    physicalNorm T γ s (fun p => f p * u p) ≤
      materialMultiplierNormConstant s *
        ∑ k ∈ Finset.range (s + 1), K k * physicalNorm T γ (s - k + d) u :=
  physicalNorm_mul_le_order_budget_of_memLp hT hf hu.1 hu.2.2.2.2 s d K hK hbound

end ContinuousFlexibility.Statements
