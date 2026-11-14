module

public import ContinuousFlexibility.Analysis.MaterialPartialNormBounds
public import ContinuousFlexibility.Analysis.MaterialDivergenceEnergy
public import ContinuousFlexibility.Analysis.PhysicalJetBonding

/-!
# Quantitative physical sums and symmetric divergence

All norms below are the actual finite weighted L² jet norms. Monotonicity
and finite sums require no symmetry of intermediate fields. The material
multiplier estimates retain the coefficient/height derivative budget.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal

theorem physicalNorm_monotone_of_memLp
    {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure) :
    Monotone (fun s => physicalNorm T γ s f) := by
  classical
  intro s t hst
  let E (j : JetIndex t) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
      2 materialCylinderMeasure ^ 2
  have hfinite : (∑ j : JetIndex t, E j) < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro j _
    dsimp only [E]
    rw [pow_two]
    exact ENNReal.mul_lt_top (hLp _ _ _) (hLp _ _ _)
  have he : physicalLevelEnergy T γ s f ≤ ∑ j : JetIndex t, E j := by
    calc
      _ = ∑ j ∈ Finset.univ.map (physicalJetIndexOfLE hst), E j := by
        rw [Finset.sum_map]
        rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => zero_le)
  exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite.ne he)

theorem contDiffOn_finset_sum_fields
    {ι : Type*} {U : Set PolarPoint} (I : Finset ι) (f : ι → PolarPoint → ℝ)
    (hf : ∀ i ∈ I, ContDiffOn ℝ ∞ (f i) U) :
    ContDiffOn ℝ ∞ (fun p => ∑ i ∈ I, f i p) U := by
  classical
  revert hf
  induction I using Finset.induction_on with
  | empty => intro hf; simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : PolarPoint => (0 : ℝ)) U)
  | @insert i I hi ih =>
    intro hf
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i I)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem weightedPhysicalJet_finset_sum
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hT : IsMaterialData D T) (I : Finset ι) (f : ι → PolarPoint → ℝ)
    (hf : ∀ i ∈ I, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (a b c : ℕ) (p : PolarPoint) :
    weightedPhysicalJet T γ a b c (fun q => ∑ i ∈ I, f i q) p =
      ∑ i ∈ I, weightedPhysicalJet T γ a b c (f i) p := by
  classical
  revert hf
  induction I using Finset.induction_on with
  | empty =>
    intro hf
    simp [weightedPhysicalJet, materialPullback, mixedDerivative, iteratedDeriv_const]
  | @insert i I hi ih =>
    intro hf
    simp only [Finset.sum_insert hi]
    rw [weightedPhysicalJet_add hT (hf i (Finset.mem_insert_self i I))
      (contDiffOn_finset_sum_fields I f (fun j hj => hf j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem physicalNorm_finset_sum_le
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hT : IsMaterialData D T) (I : Finset ι) (f : ι → PolarPoint → ℝ)
    (hf : ∀ i ∈ I, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (hLp : ∀ i ∈ I, ∀ a b c,
      MemLp (weightedPhysicalJet T γ a b c (f i)) 2 materialCylinderMeasure) (s : ℕ) :
    physicalNorm T γ s (fun p => ∑ i ∈ I, f i p) ≤
      Real.sqrt (Fintype.card (JetIndex s) : ℝ) * ∑ i ∈ I, physicalNorm T γ s (f i) := by
  apply physicalNorm_le_of_common_jet_bound
    (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
  intro J
  have heq : weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val
      (fun p => ∑ i ∈ I, f i p) =
      (fun p => ∑ i ∈ I,
        weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val (f i) p) :=
    funext (weightedPhysicalJet_finset_sum hT I f hf _ _ _)
  rw [heq]
  exact multiplier_eLpNorm_finset_sum I
    (fun i => weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val (f i))
    (fun i => physicalNorm T γ s (f i)) (fun _ _ => Real.sqrt_nonneg _)
    (fun i hi => weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp (hLp i hi) J.property)

theorem physicalNorm_add_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f g : PolarPoint → ℝ}
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (hg : ContDiffOn ℝ ∞ g (annularOpen D))
    (hfLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure)
    (hgLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c g) 2 materialCylinderMeasure)
    (s : ℕ) :
    physicalNorm T γ s (fun p => f p + g p) ≤
      Real.sqrt (Fintype.card (JetIndex s) : ℝ) *
        (physicalNorm T γ s f + physicalNorm T γ s g) := by
  apply physicalNorm_le_of_common_jet_bound (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  intro J
  have heq : weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val
      (fun p => f p + g p) =
      weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val f +
        weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val g :=
    funext (weightedPhysicalJet_add hT hf hg _ _ _)
  rw [heq, ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add (weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp hfLp J.property)
      (weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp hgLp J.property))

theorem memLp_weightedPhysicalJet_mul_of_material_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f u : PolarPoint → ℝ}
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (hu : ContDiffOn ℝ ∞ u (annularOpen D))
    (hLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure)
    (d : ℕ) (hbound : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p| ≤
        K * T.M (T.radius p.1) ^ d) (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c (fun p => f p * u p)) 2 materialCylinderMeasure := by
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let F (p : PolarPoint) : ℝ := f (T.radius p.1, p.2)
  let G : PolarPoint → ℝ := materialPullback T γ u
  have hrange (t : ℝ) : T.radius t ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 t).1
  have hW : Continuous W :=
    ((materialRadius_comp_contDiff hT (hT.1 T.M (by simp))).comp contDiff_fst).continuous
  have hWpos (p : PolarPoint) : 0 ≤ W p := zero_le_one.trans (hT.2.1 _ (hrange p.1)).2.2.2
  have hF : ContDiff ℝ ∞ F := hf.comp_contDiff
    ((hT.2.2.2.2.2.2.1.comp contDiff_fst).prodMk contDiff_snd)
    (fun p => ⟨hrange p.1, mem_univ _⟩)
  have hG : ContDiff ℝ ∞ G := contDiff_materialPullback hT hu
  have hb := memLp_weighted_mixed_product hW hWpos hF hG d hbound hLp a b c
  have hpull : materialPullback T γ (fun p => f p * u p) = (fun p => F p * G p) := by
    funext p
    dsimp only [F, G, materialPullback]
    ring
  have hjet : weightedPhysicalJet T γ a b c (fun p => f p * u p) =
      (fun p => W p ^ c * mixedDerivative a b (fun q => F q * G q) p) := by
    funext p
    change W p ^ c * mixedDerivative a b (materialPullback T γ (fun p => f p * u p)) p = _
    rw [hpull]
  exact hjet.symm ▸ hb

theorem exists_physicalNorm_partials_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (γ : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ u (annularOpen D) →
      (∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure) →
      physicalNorm T γ s (radialPartial u) ≤ C * physicalNorm T γ (s + 2) u ∧
        physicalNorm T γ s (angularPartial u) ≤ C * physicalNorm T γ (s + 2) u := by
  obtain ⟨C, hC, hb⟩ := exists_physicalNorm_radialPartial_bound hT γ s
  let A : ℝ := Real.sqrt (Fintype.card (JetIndex s) : ℝ)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨C + A, add_nonneg hC hA, fun u hu huLp => ⟨?_, ?_⟩⟩
  · exact (hb u hu huLp).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hA) (Real.sqrt_nonneg _))
  · exact ((physicalNorm_angularPartial_le hT hu huLp s).trans
      (mul_le_mul_of_nonneg_left
        (physicalNorm_monotone_of_memLp huLp (by omega : s + 1 ≤ s + 2)) hA)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (Real.sqrt_nonneg _))

/-- A fixed loss of four physical orders suffices for the symmetric
divergence, while each coefficient order k retains height order s+4-k+d.
The numerical constant is fixed before the coefficients and height. -/
theorem exists_physicalNorm_symmetric_divergence_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) (s d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ A (annularOpen D) → ContDiffOn ℝ ∞ B (annularOpen D) →
      ∀ K : ℕ → ℝ, (∀ k, 0 ≤ K k) →
      (∀ a b, ∀ p : PolarPoint,
        |mixedDerivative a b (fun q => A (T.radius q.1, q.2)) p| ≤
          K (a + b) * T.M (T.radius p.1) ^ d ∧
        |mixedDerivative a b (fun q => B (T.radius q.1, q.2)) p| ≤
          K (a + b) * T.M (T.radius p.1) ^ d) →
      ∀ u : PolarPoint → ℝ, ContDiffOn ℝ ∞ u (annularOpen D) →
      (∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure) →
      physicalNorm T γ s
        (fun p => radialPartial (fun q => A q * angularPartial u q) p +
          angularPartial (fun q => A q * radialPartial u q + B q * angularPartial u q) p) ≤
        C * ∑ k ∈ Finset.range (s + 3), K k * physicalNorm T γ (s + 4 - k + d) u := by
  classical
  choose CP hCP hbP using fun n => exists_physicalNorm_partials_bound hT γ n
  let t : ℕ := s + 2
  let P : ℝ := ∑ q : Fin (t + d + 1), CP q.val
  have hP : 0 ≤ P := Finset.sum_nonneg (fun q _ => hCP q.val)
  have hCPle (q : ℕ) (hq : q ≤ t + d) : CP q ≤ P :=
    Finset.single_le_sum (f := fun q : Fin (t + d + 1) => CP q.val)
      (fun q _ => hCP q.val) (Finset.mem_univ ⟨q, by omega⟩)
  let H (n : ℕ) : ℝ := Real.sqrt (Fintype.card (JetIndex n) : ℝ)
  have hH (n : ℕ) : 0 ≤ H n := Real.sqrt_nonneg _
  let Z : ℝ := materialMultiplierNormConstant t * P
  have hZ : 0 ≤ Z := mul_nonneg (materialMultiplierNormConstant_nonneg _) hP
  let C : ℝ := H s * CP s * (1 + 2 * H t) * Z
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (hH s) (hCP s))
    (add_nonneg zero_le_one (mul_nonneg (by norm_num) (hH t)))) hZ
  refine ⟨C, hC, fun A B hA hB K hK hcoeff u hu huLp => ?_⟩
  let N : ℝ := ∑ k ∈ Finset.range (s + 3), K k * physicalNorm T γ (s + 4 - k + d) u
  have hN : 0 ≤ N := Finset.sum_nonneg (fun k _ => mul_nonneg (hK k) (Real.sqrt_nonneg _))
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hur := contDiffOn_radialPartial_of_isOpen hU hu
  have hut := contDiffOn_angularPartial_of_isOpen hU hu
  have hurLp := memLp_weightedPhysicalJet_radialPartial hT hu huLp
  have hutLp := memLp_weightedPhysicalJet_angularPartial hT hu huLp
  have hdu (q : ℕ) (hq : q ≤ t + d) :
      physicalNorm T γ q (radialPartial u) ≤ P * physicalNorm T γ (q + 2) u ∧
        physicalNorm T γ q (angularPartial u) ≤ P * physicalNorm T γ (q + 2) u := by
    have h := hbP q u hu huLp
    have hp := mul_le_mul_of_nonneg_right (hCPle q hq)
      (show 0 ≤ physicalNorm T γ (q + 2) u from Real.sqrt_nonneg _)
    exact ⟨h.1.trans hp, h.2.trans hp⟩
  have hprod (f v : PolarPoint → ℝ)
      (hf : ContDiffOn ℝ ∞ f (annularOpen D))
      (hfb : ∀ a b, ∀ p : PolarPoint,
        |mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p| ≤
          K (a + b) * T.M (T.radius p.1) ^ d)
      (hv : ContDiffOn ℝ ∞ v (annularOpen D))
      (hvLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c v) 2 materialCylinderMeasure)
      (hvb : ∀ q ≤ t + d, physicalNorm T γ q v ≤ P * physicalNorm T γ (q + 2) u) :
      physicalNorm T γ t (fun p => f p * v p) ≤ Z * N := by
    have hb := physicalNorm_mul_le_order_budget_of_memLp hT hf hv hvLp t d K hK
      (fun a b _ p => hfb a b p)
    have hs : (∑ k ∈ Finset.range (t + 1), K k * physicalNorm T γ (t - k + d) v) ≤
        P * N := by
      have hsum : (∑ k ∈ Finset.range (t + 1), K k * physicalNorm T γ (t - k + d) v) ≤
          ∑ k ∈ Finset.range (t + 1), K k * (P * physicalNorm T γ (s + 4 - k + d) u) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkt : k ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have horder : t - k + d + 2 = s + 4 - k + d := by dsimp only [t] at *; omega
        have h := hvb (t - k + d) (by omega)
        rw [horder] at h
        exact mul_le_mul_of_nonneg_left h (hK k)
      apply hsum.trans_eq
      change (∑ k ∈ Finset.range (s + 3), K k * (P * physicalNorm T γ (s + 4 - k + d) u)) = _
      dsimp only [N]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    exact hb.trans ((mul_le_mul_of_nonneg_left hs
      (materialMultiplierNormConstant_nonneg t)).trans_eq (mul_assoc _ _ _).symm)
  let F (p : PolarPoint) : ℝ := A p * angularPartial u p
  let G (p : PolarPoint) : ℝ := A p * radialPartial u p + B p * angularPartial u p
  have hF : ContDiffOn ℝ ∞ F (annularOpen D) := hA.mul hut
  have hG : ContDiffOn ℝ ∞ G (annularOpen D) := (hA.mul hur).add (hB.mul hut)
  have hAb (a b : ℕ) : ∃ K' : ℝ, 0 ≤ K' ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => A (T.radius q.1, q.2)) p| ≤
        K' * T.M (T.radius p.1) ^ d :=
    ⟨K (a + b), hK (a + b), fun p => (hcoeff a b p).1⟩
  have hBb (a b : ℕ) : ∃ K' : ℝ, 0 ≤ K' ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => B (T.radius q.1, q.2)) p| ≤
        K' * T.M (T.radius p.1) ^ d :=
    ⟨K (a + b), hK (a + b), fun p => (hcoeff a b p).2⟩
  have hFLp (a b c : ℕ) : MemLp (weightedPhysicalJet T γ a b c F) 2 materialCylinderMeasure :=
    memLp_weightedPhysicalJet_mul_of_material_bound hT hA hut hutLp d hAb a b c
  have hArLp (a b c : ℕ) :
      MemLp (weightedPhysicalJet T γ a b c (fun p => A p * radialPartial u p))
        2 materialCylinderMeasure :=
    memLp_weightedPhysicalJet_mul_of_material_bound hT hA hur hurLp d hAb a b c
  have hBtLp (a b c : ℕ) :
      MemLp (weightedPhysicalJet T γ a b c (fun p => B p * angularPartial u p))
        2 materialCylinderMeasure :=
    memLp_weightedPhysicalJet_mul_of_material_bound hT hB hut hutLp d hBb a b c
  have hGLp (a b c : ℕ) : MemLp (weightedPhysicalJet T γ a b c G) 2 materialCylinderMeasure :=
    memLp_weightedPhysicalJet_add hT (hA.mul hur) (hB.mul hut) (hArLp a b c) (hBtLp a b c)
  have hFn : physicalNorm T γ t F ≤ Z * N :=
    hprod A (angularPartial u) hA (fun a b p => (hcoeff a b p).1) hut hutLp
      (fun q hq => (hdu q hq).2)
  have hArn : physicalNorm T γ t (fun p => A p * radialPartial u p) ≤ Z * N :=
    hprod A (radialPartial u) hA (fun a b p => (hcoeff a b p).1) hur hurLp
      (fun q hq => (hdu q hq).1)
  have hBtn : physicalNorm T γ t (fun p => B p * angularPartial u p) ≤ Z * N :=
    hprod B (angularPartial u) hB (fun a b p => (hcoeff a b p).2) hut hutLp
      (fun q hq => (hdu q hq).2)
  have hGn : physicalNorm T γ t G ≤ H t * (Z * N + Z * N) :=
    (physicalNorm_add_le hT (hA.mul hur) (hB.mul hut) hArLp hBtLp t).trans
      (mul_le_mul_of_nonneg_left (add_le_add hArn hBtn) (hH t))
  have hFr : physicalNorm T γ s (radialPartial F) ≤ CP s * (Z * N) :=
    (hbP s F hF hFLp).1.trans (mul_le_mul_of_nonneg_left hFn (hCP s))
  have hGt : physicalNorm T γ s (angularPartial G) ≤ CP s * (H t * (Z * N + Z * N)) :=
    (hbP s G hG hGLp).2.trans (mul_le_mul_of_nonneg_left hGn (hCP s))
  have hb := physicalNorm_add_le hT
    (contDiffOn_radialPartial_of_isOpen hU hF)
    (contDiffOn_angularPartial_of_isOpen hU hG)
    (memLp_weightedPhysicalJet_radialPartial hT hF hFLp)
    (memLp_weightedPhysicalJet_angularPartial hT hG hGLp) s
  have htotal := hb.trans (mul_le_mul_of_nonneg_left (add_le_add hFr hGt) (hH s))
  exact htotal.trans_eq (by dsimp only [C, N]; ring)

end ContinuousFlexibility.Statements
