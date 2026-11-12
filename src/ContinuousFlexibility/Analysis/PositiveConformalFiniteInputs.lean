import ContinuousFlexibility.Analysis.N01PositiveCircleInputs
import ContinuousFlexibility.Analysis.PositiveConformalDensityAlgebra
import ContinuousFlexibility.Analysis.OneHighCompositionJets
import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-!
# Actual finite conformal inputs on a common positive neighborhood

The three original coefficient jets through order three and positive
lower bounds for a and det A control the actual conformal speed, shear,
height, and log-height through that same order. Compactness is applied
only to the finite dimensional coefficient value set. The chain rule is
the existing ordered-partition formula; no derivative of a prospective
coordinate chart is among the inputs.

The final adapter retains the common neighborhood already selected from
N01. Its constants precede the state and angle at each future endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual speed, shear, height, and log-height used by the finite
coordinate and positive-height Taylor constructions. -/
def positiveConformalInputField (i : Fin 4) (A : SymmetricCoefficients) :
    PolarPoint → ℝ :=
  if i = 0 then positiveConformalSpeed A
  else if i = 1 then positiveConformalShear A
  else if i = 2 then positiveConformalHeight A
  else fun p => Real.log (positiveConformalHeight A p)

def positiveConformalValue (i : Fin 4) (x : ℝ × ℝ × ℝ) : ℝ :=
  if i = 0 then Real.sqrt (x.1 * x.2.2 - x.2.1 ^ 2) / x.1
  else if i = 1 then -x.2.1 / x.1
  else if i = 2 then (Real.sqrt (Real.sqrt (x.1 * x.2.2 - x.2.1 ^ 2)))⁻¹
  else Real.log ((Real.sqrt (Real.sqrt (x.1 * x.2.2 - x.2.1 ^ 2)))⁻¹)

def positiveConformalValueDomain : Set (ℝ × ℝ × ℝ) :=
  {x | 0 < x.1 ∧ 0 < x.1 * x.2.2 - x.2.1 ^ 2}

theorem positiveConformalValueDomain_isOpen :
    IsOpen positiveConformalValueDomain :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const
      ((continuous_fst.mul continuous_snd.snd).sub (continuous_snd.fst.pow 2)))

theorem positiveConformalValue_contDiffAt (i : Fin 4)
    {x : ℝ × ℝ × ℝ} (hx : x ∈ positiveConformalValueDomain) :
    ContDiffAt ℝ ∞ (positiveConformalValue i) x := by
  have ha : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.1) x := contDiffAt_fst
  have hb : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.2.1) x := contDiffAt_snd.fst
  have hc : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.2.2) x := contDiffAt_snd.snd
  have hD := (ha.mul hc).sub (hb.pow 2)
  have hS := hD.sqrt hx.2.ne'
  have hs : 0 < Real.sqrt (x.1 * x.2.2 - x.2.1 ^ 2) := Real.sqrt_pos.mpr hx.2
  have hSS := hS.sqrt hs.ne'
  have hss : 0 < Real.sqrt (Real.sqrt (x.1 * x.2.2 - x.2.1 ^ 2)) :=
    Real.sqrt_pos.mpr hs
  unfold positiveConformalValue
  split_ifs
  · exact hS.fun_div ha hx.1.ne'
  · exact hb.neg.fun_div ha hx.1.ne'
  · exact hSS.fun_inv hss.ne'
  · exact (hSS.fun_inv hss.ne').log (inv_ne_zero hss.ne')

private theorem positiveConformalValue_outer_bounds
    {l κ M : ℝ} (hl : 0 < l) (hκ : 0 < κ) :
    ∃ R : ℝ, 0 < R ∧ ∀ i : Fin 4, ∀ k : ℕ, k ≤ 3 →
      ∀ x : ℝ × ℝ × ℝ,
        |x.1| ≤ M → |x.2.1| ≤ M → |x.2.2| ≤ M →
        l ≤ x.1 → κ ≤ x.1 * x.2.2 - x.2.1 ^ 2 →
        ‖iteratedFDeriv ℝ k (positiveConformalValue i) x‖ ≤ R := by
  let K : Set (ℝ × ℝ × ℝ) :=
    (Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc (-M) M) ∩
      {x | l ≤ x.1 ∧ κ ≤ x.1 * x.2.2 - x.2.1 ^ 2}
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const
          ((continuous_fst.mul continuous_snd.snd).sub (continuous_snd.fst.pow 2))))
  have hKV : K ⊆ positiveConformalValueDomain :=
    fun _ hx => ⟨hl.trans_le hx.2.1, hκ.trans_le hx.2.2⟩
  have hbound (i : Fin 4) (k : ℕ) : ∃ D : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (positiveConformalValue i) x‖ ≤ D := by
    have hΦ : ContDiffOn ℝ ∞ (positiveConformalValue i) positiveConformalValueDomain :=
      fun x hx => (positiveConformalValue_contDiffAt i hx).contDiffWithinAt
    have hc := hΦ.continuousOn_iteratedFDerivWithin
      (m := k) (by simp) positiveConformalValueDomain_isOpen.uniqueDiffOn
    have hc' : ContinuousOn (iteratedFDeriv ℝ k (positiveConformalValue i))
        positiveConformalValueDomain := by
      apply hc.congr
      intro x hx
      exact (iteratedFDerivWithin_eq_iteratedFDeriv
        positiveConformalValueDomain_isOpen.uniqueDiffOn
        ((positiveConformalValue_contDiffAt i hx).of_le
          (by simp : (k : ℕ∞ω) ≤ ∞)) hx).symm
    exact hK.exists_bound_of_continuousOn (hc'.mono hKV)
  choose D hD using hbound
  let R : ℝ := 1 + ∑ i : Fin 4, ∑ k : Fin 4, |D i k|
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro i k hk x ha hb hc hlx hκx
  have hx : x ∈ K := ⟨⟨abs_le.mp ha, abs_le.mp hb, abs_le.mp hc⟩, hlx, hκx⟩
  have hs₁ : |D i k| ≤ ∑ j : Fin 4, |D i j| :=
    Finset.single_le_sum (f := fun j : Fin 4 => |D i j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (⟨k, by omega⟩ : Fin 4))
  have hs₂ : (∑ j : Fin 4, |D i j|) ≤ ∑ t : Fin 4, ∑ j : Fin 4, |D t j| :=
    Finset.single_le_sum (f := fun t : Fin 4 => ∑ j : Fin 4, |D t j|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
  exact (hD i k x hx).trans ((le_abs_self _).trans
    (hs₁.trans (hs₂.trans (le_add_of_nonneg_left zero_le_one))))

/-- This is a fixed order-three estimate. Its numerical constant precedes
the physical domain, the actual coefficient fields, and the point. -/
theorem exists_positiveConformal_threeJet_bound
    {l κ M : ℝ} (hl : 0 < l) (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 < B ∧
      ∀ U : Set PolarPoint, IsOpen U → ∀ A : SymmetricCoefficients,
        (∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i A) U) →
      ∀ p ∈ U, l ≤ A.a p → κ ≤ A.a p * A.c p - A.b p ^ 2 →
        (∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ 3 →
          |mixedDerivative a b (canonicalCoefficientComponent i A) p| ≤ M) →
        ∀ i : Fin 4, ∀ a b : ℕ, a + b ≤ 3 →
          |mixedDerivative a b (positiveConformalInputField i A) p| ≤ B := by
  obtain ⟨R, hR, houter⟩ := positiveConformalValue_outer_bounds hl hκ (M := M)
  let C (n : ℕ) : ℝ := ∑ π : OrderedFinpartition n,
    R * ∏ j, (2 : ℝ) ^ (π.partSize j) * M
  have hC (n : ℕ) : 0 ≤ C n :=
    Finset.sum_nonneg fun _ _ => mul_nonneg hR.le
      (Finset.prod_nonneg fun _ _ => mul_nonneg (pow_nonneg (by norm_num) _) hM)
  let B : ℝ := 1 + ∑ n : Fin 4, C n
  have hB : 0 < B :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun n _ => hC n)
  refine ⟨B, hB, ?_⟩
  intro U hU A hA p hp hal hdet hraw i a b hab
  have ha : ContDiffOn ℝ ∞ A.a U := by simpa [canonicalCoefficientComponent] using hA 0
  have hb : ContDiffOn ℝ ∞ A.b U := by simpa [canonicalCoefficientComponent] using hA 1
  have hc : ContDiffOn ℝ ∞ A.c U := by simpa [canonicalCoefficientComponent] using hA 2
  let v : PolarPoint → ℝ × ℝ × ℝ := fun q => (A.a q, A.b q, A.c q)
  have hv : ContDiffOn ℝ ∞ v U := ha.prodMk (hb.prodMk hc)
  have hvp : ContDiffAt ℝ ∞ v p := hv.contDiffAt (hU.mem_nhds hp)
  have hpV : v p ∈ positiveConformalValueDomain := ⟨hl.trans_le hal, hκ.trans_le hdet⟩
  let V := U ∩ v ⁻¹' positiveConformalValueDomain
  have hV : IsOpen V := hv.continuousOn.isOpen_inter_preimage hU positiveConformalValueDomain_isOpen
  have hp' : p ∈ V := ⟨hp, hpV⟩
  have he : positiveConformalInputField i A = positiveConformalValue i ∘ v := by
    funext q
    rfl
  have hfield : ContDiffOn ℝ ∞ (positiveConformalInputField i A) V := by
    rw [he]
    intro q hq
    exact (ContDiffAt.comp (f := v) (g := positiveConformalValue i) q
      (positiveConformalValue_contDiffAt i hq.2)
      (hv.contDiffAt (hU.mem_nhds hq.1))).contDiffWithinAt
  have hzero (j : Fin 3) : |canonicalCoefficientComponent j A p| ≤ M := by
    simpa only [mixedDerivative, iteratedDeriv_zero] using hraw j 0 0 (by omega)
  have hav : |A.a p| ≤ M := by simpa [canonicalCoefficientComponent] using hzero 0
  have hbv : |A.b p| ≤ M := by simpa [canonicalCoefficientComponent] using hzero 1
  have hcv : |A.c p| ≤ M := by simpa [canonicalCoefficientComponent] using hzero 2
  have hvjets (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k v p‖ ≤ (2 : ℝ) ^ k * M := by
    have hj (j : Fin 3) :
        ‖iteratedFDeriv ℝ k (canonicalCoefficientComponent j A) p‖ ≤ (2 : ℝ) ^ k * M :=
      norm_iteratedFDeriv_le_of_mixedDerivative hU (hA j) k hp hM
        (fun s t hst => by simpa only [Real.norm_eq_abs] using
          hraw j s t (hst.trans_le hk))
    have haj : ‖iteratedFDeriv ℝ k A.a p‖ ≤ (2 : ℝ) ^ k * M := by
      simpa [canonicalCoefficientComponent] using hj 0
    have hbj : ‖iteratedFDeriv ℝ k A.b p‖ ≤ (2 : ℝ) ^ k * M := by
      simpa [canonicalCoefficientComponent] using hj 1
    have hcj : ‖iteratedFDeriv ℝ k A.c p‖ ≤ (2 : ℝ) ^ k * M := by
      simpa [canonicalCoefficientComponent] using hj 2
    have ha' := (ha.contDiffAt (hU.mem_nhds hp)).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
    have hb' := (hb.contDiffAt (hU.mem_nhds hp)).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
    have hc' := (hc.contDiffAt (hU.mem_nhds hp)).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
    change ‖iteratedFDeriv ℝ k (fun q => (A.a q, A.b q, A.c q)) p‖ ≤ _
    rw [iteratedFDeriv_prodMk ha' (hb'.prodMk hc') le_rfl,
      ContinuousMultilinearMap.opNorm_prod,
      iteratedFDeriv_prodMk hb' hc' le_rfl, ContinuousMultilinearMap.opNorm_prod]
    exact max_le haj (max_le hbj hcj)
  have hcomp := norm_iteratedFDeriv_comp_le_partition_sum
    (positiveConformalValue_contDiffAt i hpV) hvp (a + b)
  have hsum : ‖iteratedFDeriv ℝ (a + b) (positiveConformalValue i ∘ v) p‖ ≤ C (a + b) := by
    apply hcomp.trans
    apply Finset.sum_le_sum
    intro π _
    exact mul_le_mul
      (houter i π.length (π.length_le.trans hab) (v p) hav hbv hcv hal hdet)
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => hvjets (π.partSize j) ((π.partSize_le j).trans hab)))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) hR.le
  have hs : C (a + b) ≤ ∑ n : Fin 4, C n :=
    Finset.single_le_sum (f := fun n : Fin 4 => C n)
      (fun n _ => hC n) (Finset.mem_univ (⟨a + b, by omega⟩ : Fin 4))
  have hm := abs_mixedDerivative_le_norm_iteratedFDeriv hV hfield a b hp'
  rw [he] at hm ⊢
  exact hm.trans (hsum.trans (hs.trans (le_add_of_nonneg_left zero_le_one)))

/-- Named actual finite data for the two coordinate columns and the
positive height. The log-height is included because the middle height is
one and the endpoint extension uses its logarithm. -/
def N01PositiveConformalCircleInputs
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε r κ B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ,
    κ ≤ positiveConformalSpeed (originalCoefficients D S C z) (r, θ) ∧
    0 < positiveConformalHeight (originalCoefficients D S C z) (r, θ) ∧
    (∀ i : Fin 4, ContDiffAt ℝ ∞
      (positiveConformalInputField i (originalCoefficients D S C z)) (r, θ)) ∧
    ∀ i : Fin 4, ∀ a b : ℕ, a + b ≤ 3 →
      |mixedDerivative a b
        (positiveConformalInputField i (originalCoefficients D S C z)) (r, θ)| ≤ B

/-- The same common neighborhood now gives actual finite speed, shear,
height, and log-height jets. No extra state restriction is imposed after
the endpoint is selected. -/
theorem n01_exists_positiveConformalCircle_finite_inputs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ r ∈ radialCore D, 0 < deriv D.w r → ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧
        N01PositiveConformalCircleInputs D S C base' ε' r κ B := by
  obtain ⟨base', ε', hb, hε', hε, hinputs⟩ := n01_exists_positiveCircle_finite_inputs hS hT hN
  obtain ⟨_, hD⟩ := hN.1.1
  refine ⟨base', ε', hb, hε', hε, ?_⟩
  intro r hr hrpos
  obtain ⟨κ, M, hκ, hM, hvalues, hjets⟩ := hinputs r hr hrpos
  have hw : 0 < D.w r := hD.1.2.2.2.2.1 r hr
  obtain ⟨B, hB, hbound⟩ := exists_positiveConformal_threeJet_bound
    (div_pos hw (by norm_num : (0 : ℝ) < 8)) hκ hM.le
  refine ⟨Real.sqrt κ / (16 * D.w r), B,
    div_pos (Real.sqrt_pos.mpr hκ) (mul_pos (by norm_num) hw), hB, ?_⟩
  intro z hz hs θ
  have hz₀ := stateNeighborhood_mono S C hb hε hz
  have hvalues' := hvalues z hz hs θ
  have ha : 0 < (originalCoefficients D S C z).a (r, θ) :=
    (div_pos hw (by norm_num : (0 : ℝ) < 8)).trans_le hvalues'.2.1.1
  have hd : 0 < (originalCoefficients D S C z).a (r, θ) *
      (originalCoefficients D S C z).c (r, θ) -
        (originalCoefficients D S C z).b (r, θ) ^ 2 := hκ.trans_le hvalues'.2.2
  have hAs (i : Fin 3) := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz₀ hs i
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
  have hAa : ContDiffAt ℝ ∞ (originalCoefficients D S C z).a (r, θ) := by
    simpa [canonicalCoefficientComponent] using (hAs 0).contDiffAt (hU.mem_nhds hp)
  have hAb : ContDiffAt ℝ ∞ (originalCoefficients D S C z).b (r, θ) := by
    simpa [canonicalCoefficientComponent] using (hAs 1).contDiffAt (hU.mem_nhds hp)
  have hAc : ContDiffAt ℝ ∞ (originalCoefficients D S C z).c (r, θ) := by
    simpa [canonicalCoefficientComponent] using (hAs 2).contDiffAt (hU.mem_nhds hp)
  have hf := contDiffAt_positiveConformalFields hAa hAb hAc ha hd
  have hval := positiveConformal_values ha hd
  refine ⟨?_, hval.2.1, ?_, ?_⟩
  · unfold positiveConformalSpeed
    exact (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hw) ha).mpr
      (mul_le_mul (Real.sqrt_le_sqrt hvalues'.2.2) hvalues'.2.1.2 ha.le (Real.sqrt_nonneg _))
  · intro i
    unfold positiveConformalInputField
    split_ifs
    · exact hf.1
    · exact hf.2.1
    · exact hf.2.2
    · exact hf.2.2.log hval.2.1.ne'
  · exact hbound (annularOpen D) hU (originalCoefficients D S C z) hAs
      (r, θ) hp hvalues'.2.1.1 hvalues'.2.2 (hjets z hz hs θ)

end ContinuousFlexibility.Analysis
