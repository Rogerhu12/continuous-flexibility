module

public import ContinuousFlexibility.Analysis.N03CoefficientStateNeighborhood
public import ContinuousFlexibility.Analysis.N01OriginalCoefficientStripJets
public import ContinuousFlexibility.Analysis.N04bFieldRegularity

/-!
# All actual corrected coefficient jets on the whole negative component

The genuine N03 difference estimate is added to the original N01 jets.
Only raw spatial smoothness of the actual corrected field is used in
this addition. The retained cell containing each negative component
allows the existing localized N01 bound to be used on its entire open
strip. One state neighborhood and one derivative loss precede every
component and derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem exists_lower_bound_map {P Q : ℝ → Prop} {lower : ℝ}
    (h : ∃ B : ℝ, lower ≤ B ∧ P B) (hmap : ∀ B, P B → Q B) :
    ∃ B : ℝ, lower ≤ B ∧ Q B := by
  obtain ⟨B, hB, hP⟩ := h
  exact ⟨B, hB, hmap B hP⟩

private theorem mixed_jet_le_difference_add
    {U : Set PolarPoint} (hU : IsOpen U) {f g : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ U) :
    |mixedDerivative a b f q| ≤
      |mixedDerivative a b (fun x => f x - g x) q| + |mixedDerivative a b g q| := by
  rw [mixedDerivative_sub_of_contDiffOn hU hf hg a b hq]
  calc
    _ = |(mixedDerivative a b f q - mixedDerivative a b g q) +
        mixedDerivative a b g q| := congrArg abs (by ring)
    _ ≤ _ := abs_add_le _ _

private theorem coefficient_jet_le_reference_add
    {U : Set PolarPoint} (hU : IsOpen U) {C A : SymmetricCoefficients}
    (hC : ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i C) U)
    (hA : ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i A) U)
    (ha : EqOn C.a A.a U) (a b : ℕ) {q : PolarPoint} (hq : q ∈ U)
    {X Y : ℝ} (hY : 0 ≤ Y)
    (href : ∀ i : Fin 3, |mixedDerivative a b (canonicalCoefficientComponent i A) q| ≤ X)
    (hdiff : |mixedDerivative a b (fun x => C.b x - A.b x) q| +
      |mixedDerivative a b (fun x => C.c x - A.c x) q| ≤ Y) :
    ∀ i : Fin 3, |mixedDerivative a b (canonicalCoefficientComponent i C) q| ≤ X + Y := by
  have hb : |mixedDerivative a b C.b q| ≤ Y + X :=
    (mixed_jet_le_difference_add hU
      (by simpa [canonicalCoefficientComponent] using hC 1)
      (by simpa [canonicalCoefficientComponent] using hA 1) a b hq).trans
        (add_le_add ((le_add_of_nonneg_right (abs_nonneg _)).trans hdiff)
          (by simpa [canonicalCoefficientComponent] using href 1))
  have hc : |mixedDerivative a b C.c q| ≤ Y + X :=
    (mixed_jet_le_difference_add hU
      (by simpa [canonicalCoefficientComponent] using hC 2)
      (by simpa [canonicalCoefficientComponent] using hA 2) a b hq).trans
        (add_le_add ((le_add_of_nonneg_left (abs_nonneg _)).trans hdiff)
          (by simpa [canonicalCoefficientComponent] using href 2))
  intro i
  fin_cases i
  · have he := mixedDerivative_eqOn_of_isOpen hU ha a b hq
    have hh : |mixedDerivative a b A.a q| ≤ X := by
      simpa [canonicalCoefficientComponent] using href 0
    simpa [canonicalCoefficientComponent] using
      (congrArg abs he).trans_le (hh.trans (le_add_of_nonneg_right hY))
  · simpa [canonicalCoefficientComponent, add_comm] using hb
  · simpa [canonicalCoefficientComponent, add_comm] using hc

private theorem coefficient_family_bound_of_difference
    {Z : Type*} (p : ℕ → Z → ℝ)
    (hp : ∀ i j : ℕ, i ≤ j → ∀ z, p i z ≤ p j z)
    (hnonneg : ∀ i z, 0 ≤ p i z) (V : Set Z)
    (A C : Z → SymmetricCoefficients) {U : Set PolarPoint} (hU : IsOpen U)
    (hA : ∀ z ∈ V, ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i (A z)) U)
    (hC : ∀ z ∈ V, ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i (C z)) U)
    (ha : ∀ z ∈ V, EqOn (C z).a (A z).a U) (d e : ℕ)
    (horiginal : ∀ s : ℕ, ∃ X : ℝ, 1 ≤ X ∧ ∀ z ∈ V,
      ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ U,
        |mixedDerivative a b (canonicalCoefficientComponent i (A z)) q| ≤
          X * (1 + p (s + d) z))
    (hdifference : ∀ a b : ℕ, ∃ Y : ℝ, 0 ≤ Y ∧ ∀ z ∈ V, ∀ q ∈ U,
      |mixedDerivative a b (fun x => (C z).b x - (A z).b x) q| +
        |mixedDerivative a b (fun x => (C z).c x - (A z).c x) q| ≤
          Y * (1 + p (a + b + e) z)) :
    ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ V, ∀ i : Fin 3,
      ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ U,
        |mixedDerivative a b (canonicalCoefficientComponent i (C z)) q| ≤
          B * (1 + p (s + max d e) z) := by
  classical
  choose Y hY hdiff using hdifference
  intro s
  obtain ⟨X, hX, horig⟩ := horiginal s
  let M : ℝ := ∑ a : Fin (s + 1), ∑ b : Fin (s + 1), Y a b
  have hM : 0 ≤ M := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hY a b
  have hYM (a b : ℕ) (hab : a + b ≤ s) : Y a b ≤ M := by
    have ha : a < s + 1 := by omega
    have hb : b < s + 1 := by omega
    exact (Finset.single_le_sum (f := fun j : Fin (s + 1) => Y a j)
      (fun j _ => hY a j) (Finset.mem_univ (⟨b, hb⟩ : Fin (s + 1)))).trans
        (Finset.single_le_sum (f := fun j : Fin (s + 1) => ∑ k : Fin (s + 1), Y j k)
          (fun j _ => Finset.sum_nonneg fun k _ => hY j k)
          (Finset.mem_univ (⟨a, ha⟩ : Fin (s + 1))))
  refine ⟨X + M, hX.trans (le_add_of_nonneg_right hM), ?_⟩
  intro z hz i a b hab q hq
  let W := 1 + p (s + max d e) z
  have hW : 0 ≤ W := add_nonneg zero_le_one (hnonneg _ _)
  have hreference (j : Fin 3) :
      |mixedDerivative a b (canonicalCoefficientComponent j (A z)) q| ≤ X * W :=
    (horig z hz j a b hab q hq).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ))
        (hp _ _ (Nat.add_le_add_left (le_max_left d e) s) z)) (zero_le_one.trans hX))
  have hd : |mixedDerivative a b (fun x => (C z).b x - (A z).b x) q| +
      |mixedDerivative a b (fun x => (C z).c x - (A z).c x) q| ≤ M * W :=
    (hdiff a b z hz q hq).trans
      (mul_le_mul (hYM a b hab) (add_le_add (le_refl (1 : ℝ))
        (hp _ _ (Nat.add_le_add hab (le_max_right d e)) z))
          (add_nonneg zero_le_one (hnonneg _ _)) hM)
  exact (coefficient_jet_le_reference_add hU (hC z hz) (hA z hz) (ha z hz)
    a b hq (mul_nonneg hM hW) hreference hd i).trans_eq (by ring)

def N03TotalCoefficientBoundAtOrder
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ)
    (m s : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
        |mixedDerivative a b (canonicalCoefficientComponent i (L.coefficients z)) q| ≤
          B * (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0)))

/-- The actual total corrected field has all mixed jets on every whole
negative component. The cell assignment is the one already supplied by
the explicit optical correction; no state-dependent choice is made. -/
theorem n03_totalCoefficient_commonNeighborhood_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε) (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m)) :
    ∃ outLoss base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
        N03TotalCoefficientBoundAtOrder S C L base' outLoss ε' m s B := by
  obtain ⟨corrLoss, base', ε', hb, hε', hεold, hdifference⟩ :=
    n03_correctedCoefficient_commonNeighborhood_fixed_loss
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
      (base := base) (loss := loss) (ε := ε) hS hT hN01 hN02 hN03 hA hB
  have hsub := stateNeighborhood_mono S C hb hεold
  refine ⟨max loss corrLoss, base', ε', hb, hε', hεold, ?_⟩
  intro m s
  have hends := hN01.2.2.2.1.1 m
  let ρ := min ((C.left m - D.a) / 2) ((D.b - C.right m) / 2)
  have hρ : 0 < ρ := lt_min (half_pos (sub_pos.mpr hends.1))
    (half_pos (sub_pos.mpr hends.2.2))
  have hphysical : Ioo (C.left m - ρ) (C.right m + ρ) ⊆ Ioo D.a D.b := by
    intro r hr
    have hl : ρ ≤ (C.left m - D.a) / 2 := min_le_left _ _
    have hu : ρ ≤ (D.b - C.right m) / 2 := min_le_right _ _
    constructor <;> linarith only [hr.1, hr.2, hl, hu, hends.1, hends.2.2]
  let U : Set PolarPoint := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hUAnn : U ⊆ annularOpen D := fun q hq =>
    ⟨⟨hends.1.trans hq.1.1, hq.1.2.trans hends.2.2⟩, hq.2⟩
  let V : Set (AnnularState S × ℝ) :=
    {z | z ∈ stateNeighborhood S C base' ε' ∧ stateSector S z.1}
  have hC : ∀ z ∈ V, ∀ i : Fin 3,
      ContDiffOn ℝ ∞ (canonicalCoefficientComponent i (L.coefficients z)) U := by
    intro z hz i
    have hh := hfield.smooth_coefficients z (hsub hz.1) hz.2
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hh.1.mono hUAnn
    · exact hh.2.1.mono hUAnn
    · exact hh.2.2.mono hUAnn
  have hOrig : ∀ z ∈ V, ∀ i : Fin 3,
      ContDiffOn ℝ ∞ (canonicalCoefficientComponent i (originalCoefficients D S C z)) U :=
    fun z hz i => (contDiffOn_originalCoefficientComponent_of_n01
      hS hT hN01 (hsub hz.1) hz.2 i).mono hUAnn
  have hinput (n : ℕ) : ∃ A : ℝ, 1 ≤ A ∧ ∀ z ∈ V,
      ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ n → ∀ q ∈ U,
        |mixedDerivative a b (canonicalCoefficientComponent i
          (originalCoefficients D S C z)) q| ≤
          A * (1 + pairGrading (stateGrading S) realGrading (n + loss)
            (z - (C.referenceState, 0))) := by
    exact exists_lower_bound_map
      (P := N01OriginalCoefficientStripBoundAtOrder D S C base loss ε (C.left m) (C.right m) n)
      (n01_originalCoefficient_strip_fixed_loss_bound
        (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
        hS hT hN01 hends.2.1.le hρ hphysical (j m) (hcell m) n)
      (fun A hbound z hz => hbound z (hsub hz.1) hz.2)
  exact exists_lower_bound_map
    (Q := N03TotalCoefficientBoundAtOrder S C L base' (max loss corrLoss) ε' m s)
    (coefficient_family_bound_of_difference
      (p := fun n z => pairGrading (stateGrading S) realGrading n (z - (C.referenceState, 0)))
      (fun _ _ hij z => tamePairGrading_monotone (stateGrading_monotone S)
        (fun _ _ _ => le_rfl) hij (z - (C.referenceState, 0)))
      (fun _ _ => apply_nonneg _ _) V (originalCoefficients D S C) L.coefficients hU
      hOrig hC (fun z hz q _ => hN03.1 z (hsub hz.1) hz.2 q) loss corrLoss hinput
      (fun a b => exists_lower_bound_map
        (P := N03CorrectedCoefficientStateBoundAtOrder D S C L base' corrLoss ε' m a b)
        (hdifference m a b) (fun B hbound z hz => hbound z hz.1 hz.2)) s)
    (fun B hbound z hz hs => hbound z ⟨hz, hs⟩)

end ContinuousFlexibility.Analysis
