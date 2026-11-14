import ContinuousFlexibility.Analysis.N04PrincipalPairAlgebra
import ContinuousFlexibility.Analysis.N04PrincipalNegativeReciprocalDifference
import ContinuousFlexibility.Analysis.N04PrincipalDataTowers

/-!
# Restriction and inversion of paired current families

The reciprocal is formed on one open domain with a uniform inverse-value
envelope. The full current and reference towers are inverted separately;
the exact reciprocal difference keeps the original material weight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U V : Set X} {Ω : Set PolarPoint}

theorem n04Principal_weightedTower_restrict
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E W : ι → ℝ)
    {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (hV : IsOpen V) (hVU : V ⊆ U)
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base E W
      (fun m => n04Principal_mixedRegularity_restrict (R m) hV hVU) := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  exact ⟨B, hB, fun m a b hab q hq x hx hlow v =>
    hbound m a b hab q hq x (hVU hx) hlow v⟩

namespace N04PrincipalPairBounds

variable {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {f : ι → X → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}

theorem restrict (hf : N04PrincipalPairBounds p E W (U := U) (Ω := Ω) f f₀)
    (hV : IsOpen V) (hVU : V ⊆ U) :
    N04PrincipalPairBounds p E W (U := V) (Ω := Ω) f f₀ := by
  obtain ⟨base, RF, RR, RD, hF, hR, hD⟩ := hf
  exact ⟨base, (fun m => n04Principal_mixedRegularity_restrict (RF m) hV hVU),
    (fun m => n04Principal_mixedRegularity_restrict (RR m) hV hVU),
    (fun m => n04Principal_mixedRegularity_restrict (RD m) hV hVU),
    n04Principal_weightedTower_restrict p base E (fun _ => 1) RF hV hVU hF,
    n04Principal_weightedTower_restrict p base E (fun _ => 1) RR hV hVU hR,
    n04Principal_weightedTower_restrict p base E W RD hV hVU hD⟩

theorem inv (hf : N04PrincipalPairBounds p E W (U := U) (Ω := Ω) f f₀)
    (hp : Monotone p) (hI : HasInterpolation p) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 < W m)
    (hnonzero : ∀ m x, x ∈ U → ∀ q ∈ Ω, f m x q ≠ 0)
    (hrefnonzero : ∀ m q, q ∈ Ω → f₀ m q ≠ 0)
    (hinverse : ∃ B : ℝ, 0 < B ∧ ∀ m x, x ∈ U → ∀ q ∈ Ω,
      |(f m x q)⁻¹| ≤ B * E m ^ B)
    (hrefinverse : ∃ B : ℝ, 0 < B ∧ ∀ m q, q ∈ Ω →
      |(f₀ m q)⁻¹| ≤ B * E m ^ B) :
    N04PrincipalPairBounds p E W (U := U) (Ω := Ω)
      (fun m x q => (f m x q)⁻¹) (fun m q => (f₀ m q)⁻¹) := by
  classical
  obtain ⟨base, RF, RR, RD, hF, hR, hD⟩ := hf
  let RI (m : ι) : MixedJetRegularity U Ω (fun x q => (f m x q)⁻¹) :=
    (RF m).n04PrincipalNegative_inv hU hΩ (hnonzero m)
  let RI₀ (m : ι) : MixedJetRegularity U Ω (fun _ q => (f₀ m q)⁻¹) :=
    (RR m).n04PrincipalNegative_inv hU hΩ (fun _ _ => hrefnonzero m)
  let RN₀ (m : ι) : MixedJetRegularity U Ω (fun _ q => -(f₀ m q)⁻¹) :=
    (RI₀ m).scalarComp hU hΩ isOpen_univ contDiff_neg.contDiffOn
      (fun _ _ _ _ => mem_univ _)
  let RDI (m : ι) : MixedJetRegularity U Ω
      (fun x q => (f m x q)⁻¹ - (f₀ m q)⁻¹) := by
    simpa only [sub_eq_add_neg] using (RI m).add (RN₀ m) hU hΩ
  have hi := n04PrincipalNegative_reciprocal_weightedTower p hp hI base base E hE
    hU hΩ f RF RI hF hnonzero hinverse
  have hr := n04PrincipalNegative_reciprocal_weightedTower p hp hI base base E hE
    hU hΩ (fun m _ => f₀ m) RR RI₀ hR
    (fun m _ _ => hrefnonzero m)
    ⟨hrefinverse.choose, hrefinverse.choose_spec.1,
      fun m _ _ => hrefinverse.choose_spec.2 m⟩
  let common : ℕ := max hi.choose hr.choose
  have hbi : hi.choose ≤ common := le_max_left _ _
  have hbr : hr.choose ≤ common := le_max_right _ _
  have hbase : base ≤ common :=
    (le_max_left _ _).trans (hi.choose_spec.1.trans hbi)
  have hIbound : N04PrincipalWeightedTowerBounds p common E (fun _ => 1) RI :=
    n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
      (fun _ => zero_le_one) hbi RI hi.choose_spec.2
  have hRbound : N04PrincipalWeightedTowerBounds p common E (fun _ => 1) RI₀ :=
    n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
      (fun _ => zero_le_one) hbr RI₀ hr.choose_spec.2
  have hDbound : N04PrincipalWeightedTowerBounds p common E W RD :=
    n04Principal_weightedTower_monoBase p hp E W hE (fun m => (hW m).le)
      hbase RD hD
  have hd := n04PrincipalNegative_reciprocalDifference_weightedTower p hp hI
    common common hU hΩ E W hE hW f f₀ RD RI RI₀ RDI
    hDbound hIbound hRbound hnonzero hrefnonzero
  have hcommon : common ≤ hd.choose := (le_max_left _ _).trans hd.choose_spec.1
  exact ⟨hd.choose, RI, RI₀, RDI,
    n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
      (fun _ => zero_le_one) hcommon RI hIbound,
    n04Principal_weightedTower_monoBase p hp E (fun _ => 1) hE
      (fun _ => zero_le_one) hcommon RI₀ hRbound,
    hd.choose_spec.2⟩

end N04PrincipalPairBounds

end ContinuousFlexibility.Analysis
