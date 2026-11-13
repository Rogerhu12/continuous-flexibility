import ContinuousFlexibility.Analysis.WholeReferenceGaugeUnitMaterialGeometry
import ContinuousFlexibility.Analysis.RetainedPositiveMaterialRatioJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeMaterialRatioJets
import ContinuousFlexibility.Analysis.WholeReferenceGaugeEnvelopeRatioJets
import ContinuousFlexibility.Analysis.CanonicalStaticAtomRegularity

/-!
# All six actual material reference ratios on the same whole atlas

The actual unit point has a uniformly bounded endpoint-coordinate distance
to the original stored sample. The three scalar weight estimates therefore
apply to every negative half and positive whole component. Unit rescaling
uses only the positive physical width. The explicit envelope enlargement
is differentiated as a new function and supplies the floor for finite
packing; no floor is assumed for the original material datum.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open CanonicalGeometry
open scoped ContDiff BigOperators

def canonicalMaterialRatioSelector (envelope useM inverse : Bool) : Atom :=
  if envelope then canonicalE0Atom inverse else canonicalHMAtom useM inverse

theorem canonical_materialRatioAtom_exists_selector {a : Atom}
    (ha : CanonicalMaterialRatioAtom a) :
    ∃ envelope useM inverse, a = canonicalMaterialRatioSelector envelope useM inverse := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨false, false, false, rfl⟩
  · exact ⟨false, false, true, rfl⟩
  · exact ⟨false, true, false, rfl⟩
  · exact ⟨false, true, true, rfl⟩
  · exact ⟨true, false, false, rfl⟩
  · exact ⟨true, false, true, rfl⟩

theorem canonicalMaterialRatioSelector_eq_normalizedPower
    {D : ReferenceData} {U : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (envelope useM inverse : Bool) :
    atom D U S C L K z m (canonicalMaterialRatioSelector envelope useM inverse) =
      fun p => materialRatioNormalizedPower U envelope useM (if inverse then -1 else 1)
        (U.sample (K.cell m)) (physicalUnitPoint K m p).1 := by
  cases envelope with
  | false =>
    simpa only [canonicalMaterialRatioSelector, materialRatioNormalizedPower,
      Bool.false_eq_true, ite_false] using
      canonicalHMAtom_eq_normalizedPower (D := D) (T := U) (C := C) (L := L) (K := K)
        z m useM inverse
  | true =>
    simpa only [canonicalMaterialRatioSelector, materialRatioNormalizedPower,
      ite_true] using
      canonicalE0Atom_eq_normalizedPower (D := D) (T := U) (C := C) (L := L) (K := K)
        z m inverse

variable {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S₀ K₀ q length) (hS₀ : IsSelectedTail S₀)
  (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
  {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
  (hw : Γ.reference.w = P.pair.profile)
  (hcoordinates : R11aRetainedCoordinates P Γ)
  {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
  (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
  (hfield : N04bFieldRegularity Γ.reference S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex Γ.reference) (e : ℕ ≃ N04WholePieceIndex Γ.reference)
  (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
  (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
  (ψ χ : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
    PolarPoint → PolarPoint)
  (h₀ : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
    PolarPoint → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
      PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) →
      PolarPoint → ℝ)
  (N : Set ℝ)

include P hS₀ hband hq hΓ hw hcoordinates hcell in
/-- All orders of every actual ratio on every piece, with separate
coefficient and exponent. The material datum may change only subject to
the displayed true material contract and equality of stored samples. -/
theorem n04WholeReferenceGauge_materialRatio_jets
    (U : MaterialData) (hU : IsMaterialData Γ.reference U)
    (hsample : U.sample = T.sample) (envelope useM inverse : Bool) (a : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ z m, ∀ p ∈ unitStrip, ∀ b : ℕ,
      |mixedDerivative a b
        (atom Γ.reference U S C L V z m
          (canonicalMaterialRatioSelector envelope useM inverse)) p| ≤
            B * U.E0 (U.sample (V.cell m)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  obtain ⟨A₀, hA₀, hgeometry⟩ := n04WholeReferenceGauge_unit_material_geometry
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  obtain ⟨B, A, hB, hA, hphysical⟩ :=
    materialRatio_normalized_physical_jets_of_bounded_X_shift
      hU hΓ.2.1 envelope useM (if inverse then -1 else 1) a hA₀
  refine ⟨|Γ.reference.b - Γ.reference.a| ^ a * B, A,
    mul_nonneg (pow_nonneg (abs_nonneg _) _) hB, hA, ?_⟩
  intro z m p hp b
  let f := materialRatioNormalizedPower U envelope useM (if inverse then -1 else 1)
    (U.sample (V.cell m))
  let d := V.physicalLeft m
  let c := V.physicalRight m - V.physicalLeft m
  have hc : 0 < c := (hgeometry m).1
  have hwidth : c ≤ Γ.reference.b - Γ.reference.a := (hgeometry m).2.1
  have hpoint := (hgeometry m).2.2 p hp
  have hs := materialSample_mem_interval hΓ.2.1 hU (V.cell m)
  have hEs : 0 < U.E0 (U.sample (V.cell m)) := (hU.2.1 _ hs).2.2.1
  have hdist :
      |endpointX 1 (Statements.endpointDistance Γ.reference (physicalUnitPoint V m p).1) -
        endpointX 1 (Statements.endpointDistance Γ.reference (U.sample (V.cell m)))| ≤ A₀ := by
    rw [hsample]
    exact hpoint.2
  have hvalue := hphysical (physicalUnitPoint V m p).1
    (U.sample (V.cell m)) hpoint.1 hs hdist
  rw [canonicalMaterialRatioSelector_eq_normalizedPower]
  change |mixedDerivative a b (fun v => f (d + c * v.1)) p| ≤ _
  rw [n08_mixedDerivative_radial (fun r => f (d + c * r))]
  by_cases hb : b = 0
  · rw [if_pos hb, n07a_iteratedDeriv_comp_affine, abs_mul, abs_pow]
    have hpow : |c| ^ a ≤ |Γ.reference.b - Γ.reference.a| ^ a := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_of_pos hc]
      exact hwidth.trans (le_abs_self _)
    calc
      _ ≤ |c| ^ a * (B * U.E0 (U.sample (V.cell m)) ^ A) :=
        mul_le_mul_of_nonneg_left hvalue (pow_nonneg (abs_nonneg _) _)
      _ ≤ |Γ.reference.b - Γ.reference.a| ^ a *
          (B * U.E0 (U.sample (V.cell m)) ^ A) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hB (Real.rpow_nonneg hEs.le _))
      _ = _ := by ring
  · rw [if_neg hb, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) hB)
      (Real.rpow_nonneg hEs.le _)

include P hS₀ hband hq hΓ hw hcoordinates hcell in
/-- The six actual reference atoms satisfy the finite-order spatial
bound on the same atlas. The explicitly enlarged E0 is differentiated;
its genuine floor is used only after the separate bounds are proved. -/
theorem n04WholeReferenceGauge_materialRatioReferenceJets_enlargedMaterialData :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let U := enlargedMaterialData T
    (∀ z m a, CanonicalMaterialRatioAtom a →
      ContDiffOn ℝ ∞ (atom Γ.reference U S C L V z m a) unitStrip ∧
      ∀ p ∈ unitStrip,
        atom Γ.reference U S C L V z m a (p + (0, Real.pi)) =
          atom Γ.reference U S C L V z m a p) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z m a, CanonicalMaterialRatioAtom a →
      ∀ p ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (atom Γ.reference U S C L V z m a) p| ≤
          B * U.E0 (U.sample (V.cell m)) ^ B := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let U := enlargedMaterialData T
  have hU : IsMaterialData Γ.reference U := isMaterialData_enlargedMaterialData hΓ.2.1 hT
  have hsample : U.sample = T.sample := rfl
  obtain ⟨A₀, hA₀, hgeometry⟩ := n04WholeReferenceGauge_unit_material_geometry
    P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
  refine ⟨?_, ?_⟩
  · intro z m a ha
    refine ⟨canonical_staticAtom_contDiffOn_of_core hU z m (Or.inr ha) ?_, ?_⟩
    · intro p hp
      exact ((hgeometry m).2.2 p hp).1
    · intro p hp
      exact canonical_staticAtom_angle_period z m (Or.inr ha) p
  · intro s
    let I := Fin (s + 1) × Bool × Bool × Bool
    have hfamily (i : I) := n04WholeReferenceGauge_materialRatio_jets
      P hS₀ hband hq hΓ hw hcoordinates hT hS hN hfield e₀ e cell hcell ψ χ h₀ τ σ Q N
      U hU hsample i.2.1 i.2.2.1 i.2.2.2 i.1.val
    choose C₀ A hC₀ hA hjet using hfamily
    choose B hB hpack using fun i : I => coefficientEnvelope_pack (C₀ i) (A i)
    let M : ℝ := 1 + ∑ i : I, B i
    have hsum : 0 ≤ ∑ i : I, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
    have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one hsum
    have hBM (i : I) : B i ≤ M :=
      (Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one)
    refine ⟨M, hM, ?_⟩
    intro z m a ha p hp i j hij
    obtain ⟨envelope, useM, inverse, rfl⟩ := canonical_materialRatioAtom_exists_selector ha
    let k : I := (⟨i, by omega⟩, envelope, useM, inverse)
    let t := U.E0 (U.sample (V.cell m))
    have hs := materialSample_mem_interval hΓ.2.1 hT (V.cell m)
    have hfloor : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hs
    have hh := hjet k z m p hp j
    calc
      _ ≤ C₀ k * t ^ A k := hh
      _ ≤ B k * t ^ B k := hpack k t hfloor
      _ ≤ M * t ^ M := mul_le_mul (hBM k)
        (Real.rpow_le_rpow_of_exponent_le hfloor (hBM k))
        (Real.rpow_nonneg (zero_le_one.trans hfloor) _) hM.le

end ContinuousFlexibility.Analysis
