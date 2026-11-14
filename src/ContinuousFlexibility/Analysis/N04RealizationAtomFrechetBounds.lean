module

public import ContinuousFlexibility.Analysis.N04RealizationAtomJets
public import ContinuousFlexibility.Analysis.N07aCanonicalAtomBounds
public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Fréchet bounds with the original sampled coefficient envelope

The actual scalar atoms on the canonical interval retain their sampled E0
power when mixed derivatives are converted to Fréchet operator norms. The
conversion is uniform over all atoms and pieces and uses one fixed state
loss. No sampled subpower envelope replaces the coefficient power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n04Realization_mixedJet_frechetEnvelope
    (n : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∀ (U : Set PolarPoint), IsOpen U →
      ∀ (f : PolarPoint → ℝ), ContDiffOn ℝ ∞ f U →
        ∀ E rho : ℝ, 1 ≤ E → 0 ≤ rho →
          (∀ i j : ℕ, i + j ≤ n → ∀ x ∈ U,
            |mixedDerivative i j f x| ≤ A * E ^ A * rho) →
          ∀ x ∈ U, ‖iteratedFDeriv ℝ n f x‖ ≤ B * E ^ B * rho := by
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack ((2 : ℝ) ^ n * A) A
  refine ⟨B, hB, ?_⟩
  intro U hU f hf E rho hE hrho hjet x hx
  have hM : 0 ≤ A * E ^ A * rho :=
    mul_nonneg (mul_nonneg hA.le
      (Real.rpow_nonneg (zero_le_one.trans hE) _)) hrho
  have hnorm := norm_iteratedFDeriv_le_of_mixedDerivative hU hf n hx hM
    (fun i j hij => by
      rw [Real.norm_eq_abs]
      exact hjet i j hij.le x hx)
  calc
    ‖iteratedFDeriv ℝ n f x‖ ≤ (2 : ℝ) ^ n * (A * E ^ A * rho) := hnorm
    _ = ((2 : ℝ) ^ n * A * E ^ A) * rho := by ring
    _ ≤ (B * E ^ B) * rho := mul_le_mul_of_nonneg_right (hpack E hE) hrho

private theorem n04Realization_allOrderEnvelope_repack
    {P Q : ℕ → ℕ → ℝ → Prop}
    (hP : ∃ d : ℕ, ∀ n : ℕ, ∃ A : ℝ, 0 < A ∧ P d n A)
    (hPQ : ∀ d n A, 0 < A → P d n A → ∃ B : ℝ, 0 < B ∧ Q d n B) :
    ∃ d : ℕ, ∀ n : ℕ, ∃ B : ℝ, 0 < B ∧ Q d n B := by
  obtain ⟨d, hd⟩ := hP
  refine ⟨d, fun n => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hd n
  exact hPQ d n A hA hbound

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- The inverse affine coordinate is a left inverse on the entire plane. -/
theorem n04Realization_unitInverse_unitPoint
    {m : ℕ} (hlen : K.left m < K.right m) (p : PolarPoint) :
    n07aCanonicalUnitInversePoint K m (canonicalUnitPoint K m p) = p := by
  have hne : K.right m - K.left m ≠ 0 := (sub_pos.mpr hlen).ne'
  apply Prod.ext
  · change (K.left m + (K.right m - K.left m) * p.1 - K.left m) /
      (K.right m - K.left m) = p.1
    field_simp [hne]
    ring
  · rfl

/-- The existing canonical atom field is the same complete function after
undoing the unit-interval substitution. -/
theorem n04Realization_canonicalAtom_unit_identity
    (z : Parameter S) (m : ℕ) (a : Atom) (hlen : K.left m < K.right m) :
    EqOn ((n07aCanonicalAtomField D T S C L K a z m) ∘ canonicalUnitPoint K m)
      (atom D T S C L K (liftSectorParameter S C z) m a) unitStrip := by
  intro p _
  simp only [n07aCanonicalAtomField, Function.comp_apply,
    n04Realization_unitInverse_unitPoint hlen p]

/-- Any actual scalar field identified with an atom has the same Fréchet
bound. Its smoothness is checked on its genuine open canonical domain. -/
theorem n04Realization_canonicalAtom_frechet_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hlen : ∀ m, K.left m < K.right m)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ d : ℕ, ∀ n : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ m a (f : PolarPoint → ℝ),
          ContDiffOn ℝ ∞ f (canonicalOpen S K m) →
          EqOn (f ∘ canonicalUnitPoint K m) (atom D T S C L K z m a) unitStrip →
          ∀ x ∈ canonicalOpen S K m,
            ‖iteratedFDeriv ℝ n f x‖ ≤ B * T.E0 (T.sample (K.cell m)) ^ B *
              (1 + stateGrading S (n + d) (z.1 - C.referenceState) + |z.2|) := by
  refine n04Realization_allOrderEnvelope_repack
    (P := fun d n A => N04RealizationCanonicalAtomBoundAtOrder D T S C L K base d ε n A)
    (hP := n04Realization_canonicalAtom_jet_bounds
      (S := S) (C := C) (L := L) (K := K) (base := base) (ε := ε)
      hD hT hrefState href hcur hlen hfloor) ?_
  intro d n A hA hjet
  obtain ⟨B, hB, hbound⟩ := n04Realization_mixedJet_frechetEnvelope n hA
  refine ⟨B, hB, fun z hz hs m a f hf heq x hx => ?_⟩
  exact hbound (canonicalOpen S K m) (isOpen_Ioo.prod isOpen_univ) f hf
    (T.E0 (T.sample (K.cell m)))
    (1 + stateGrading S (n + d) (z.1 - C.referenceState) + |z.2|) (hfloor m)
    (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _))
    (fun i j hij y hy => hjet z hz hs m a f heq i j hij y hy) x hx

end ContinuousFlexibility.Analysis
