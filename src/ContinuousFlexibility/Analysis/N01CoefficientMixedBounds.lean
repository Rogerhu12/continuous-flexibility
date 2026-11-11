import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientRegularity
import ContinuousFlexibility.Analysis.N01OpticalSpeedJetBounds
import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity
import ContinuousFlexibility.Analysis.MixedDerivativeLocality
import ContinuousFlexibility.Analysis.PolynomialJetComposition

/-!
# Uniform spatial jets of the actual original coefficients

The zeroth parameter jet in N01 bounds each actual coefficient
difference. Its positive height factor absorbs every fixed sample power.
The reference coefficients are the radial functions w, 0, and w'/r,
whose jets are uniformly bounded on the compact annulus. This yields
uniform ordinary mixed and Fréchet jets of the original coefficients.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01CoefficientMixedBoundsStateSMul
    (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

theorem mixedDerivative_radial_field (f : ℝ → ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q : PolarPoint => f q.1) p =
      if b = 0 then iteratedDeriv a f p.1 else 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [mixedDerivative, iteratedDeriv_zero, ↓reduceIte]
  · have hzero (r : ℝ) : iteratedDeriv b (fun _ : ℝ => f r) p.2 = 0 := by
      simp only [iteratedDeriv_const, if_neg hb]
    simp only [mixedDerivative, hzero, iteratedDeriv_const, ite_self, if_neg hb]

theorem N01Properties.coefficientFamily_uniform_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) (s : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m i a b p, a + b ≤ s → p.1 ∈ D.cells m →
      |coefficientFamily D S C i a b p z| ≤ A := by
  let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.1 0 s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  obtain ⟨A, hA, hweight⟩ :=
    materialSample_H_E0_envelope hT hN.1.1 (γ := (3 / 4 : ℝ)) (by norm_num) B
  let Q := 1 + pairGrading (stateGrading S) realGrading (s + loss)
    (z - (C.referenceState, 0))
  have hQ : 0 ≤ Q := add_nonneg zero_le_one (apply_nonneg _ _)
  have hpoint : ∀ m i a b p, a + b ≤ s → p.1 ∈ D.cells m →
      |coefficientFamily D S C i a b p z| ≤ B * A * Q := by
    intro m i a b p hab hp
    let dataJ := hdata.choose_spec.2 m i a b p hab hp
    let J := dataJ.choose
    have hraw : |J.D 0 z Fin.elim0| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample m) ^ B * Q := by
      simpa only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
        mul_one, add_zero, Q, B, J] using dataJ.choose_spec z hz Fin.elim0
    have hzero : J.D 0 z Fin.elim0 = coefficientFamily D S C i a b p z := J.zero z hz
    have hM : B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample m) ^ B * Q ≤ B * A * Q := by
      have h := mul_le_mul_of_nonneg_left (hweight m) (mul_nonneg hB.le hQ)
      convert h using 1 <;> ring
    exact (congrArg abs hzero).symm.le.trans (hraw.trans hM)
  exact ⟨B * A * Q, mul_nonneg (mul_nonneg hB.le hA.le) hQ, hpoint⟩

theorem N01Properties.reference_coefficient_smooth_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (i : Fin 3) :
    let f : PolarPoint → ℝ :=
      if i = 0 then (originalCoefficients D S C (C.referenceState, 0)).a else
      if i = 1 then (originalCoefficients D S C (C.referenceState, 0)).b else
        (originalCoefficients D S C (C.referenceState, 0)).c
    ContDiffOn ℝ ∞ f (annularOpen D) ∧
      ∀ a b : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ annularOpen D,
        |mixedDerivative a b f p| ≤ A := by
  let g : ℝ → ℝ := if i = 0 then D.w else
    if i = 1 then fun _ => 0 else fun r => deriv D.w r / r
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hs : ContDiffOn ℝ ∞ g (Ioi (0 : ℝ)) := by
    dsimp only [g]
    split_ifs
    · exact hw.contDiffOn
    · exact contDiffOn_const
    · exact (contDiff_infty_iff_deriv.mp hw).2.contDiffOn.div contDiffOn_id
        (fun r hr => (ne_of_gt hr))
  have heq : (if i = 0 then (originalCoefficients D S C (C.referenceState, 0)).a else
      if i = 1 then (originalCoefficients D S C (C.referenceState, 0)).b else
        (originalCoefficients D S C (C.referenceState, 0)).c) =
      (fun p : PolarPoint => g p.1) := by
    funext p
    dsimp only [g]
    split_ifs
    · exact (hN.reference_coefficients p).1
    · exact (hN.reference_coefficients p).2.1
    · exact (hN.reference_coefficients p).2.2
  dsimp only
  rw [heq]
  constructor
  · simpa only [Function.comp_def] using hs.comp contDiffOn_fst
      (show MapsTo (fun p : PolarPoint => p.1) (annularOpen D) (Ioi (0 : ℝ))
        from fun p hp => hg.1.trans hp.1.1)
  · intro a b
    obtain ⟨A, hA, hb⟩ := scalar_positive_interval_jet_bound
      (a := D.a) (b := D.b) hg.1 hs a
    refine ⟨A, hA, fun p hp => ?_⟩
    rw [mixedDerivative_radial_field]
    split_ifs
    · simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        hb p.1 ⟨hp.1.1.le, hp.1.2.le⟩
    · simpa only [abs_zero] using hA

theorem N01Properties.original_coefficient_contDiffOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) :
    ContDiffOn ℝ ∞
      (if i = 0 then (originalCoefficients D S C z).a else
        if i = 1 then (originalCoefficients D S C z).b else
          (originalCoefficients D S C z).c) (annularOpen D) := by
  intro p hp
  obtain ⟨ha, hb, hc⟩ := hN.originalCoefficients_contDiffAt hS hT hz hsector hp
  split_ifs
  · exact ha.contDiffWithinAt
  · exact hb.contDiffWithinAt
  · exact hc.contDiffWithinAt

theorem N01Properties.original_coefficient_mixed_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) (a b : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m p, p.1 ∈ D.cells m →
      |mixedDerivative a b
        (if i = 0 then (originalCoefficients D S C z).a else
          if i = 1 then (originalCoefficients D S C z).b else
            (originalCoefficients D S C z).c) p| ≤ A := by
  obtain ⟨A, hA, hdiff⟩ := hN.coefficientFamily_uniform_bound hT hz (a + b)
  obtain ⟨href, hbounds⟩ := hN.reference_coefficient_smooth_jets i
  obtain ⟨B, hB, hb⟩ := hbounds a b
  have hf := hN.original_coefficient_contDiffOn hS hT hz hsector i
  have hpart : RadialPartition D := hN.1.1.choose_spec.2.1
  refine ⟨A + B, add_nonneg hA hB, fun m p hp => ?_⟩
  have hpD : p ∈ annularOpen D := ⟨hpart.2.2.2.1 m hp, mem_univ _⟩
  have hsub := mixedDerivative_sub_of_contDiffOn
    (isOpen_Ioo.prod isOpen_univ) hf href a b hpD
  change coefficientFamily D S C i a b p z = _ at hsub
  calc
    _ = |coefficientFamily D S C i a b p z +
        mixedDerivative a b
          (if i = 0 then (originalCoefficients D S C (C.referenceState, 0)).a else
            if i = 1 then (originalCoefficients D S C (C.referenceState, 0)).b else
              (originalCoefficients D S C (C.referenceState, 0)).c) p| := by
                rw [hsub, sub_add_cancel]
    _ ≤ |coefficientFamily D S C i a b p z| +
        |mixedDerivative a b
          (if i = 0 then (originalCoefficients D S C (C.referenceState, 0)).a else
            if i = 1 then (originalCoefficients D S C (C.referenceState, 0)).b else
              (originalCoefficients D S C (C.referenceState, 0)).c) p| := abs_add_le _ _
    _ ≤ A + B := add_le_add (hdiff m i a b p le_rfl hp) (hb p hpD)

theorem N01Properties.original_coefficient_fderiv_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m p, p.1 ∈ D.cells m →
      ‖iteratedFDeriv ℝ n
        (if i = 0 then (originalCoefficients D S C z).a else
          if i = 1 then (originalCoefficients D S C z).b else
            (originalCoefficients D S C z).c) p‖ ≤ A := by
  let f : PolarPoint → ℝ := if i = 0 then (originalCoefficients D S C z).a else
    if i = 1 then (originalCoefficients D S C z).b else (originalCoefficients D S C z).c
  have hbound (k : ℕ) (_hk : k ≤ n) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p, p ∈ D.cells m ×ˢ (univ : Set ℝ) →
        |mixedDerivative k (n - k) f p| ≤ A * (1 : ℝ) ^ P := by
    obtain ⟨A, hA, hb⟩ := hN.original_coefficient_mixed_jets
      hS hT hz hsector i k (n - k)
    exact ⟨A, 0, hA, le_rfl, fun m p hp => by
      simpa only [Real.rpow_zero, mul_one] using hb m p hp.1⟩
  obtain ⟨A, P, hA, _, hb⟩ := finite_polynomial_majorant (fun _ : ℕ => (1 : ℝ))
    (fun _ => le_rfl) (fun m => D.cells m ×ˢ (univ : Set ℝ))
    (fun k _ p => |mixedDerivative k (n - k) f p|) n hbound
  refine ⟨(2 : ℝ) ^ n * A, mul_nonneg (pow_nonneg (by norm_num) _) hA, fun m p hp => ?_⟩
  have hpart : RadialPartition D := hN.1.1.choose_spec.2.1
  apply norm_iteratedFDeriv_le_of_mixedDerivative
    (isOpen_Ioo.prod isOpen_univ)
    (hN.original_coefficient_contDiffOn hS hT hz hsector i) n
    (show p ∈ annularOpen D from ⟨hpart.2.2.2.1 m hp, mem_univ _⟩) hA
  intro a b hab
  have hbn : b = n - a := by omega
  rw [hbn, Real.norm_eq_abs]
  simpa only [Real.one_rpow, mul_one] using hb a (by omega) m p ⟨hp, mem_univ _⟩

end ContinuousFlexibility.Statements
