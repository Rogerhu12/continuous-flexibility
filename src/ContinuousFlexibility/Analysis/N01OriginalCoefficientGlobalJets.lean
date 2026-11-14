module

public import ContinuousFlexibility.Analysis.N01CoefficientValueJets
public import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity
public import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope
public import ContinuousFlexibility.Analysis.LocalMixedProductBounds
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Actual original coefficient jets throughout the annulus

The N01 difference retains its original state loss. Material absorption
removes its sample factor uniformly over the actual partition. Reference
jets use one fixed radial compact set, independently of all components.
No root chart, strip radius, or reciprocal coefficient bound is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem radial_mixedDerivative_angle_zero {f : PolarPoint → ℝ}
    (hf : ∀ r θ : ℝ, f (r, θ) = f (r, 0)) (a b : ℕ) (r θ : ℝ) :
    mixedDerivative a b f (r, θ) = mixedDerivative a b f (r, 0) := by
  have hs (x : ℝ) : (fun η : ℝ => f (x, η)) = fun _ : ℝ => f (x, 0) :=
    funext (hf x)
  unfold mixedDerivative
  simp_rw [hs]
  simp only [iteratedDeriv_const]

private theorem radial_coefficient_compact_jet_bound
    (K : Fin 3 → PolarPoint → ℝ)
    (hK : ∀ i, ContDiffOn ℝ ∞ (K i) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (hangle : ∀ i r θ, K i (r, θ) = K i (r, 0))
    {l : ℝ} (hl : 0 < l) (u : ℝ) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q : PolarPoint, q.1 ∈ Icc l u → |mixedDerivative a b (K i) q| ≤ M := by
  let J : ℝ → ℝ := fun r =>
    ∑ i : Fin 3, ∑ a : Fin (s + 1), ∑ b : Fin (s + 1),
      |mixedDerivative a b (K i) (r, 0)|
  have hc (i : Fin 3) (a b : ℕ) :
      ContinuousOn (fun r : ℝ => |mixedDerivative a b (K i) (r, 0)|) (Icc l u) :=
    (((contDiffOn_mixedDerivative (isOpen_Ioi.prod isOpen_univ) (hK i) a b).continuousOn).comp'
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hl.trans_le hr.1, mem_univ _⟩)).abs
  have hJ : ContinuousOn J (Icc l u) :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun a _ =>
      continuousOn_finsetSum _ (fun b _ => hc i a b)))
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc l u)).exists_bound_of_continuousOn hJ
  refine ⟨|M|, abs_nonneg _, ?_⟩
  intro i a b hab q hq
  have ha : a < s + 1 := by omega
  have hb : b < s + 1 := by omega
  have ht : |mixedDerivative a b (K i) (q.1, 0)| ≤ J q.1 := by
    calc
      _ ≤ ∑ j : Fin (s + 1), |mixedDerivative a j (K i) (q.1, 0)| :=
        Finset.single_le_sum
          (f := fun j : Fin (s + 1) => |mixedDerivative a j (K i) (q.1, 0)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ (⟨b, hb⟩ : Fin (s + 1)))
      _ ≤ ∑ k : Fin (s + 1), ∑ j : Fin (s + 1),
          |mixedDerivative k j (K i) (q.1, 0)| :=
        Finset.single_le_sum
          (f := fun k : Fin (s + 1) => ∑ j : Fin (s + 1),
            |mixedDerivative k j (K i) (q.1, 0)|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          (Finset.mem_univ (⟨a, ha⟩ : Fin (s + 1)))
      _ ≤ J q.1 :=
        Finset.single_le_sum
          (f := fun k : Fin 3 => ∑ a : Fin (s + 1), ∑ b : Fin (s + 1),
            |mixedDerivative a b (K k) (q.1, 0)|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ =>
            Finset.sum_nonneg (fun _ _ => abs_nonneg _))) (Finset.mem_univ i)
  have he := congrArg abs (radial_mixedDerivative_angle_zero (hangle i) a b q.1 q.2)
  have hJM : J q.1 ≤ M := (le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs] using hM q.1 hq)
  exact he.trans_le (ht.trans (hJM.trans (le_abs_self M)))

/-- The reference fields are exactly `w`, `0`, and `w'/r`; their finite
jets have one bound on the fixed closed radial annulus, at all angles. -/
theorem N01Properties.reference_coefficient_mixed_global_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s →
      ∀ q : PolarPoint, q.1 ∈ Icc D.a D.b →
        |mixedDerivative a b (canonicalCoefficientComponent i
          (originalCoefficients D S C (C.referenceState, 0))) q| ≤ M := by
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have ha : (originalCoefficients D S C (C.referenceState, 0)).a =
      fun p : PolarPoint => D.w p.1 := funext (fun p => (hN.reference_coefficients p).1)
  have hb : (originalCoefficients D S C (C.referenceState, 0)).b =
      fun _ : PolarPoint => 0 := funext (fun p => (hN.reference_coefficients p).2.1)
  have hc : (originalCoefficients D S C (C.referenceState, 0)).c =
      fun p : PolarPoint => deriv D.w p.1 / p.1 :=
    funext (fun p => (hN.reference_coefficients p).2.2)
  refine radial_coefficient_compact_jet_bound
    (fun i => canonicalCoefficientComponent i (originalCoefficients D S C (C.referenceState, 0)))
    (fun i => ?_)
    (fun i r θ => originalCoefficientComponent_zeroParameter_angle_invariant
      D S C C.referenceState i r θ 0) hg.1 D.b s
  show ContDiffOn ℝ ∞
    (canonicalCoefficientComponent i (originalCoefficients D S C (C.referenceState, 0)))
    (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))
  unfold canonicalCoefficientComponent
  split_ifs
  · rw [ha]
    exact (hw.comp contDiff_fst).contDiffOn
  · rw [hb]
    exact contDiff_const.contDiffOn
  · rw [hc]
    exact (hwd.comp contDiff_fst).contDiffOn.fun_div contDiff_fst.contDiffOn
      (fun p hp => hp.1.ne')

def N01OriginalCoefficientGlobalBoundAtOrder (D : ReferenceData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (A : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ annularOpen D,
      |mixedDerivative a b (canonicalCoefficientComponent i
        (originalCoefficients D S C z)) q| ≤
        A * (1 + pairGrading (stateGrading S) realGrading (s + loss)
          (z - (C.referenceState, 0)))

/-- The actual N01 coefficient family gives a bound independent of the
physical component. Its state base, radius, and loss are unchanged. -/
theorem originalCoefficient_global_bound_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ N01OriginalCoefficientGlobalBoundAtOrder D S C base loss ε s A := by
  obtain ⟨B, hB, hdifference⟩ := coefficientFamily_value_bound_of_n01 hN s
  obtain ⟨K, hK, habsorb⟩ :=
    materialSample_H_E0_envelope hT hN.1.1 (by norm_num : (0 : ℝ) < 3 / 4) B
  obtain ⟨M, hM, hreference⟩ := N01Properties.reference_coefficient_mixed_global_bound hN s
  refine ⟨B * K + M, add_pos_of_pos_of_nonneg (mul_pos hB hK) hM, ?_⟩
  intro z hz hsector i a b hab q hq
  have hpart : RadialPartition D := hN.1.1.choose_spec.2.1
  have hex : ∃ m, D.localizer m q.1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hzsum : (∑' m, D.localizer m q.1) = 0 := by simp only [hn, tsum_zero]
    have hosum := (hpart.2.2.2.2.1 q.1 hq.1).2
    linarith only [hzsum, hosum]
  obtain ⟨m, hm⟩ := hex
  have hcell : q.1 ∈ D.cells m := hpart.2.2.1 m hm
  let w : ℝ := 1 + pairGrading (stateGrading S) realGrading (s + loss)
    (z - (C.referenceState, 0))
  have hw : 1 ≤ w := le_add_of_nonneg_right (apply_nonneg _ _)
  have hw0 : 0 ≤ w := zero_le_one.trans hw
  have hd : |coefficientFamily D S C i a b q z| ≤ (B * K) * w := by
    calc
      _ ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B * w :=
        hdifference m i a b q hab hcell z hz
      _ = (B * (T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)) * w := by ring
      _ ≤ (B * K) * w := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (habsorb m) hB.le) hw0
  have href := hreference i a b hab q ⟨hq.1.1.le, hq.1.2.le⟩
  have hcur := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hsector i
  have hzero := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN
    (reference_mem_stateNeighborhood S C base hN.2.1) hN.2.2.1.stateSector i
  have he : coefficientFamily D S C i a b q z =
      mixedDerivative a b (canonicalCoefficientComponent i (originalCoefficients D S C z)) q -
        mixedDerivative a b (canonicalCoefficientComponent i
          (originalCoefficients D S C (C.referenceState, 0))) q := by
    simpa only [coefficientFamily, canonicalCoefficientComponent] using
      mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ) hcur hzero a b hq
  rw [he] at hd
  have href' : |mixedDerivative a b (canonicalCoefficientComponent i
      (originalCoefficients D S C (C.referenceState, 0))) q| ≤ M * w :=
    href.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw hM)
  calc
    _ ≤ |mixedDerivative a b (canonicalCoefficientComponent i
        (originalCoefficients D S C z)) q - mixedDerivative a b
          (canonicalCoefficientComponent i
            (originalCoefficients D S C (C.referenceState, 0))) q| +
        |mixedDerivative a b (canonicalCoefficientComponent i
          (originalCoefficients D S C (C.referenceState, 0))) q| := by
      simpa only [sub_add_cancel] using abs_add_le
        (mixedDerivative a b (canonicalCoefficientComponent i (originalCoefficients D S C z)) q -
          mixedDerivative a b (canonicalCoefficientComponent i
            (originalCoefficients D S C (C.referenceState, 0))) q)
        (mixedDerivative a b (canonicalCoefficientComponent i
          (originalCoefficients D S C (C.referenceState, 0))) q)
    _ ≤ (B * K) * w + M * w := add_le_add hd href'
    _ = (B * K + M) * w := by ring

end ContinuousFlexibility.Analysis
