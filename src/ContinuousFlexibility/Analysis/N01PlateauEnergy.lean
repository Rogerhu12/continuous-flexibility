import ContinuousFlexibility.Analysis.N01ControlPlateauOverlap
import ContinuousFlexibility.Analysis.MaterialPlateauLocalization
import ContinuousFlexibility.Analysis.MaterialCutoffJetEnergy

/-!
# Summing actual N01 plateau-localized height energies

Both the cutoff derivatives and the support overlap are controlled at
the actual material point. Their costs are two additional material
orders, independent of the derivative order and of the height field.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def controlPlateauMaterialStrip (D : ReferenceData) (T : MaterialData)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (m : ℕ) : Set PolarPoint :=
  {p | T.radius p.1 ∈ Icc
    (C.left m - endpointPlateauWidth D (C.left m) (C.right m))
    (C.right m + endpointPlateauWidth D (C.left m) (C.right m))}

theorem controlPlateauMaterialStrip_measurable {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hT : IsMaterialData D T)
    (C : NonlinearGeometryData S) (m : ℕ) :
    MeasurableSet (controlPlateauMaterialStrip D T C m) :=
  (isClosed_Icc.preimage (hT.2.2.2.2.2.2.1.continuous.comp continuous_fst)).measurableSet

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.controlPlateau_material_overlap_bound
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : PolarPoint,
      {m : ℕ | p ∈ controlPlateauMaterialStrip D T C m}.Finite ∧
      ({m : ℕ | p ∈ controlPlateauMaterialStrip D T C m}.ncard : ℝ) ≤
        K * T.M (T.radius p.1) ^ 2 := by
  obtain ⟨K₀, A, hK₀, _, hover⟩ := hN.controlPlateau_overlap_bound hT
  have hmaterial := hT
  obtain ⟨_, _, _, _, _, _, _, hinside, _, _, _, henv, _⟩ := hmaterial
  obtain ⟨Ke, hKe, hE⟩ := henv A
  refine ⟨K₀ * Ke, mul_pos hK₀ hKe, fun p => ?_⟩
  have hp := (hinside p.1).1
  obtain ⟨hfinite, hcount⟩ := hover (T.radius p.1) hp
  refine ⟨hfinite, ?_⟩
  have hM : 1 ≤ T.M (T.radius p.1) := (hT.2.1 _ hp).2.2.2
  have hMM : T.M (T.radius p.1) ≤ T.M (T.radius p.1) ^ 2 := by nlinarith only [hM]
  calc
    _ ≤ K₀ * T.E0 (T.radius p.1) ^ A := hcount
    _ ≤ K₀ * (Ke * T.M (T.radius p.1)) := mul_le_mul_of_nonneg_left (hE _ hp) hK₀.le
    _ ≤ K₀ * (Ke * T.M (T.radius p.1) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMM hKe.le) hK₀.le
    _ = _ := by ring

theorem N01Properties.controlPlateau_cutoff_coeff_bound
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i : Fin (a + 1), ∀ x : ℝ,
      |(a.choose i.val : ℝ) * iteratedDeriv i.val
        (materialPlateauCutoff T (C.left m) (C.right m)
          (endpointPlateauWidth D (C.left m) (C.right m))) x| ≤ K * T.M (T.radius x) := by
  classical
  have hi (i : Fin (a + 1)) := materialPlateauCutoff_iteratedDeriv_bound_by_M hN.1.1 hT i.val
  choose Ki hKi hjet using hi
  let K : ℝ := ∑ i : Fin (a + 1), (a.choose i.val : ℝ) * Ki i
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hKi i).le)
  obtain ⟨_, _, hcells⟩ := hN.actualCell_travel_lower_bound
  have hc : controlGeometryConditions D S C := hN.2.2.2.1
  refine ⟨K, hK, fun m i x => ?_⟩
  obtain ⟨_, j, hj, _⟩ := hcells m
  have hm := hjet i j (C.left m) (C.right m)
    (hc.1 m).1 (hc.1 m).2.1 (hc.1 m).2.2 hj x
  have hM : 0 ≤ T.M (T.radius x) :=
    zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.2.2
  have hKiK : (a.choose i.val : ℝ) * Ki i ≤ K :=
    Finset.single_le_sum (f := fun k : Fin (a + 1) => (a.choose k.val : ℝ) * Ki k)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hKi k).le)
      (Finset.mem_univ i)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (a.choose i.val : ℝ) * (Ki i * T.M (T.radius x)) :=
      mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
    _ ≤ K * T.M (T.radius x) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKiK hM

/-- The bound is uniform over the height field and over the remaining
jet indices. The input gains exactly two material orders. -/
theorem N01Properties.controlPlateau_cutoff_jet_energy_tsum_le
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : ℝ) (f : PolarPoint → ℝ), HeightMember D T γ f →
      ∀ b c : ℕ,
      (∑' m : ℕ, eLpNorm (weightedPhysicalJet T γ a b c
        (radialPlateauLocalization D T (C.left m) (C.right m) f))
          2 materialCylinderMeasure ^ 2) ≤
        ENNReal.ofReal K * ∑ i : Fin (a + 1),
          eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 2) f)
            2 materialCylinderMeasure ^ 2 := by
  classical
  obtain ⟨Kc, hKc, hcoeff⟩ := hN.controlPlateau_cutoff_coeff_bound hT a
  obtain ⟨Ko, hKo, hover⟩ := hN.controlPlateau_material_overlap_bound hT
  let P : ℝ := ((a + 1 : ℕ) : ℝ) * Kc ^ 2
  have hP : 0 ≤ P := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine ⟨P * Ko, mul_nonneg hP hKo.le, fun γ f hf b c => ?_⟩
  let A : ℕ → Set PolarPoint := controlPlateauMaterialStrip D T C
  let g (m : ℕ) (i : Fin (a + 1)) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 1) f)
      2 (materialCylinderMeasure.restrict (A m)) ^ 2
  have hA (m : ℕ) : MeasurableSet (A m) := controlPlateauMaterialStrip_measurable hT C m
  have hc : controlGeometryConditions D S C := hN.2.2.2.1
  have hm (m : ℕ) :
      eLpNorm (weightedPhysicalJet T γ a b c
        (radialPlateauLocalization D T (C.left m) (C.right m) f))
          2 materialCylinderMeasure ^ 2 ≤ ENNReal.ofReal P * ∑ i : Fin (a + 1), g m i := by
    have hχ := materialPlateauCutoff_contDiff hT (C.left m) (C.right m)
      (endpointPlateauWidth D (C.left m) (C.right m))
    have hcut := radialPlateauLocalization_member hT hf (hc.1 m).1 (hc.1 m).2.2
    apply weightedPhysicalJet_cutoff_energy_le hT hχ hf hcut hKc (hA m)
      a b c (fun p i => hcoeff m i p.1)
    intro p hp i hi
    exact materialPlateauCutoff_iteratedDeriv_zero_off_support hT
      (endpointPlateauWidth_pos (hc.1 m).1 (hc.1 m).2.2) hp i
  have hi (i : Fin (a + 1)) :
      (∑' m : ℕ, g m i) ≤ ENNReal.ofReal Ko *
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 2) f)
          2 materialCylinderMeasure ^ 2 := by
    simpa only [g, Nat.add_assoc, Nat.reduceAdd] using
      weightedPhysicalJet_restricted_energy_tsum_le hT hf hKo.le hA
        (fun p => (hover p).1) (fun p => (hover p).2) (a - i.val) b (c + 1)
  have hcomm : (∑' m : ℕ, ∑ i : Fin (a + 1), g m i) =
      ∑ i : Fin (a + 1), ∑' m : ℕ, g m i := by
    simpa only [tsum_fintype] using ENNReal.tsum_comm (f := g)
  calc
    _ ≤ ∑' m : ℕ, ENNReal.ofReal P * ∑ i : Fin (a + 1), g m i :=
      ENNReal.tsum_le_tsum hm
    _ = ENNReal.ofReal P * ∑ i : Fin (a + 1), ∑' m : ℕ, g m i := by
      rw [ENNReal.tsum_mul_left, hcomm]
    _ ≤ ENNReal.ofReal P * ∑ i : Fin (a + 1), ENNReal.ofReal Ko *
        eLpNorm (weightedPhysicalJet T γ (a - i.val) b (c + 2) f)
          2 materialCylinderMeasure ^ 2 :=
      mul_le_mul_right (Finset.sum_le_sum (fun i _ => hi i)) _
    _ = _ := by rw [← Finset.mul_sum, ENNReal.ofReal_mul hP, mul_assoc]

theorem N01Properties.controlPlateau_cutoff_jet_energy_tsum_lt_top
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (a b c : ℕ) :
    (∑' m : ℕ, eLpNorm (weightedPhysicalJet T γ a b c
      (radialPlateauLocalization D T (C.left m) (C.right m) f))
        2 materialCylinderMeasure ^ 2) < ⊤ := by
  obtain ⟨K, _, hb⟩ := hN.controlPlateau_cutoff_jet_energy_tsum_le hT a
  apply (hb γ f hf b c).trans_lt
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  rw [pow_two]
  exact ENNReal.mul_lt_top (hf.2.2.2.2 _ _ _) (hf.2.2.2.2 _ _ _)

end ContinuousFlexibility.Statements
