import ContinuousFlexibility.Analysis.StateKappaBounds

/-!
# Material weights for the canonical volume scale

These estimates use the actual `IsMaterialData` envelopes.  They apply at
any cell sample, without assuming a relation between a canonical piece and
its chosen cell label.  A positive endpoint exponent bounds the forget
weight into an unweighted sequence space.  A strict endpoint margin absorbs
any fixed change of material order, and a coefficient power costs one
material order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem n05_materialWeight_pos {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {r : ℝ} (hr : r ∈ Ioo D.a D.b)
    (γ t : ℝ) :
    0 < T.M r ^ (-t) * T.H r ^ γ := by
  have hH : 0 < T.H r := (hT.2.1 r hr).2.1
  have hM : 0 < T.M r := zero_lt_one.trans_le (hT.2.1 r hr).2.2.2
  exact mul_pos (Real.rpow_pos_of_pos hM _) (Real.rpow_pos_of_pos hH _)

/-- Every positive endpoint exponent controls the canonical forget weight,
uniformly over the physical annulus. -/
theorem n05_materialWeight_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Ioo D.a D.b,
      T.M r ^ (-t) * T.H r ^ γ ≤ B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hT
  obtain ⟨B, hB, hb, _, _⟩ := henv (-t) γ hγ
  exact ⟨B, hB, fun r hr => by simpa only [mul_comm] using hb r hr⟩

/-- An endpoint-exponent margin absorbs an arbitrary material-order change. -/
theorem n05_materialWeight_compare {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γlo γhi : ℝ} (hγ : γlo < γhi)
    (tlo thi : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Ioo D.a D.b,
      T.M r ^ (-thi) * T.H r ^ γhi ≤
        B * (T.M r ^ (-tlo) * T.H r ^ γlo) := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨B, hB, hb, _, _⟩ := henv (tlo - thi) (γhi - γlo) (sub_pos.mpr hγ)
  refine ⟨B, hB, ?_⟩
  intro r hr
  have hH : 0 < T.H r := (hT.2.1 r hr).2.1
  have hM : 0 < T.M r := zero_lt_one.trans_le (hT.2.1 r hr).2.2.2
  have hm : T.M r ^ (tlo - thi) * T.M r ^ (-tlo) = T.M r ^ (-thi) := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  have hh : T.H r ^ (γhi - γlo) * T.H r ^ γlo = T.H r ^ γhi := by
    rw [← Real.rpow_add hH]
    congr 1
    ring
  calc
    T.M r ^ (-thi) * T.H r ^ γhi =
        (T.M r ^ (tlo - thi) * T.M r ^ (-tlo)) *
          (T.H r ^ (γhi - γlo) * T.H r ^ γlo) := by rw [hm, hh]
    _ = (T.H r ^ (γhi - γlo) * T.M r ^ (tlo - thi)) *
        (T.M r ^ (-tlo) * T.H r ^ γlo) := by ring
    _ ≤ B * (T.M r ^ (-tlo) * T.H r ^ γlo) :=
      mul_le_mul_of_nonneg_right (hb r hr) (n05_materialWeight_pos hT hr γlo tlo).le

/-- The coefficient envelope costs one material weight order, independently
of the endpoint exponent and of the incoming material order. -/
theorem n05_materialCoefficient_weight_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (A : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ γ t : ℝ, ∀ r ∈ Ioo D.a D.b,
      T.E0 r ^ A * (T.M r ^ (-t) * T.H r ^ γ) ≤
        B * (T.M r ^ (-(t - 1)) * T.H r ^ γ) := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨B, hB, hb⟩ := henv A
  refine ⟨B, hB, ?_⟩
  intro γ t r hr
  have hM : 0 < T.M r := zero_lt_one.trans_le (hT.2.1 r hr).2.2.2
  have hm : T.M r * T.M r ^ (-t) = T.M r ^ (-(t - 1)) := by
    calc
      T.M r * T.M r ^ (-t) = T.M r ^ (1 : ℝ) * T.M r ^ (-t) := by
        rw [Real.rpow_one]
      _ = T.M r ^ (1 + -t) := (Real.rpow_add hM _ _).symm
      _ = T.M r ^ (-(t - 1)) := by congr 1; ring
  calc
    T.E0 r ^ A * (T.M r ^ (-t) * T.H r ^ γ) ≤
        (B * T.M r) * (T.M r ^ (-t) * T.H r ^ γ) :=
      mul_le_mul_of_nonneg_right (hb r hr) (n05_materialWeight_pos hT hr γ t).le
    _ = B * (T.M r ^ (-(t - 1)) * T.H r ^ γ) := by rw [← hm]; ring

theorem n05_materialSampleWeight_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D)
    {γ : ℝ} (hγ : 0 < γ) (t : ℝ) (cell : ℕ → ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ,
      T.M (T.sample (cell m)) ^ (-t) * T.H (T.sample (cell m)) ^ γ ≤ B := by
  obtain ⟨B, hB, hb⟩ := n05_materialWeight_bound hT hγ t
  exact ⟨B, hB, fun m => hb _ (materialSample_mem_radialCore hT hPart (cell m))⟩

theorem n05_materialSampleWeight_compare {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D)
    {γlo γhi : ℝ} (hγ : γlo < γhi) (tlo thi : ℝ) (cell : ℕ → ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ,
      T.M (T.sample (cell m)) ^ (-thi) * T.H (T.sample (cell m)) ^ γhi ≤
        B * (T.M (T.sample (cell m)) ^ (-tlo) *
          T.H (T.sample (cell m)) ^ γlo) := by
  obtain ⟨B, hB, hb⟩ := n05_materialWeight_compare hT hγ tlo thi
  exact ⟨B, hB, fun m => hb _ (materialSample_mem_radialCore hT hPart (cell m))⟩

end ContinuousFlexibility.Statements
