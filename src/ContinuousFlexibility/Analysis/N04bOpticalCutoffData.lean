import ContinuousFlexibility.Analysis.ReturnCorrectionBufferedCollars
import ContinuousFlexibility.Analysis.N01FlowInverseJetBounds

/-!
# One actual optical cutoff with its retained geometric and quantitative data

The cutoff and its strictly wider positive collar come from the proved
buffered optical construction. A further shrinking supplies the old-flow angular bounds.
The strict corrected characteristic gap is retained through that shrinking,
so the same cutoff can be used for the source and the raw physical field.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

structure N04bOpticalCutoffData (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) where
  cutoff : ℕ → ℝ → ℝ
  cell : ℕ → ℕ
  center : ℕ → ℝ
  width : ℕ → ℝ
  widthConstant : ℝ
  widthPower : ℝ
  opticalPower : ℝ
  discScale : ℝ
  discPower : ℝ
  widthConstant_pos : 0 < widthConstant
  widthPower_pos : 0 < widthPower
  opticalPower_pos : 0 < opticalPower
  discScale_pos : 0 < discScale
  discPower_pos : 0 < discPower
  component_cell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (cell m)
  width_pos : ∀ m, 0 < width m
  left_lt : ∀ m, C.left m < center m - width m
  lt_right : ∀ m, center m + width m < C.right m
  inverse_width_bound : ∀ m,
    (width m)⁻¹ ≤ widthConstant * radialE (D.cellIndex (cell m)) ^ widthPower
  optical_lower : ∀ m r, r ∈ Icc (center m - width m) (center m + width m) →
    radialE (D.cellIndex (cell m)) ^ (-opticalPower) / (2 * (D.b - D.a)) ≤
      opticalSpeed D.w r
  cutoff_eq : ∀ m, cutoff m = returnOpticalCutoff (center m) (width m)
  cutoff_smooth : ∀ m, ContDiff ℝ ∞ (cutoff m)
  cutoff_range : ∀ m r, cutoff m r ∈ Icc (0 : ℝ) 1
  cutoff_left : ∀ m, cutoff m =ᶠ[𝓝 (C.left m)] (fun _ => 0)
  cutoff_right : ∀ m, cutoff m =ᶠ[𝓝 (C.right m)] (fun _ => 1)
  cutoff_support : ∀ m,
    tsupport (deriv (cutoff m)) ⊆ Icc (center m - width m) (center m + width m)
  cutoff_jets : ∀ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ m r,
    |iteratedDeriv n (cutoff m) r| ≤
      K * radialE (D.cellIndex (cell m)) ^ (widthPower * n)
  collar_positive : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
    p.1 ∈ Icc (center m - width m) (center m + width m) →
    let d := discScale * radialE (D.cellIndex (cell m)) ^ (-discPower) / 2
    0 < d ∧
    d ≤ (originalCoefficients D S C z).a p ∧
    d ≤ -(originalCoefficients D S C z).c p ∧
    d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ∧
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p
  buffer_left : ∀ m, C.left m < center m - 2 * width m
  buffer_right : ∀ m, center m + 2 * width m < C.right m
  buffer_positive : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
    p.1 ∈ Icc (center m - 2 * width m) (center m + 2 * width m) →
    let d := discScale * radialE (D.cellIndex (cell m)) ^ (-discPower) / 2
    d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p
  corrected_speeds : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ,
      (deriv (cutoff m) r ≠ 0 →
        0 < (-returnCorrectedMinusSpeed D S C cutoff z m (r, -θ) -
          returnCorrectedMinusSpeed D S C cutoff z m (r, θ)) / 2) ∧
      returnCorrectedMinusSpeed D S C cutoff z m (r, θ) ≤
        -returnCorrectedMinusSpeed D S C cutoff z m (r, -θ)
  flow_slope : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧
        deriv (C.minusFlow z m r) θ ≤ 3 / 2

theorem N01Properties.exists_n04b_opticalCutoffData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01Properties D T S C base' loss ε' ∧
      Nonempty (N04bOpticalCutoffData D S C base' ε') := by
  let data := hN.exists_positive_opticalCorrectionCollars_buffered hT
  let b₀ : ℕ := data.choose
  let dataε := data.choose_spec
  let ε₀ : ℝ := dataε.choose
  let dataχ := dataε.choose_spec
  let χ : ℕ → ℝ → ℝ := dataχ.choose
  let dataj := dataχ.choose_spec
  let j : ℕ → ℕ := dataj.choose
  let datax := dataj.choose_spec
  let x : ℕ → ℝ := datax.choose
  let dataδ := datax.choose_spec
  let δ : ℕ → ℝ := dataδ.choose
  let dataK := dataδ.choose_spec
  let K : ℝ := dataK.choose
  let dataA := dataK.choose_spec
  let A : ℝ := dataA.choose
  let dataB := dataA.choose_spec
  let B : ℝ := dataB.choose
  let datalam := dataB.choose_spec
  let lam : ℝ := datalam.choose
  let dataP := datalam.choose_spec
  let P : ℝ := dataP.choose
  have hchosen := dataP.choose_spec
  have hb₀ : base ≤ b₀ := hchosen.1
  have hε₀ : 0 < ε₀ := hchosen.2.1
  have hε₀ε : ε₀ ≤ ε := hchosen.2.2.1
  have hK : 0 < K := hchosen.2.2.2.1
  have hA : 0 < A := hchosen.2.2.2.2.1
  have hB : 0 < B := hchosen.2.2.2.2.2.1
  have hlam : 0 < lam := hchosen.2.2.2.2.2.2.1
  have hP : 0 < P := hchosen.2.2.2.2.2.2.2.1
  have hN₀ : N01Properties D T S C b₀ loss ε₀ :=
    hchosen.2.2.2.2.2.2.2.2.1
  have hdata := hchosen.2.2.2.2.2.2.2.2.2.1
  have hχeq := hchosen.2.2.2.2.2.2.2.2.2.2.1
  have hχ := hchosen.2.2.2.2.2.2.2.2.2.2.2.1
  have hend := hchosen.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbuffer := hchosen.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hjets := hchosen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpositive := hchosen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcell (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ D.cells (j m) :=
    (hdata m).1
  obtain ⟨J, hJ, hjet⟩ := hjets 1
  have hcutoff (m : ℕ) (r : ℝ) :
      |deriv (χ m) r| ≤ J * radialE (D.cellIndex (j m)) ^ A := by
    simpa only [iteratedDeriv_one, Nat.cast_one, mul_one] using hjet m r
  have hpositiveSupport (z : AnnularState S × ℝ)
      (hz : z ∈ stateNeighborhood S C b₀ ε₀) (m : ℕ) (p : PolarPoint)
      (hp : p.1 ∈ tsupport (deriv (χ m))) :=
    hpositive z hz m p ⟨(hbuffer m hp).1.le, (hbuffer m hp).2.le⟩
  obtain ⟨b₁, ε₁, hb₁, hε₁, hε₁₀, hN₁, hgap⟩ :=
    exists_gap_neighborhood_for_positive_cutoff hN₀ hS hT hε₀ χ j
      hJ hA.le hlam hP.le hcell hcutoff hpositiveSupport
  obtain ⟨b₂, ε₂, hb₂, hε₂, hε₂₁, hN₂, hangular⟩ :=
    hN₁.exists_uniform_inverse_angular_jets hS hT
  have hsub : stateNeighborhood S C b₂ ε₂ ⊆ stateNeighborhood S C b₀ ε₀ :=
    stateNeighborhood_mono S C (hb₁.trans hb₂) (hε₂₁.trans hε₁₀)
  have hδ (m : ℕ) : 0 < δ m := (hdata m).2.1
  have htwice (m : ℕ) : 2 * (δ m / 2) = δ m := by ring
  have hwidth (m : ℕ) :
      (δ m / 2)⁻¹ ≤ (2 * K) * radialE (D.cellIndex (j m)) ^ A := by
    have heq : (δ m / 2)⁻¹ = 2 * (δ m)⁻¹ := by
      field_simp [(hδ m).ne']
      <;> ring
    have hb := mul_le_mul_of_nonneg_left (hdata m).2.2.2.2.1
      (by norm_num : (0 : ℝ) ≤ 2)
    exact heq.trans_le (hb.trans_eq (mul_assoc _ _ _).symm)
  have hinner (m : ℕ) :
      Icc (x m - δ m / 2) (x m + δ m / 2) ⊆ Icc (x m - δ m) (x m + δ m) := by
    intro r hr
    constructor <;> linarith only [hr.1, hr.2, hδ m]
  refine ⟨b₂, ε₂, hb₀.trans (hb₁.trans hb₂), hε₂,
    (hε₂₁.trans hε₁₀).trans hε₀ε, hN₂, ⟨?_⟩⟩
  exact
    { cutoff := χ
      cell := j
      center := x
      width := fun m => δ m / 2
      widthConstant := 2 * K
      widthPower := A
      opticalPower := B
      discScale := lam
      discPower := P
      widthConstant_pos := mul_pos (by norm_num) hK
      widthPower_pos := hA
      opticalPower_pos := hB
      discScale_pos := hlam
      discPower_pos := hP
      component_cell := hcell
      width_pos := fun m => half_pos (hδ m)
      left_lt := fun m => by linarith only [(hdata m).2.2.1, hδ m]
      lt_right := fun m => by linarith only [(hdata m).2.2.2.1, hδ m]
      inverse_width_bound := hwidth
      optical_lower := fun m r hr => (hdata m).2.2.2.2.2 r (hinner m hr)
      cutoff_eq := hχeq
      cutoff_smooth := fun m => (hχ m).1
      cutoff_range := fun m => (hχ m).2
      cutoff_left := fun m => (hend m).1
      cutoff_right := fun m => (hend m).2.1
      cutoff_support := fun m => (hend m).2.2
      cutoff_jets := hjets
      collar_positive := fun z hz m p hp => hpositive z (hsub hz) m p (hinner m hp)
      buffer_left := fun m => by simpa only [htwice] using (hdata m).2.2.1
      buffer_right := fun m => by simpa only [htwice] using (hdata m).2.2.2.1
      buffer_positive := fun z hz m p hp => by
        have hpos := hpositive z (hsub hz) m p (by simpa only [htwice] using hp)
        exact ⟨hpos.2.1, hpos.2.2.2.1⟩
      corrected_speeds := fun z hz hs m r hr θ =>
        hgap z (stateNeighborhood_mono S C hb₂ hε₂₁ hz) hs m r hr θ
      flow_slope := fun z hz hs => (hangular z hz hs).1 }

end ContinuousFlexibility.Statements
