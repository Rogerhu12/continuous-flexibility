import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData
import ContinuousFlexibility.Analysis.N04NegativeGeometryDataCollector
import ContinuousFlexibility.Analysis.N04SourceColumnsPrefix
import ContinuousFlexibility.Analysis.N04SourceColumnsScalarComposition

/-!
# Scalar composition on one fixed compact range

The parameter base is chosen from the full input tower before its order.
Every positive derivative of the scalar composite retains the sampled
height factor.  The first derivative then controls the reference
difference, on one smaller convex sector neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {S : PhysicalSpacesData} {T : MaterialData} {D : ReferenceData}
  {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Restrict the actual mixed towers without choosing new derivatives. -/
def MixedJetRegularity.height_restrict
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U U' : Set X} {Ω : Set PolarPoint} {F : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U Ω F) (hU' : IsOpen U') (hsub : U' ⊆ U) :
    MixedJetRegularity U' Ω F where
  spatial x hx := R.spatial x (hsub hx)
  parameter a b q hq := (R.parameter a b q hq).restrict hU' hsub

/-- The two defining sector bounds control the sum parameter grading. -/
theorem n04NegativeHeight_parameterGrading_le_one
    {b : ℕ} {e : ℝ} (he : e ≤ 1 / 2) {z : Parameter S}
    (hz : z ∈ sectorNeighborhood S b e e) : parameterGrading S b z ≤ 1 := by
  change sectorGrading S b z.1 + ‖z.2‖ ≤ 1
  rw [Real.norm_eq_abs]
  linarith [hz.1, hz.2]

/-- Smooth scalar kernels on a fixed compact range preserve the actual
current-data estimate, including the positive parameter height factor. -/
theorem CurrentJetDataOn.height_scalarComp
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : N04HeightReferenceDataOn T cell P f₀)
    (hzero : ∀ m, P m → ∀ q ∈ unitStrip, f 0 m q = f₀ m q)
    {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} (hK : IsCompact K) (hKV : K ⊆ V)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g V)
    (hrange : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ∀ q ∈ unitStrip, f z m q ∈ K) :
    ∃ b' : ℕ, ∃ ε' : ℝ, base ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell P b' ε'
        (fun z m q => g (f z m q)) (fun m q => g (f₀ m q)) := by
  classical
  let U := sectorNeighborhood S base ε ε
  have hU : IsOpen U := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  let RF : ∀ m, P m → MixedJetRegularity U unitStrip (fun z => f z m) :=
    fun m hm => h.height_regularity h₀ m hm
  let RG : ∀ m, P m → MixedJetRegularity U unitStrip (fun z q => g (f z m q)) :=
    fun m hm => (RF m hm).scalarComp hU hΩ hV hg
      (fun z hz q hq => hKV (hrange z hz m hm q hq))
  have hz₀ : (0 : Parameter S) ∈ U := by
    exact ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  obtain ⟨RH, hRH, hheight⟩ := material_sample_height_coefficient_power_bounded hD hT cell 0
    (by norm_num : (0 : ℝ) < 3 / 4)
  have hHR (m : ℕ) : T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ RH := by
    simpa only [Real.rpow_zero, mul_one] using hheight m
  have ht := h.height_fullTower hD hT h₀ hE
  let L : ℕ → ℕ := fun k => (ht k).choose
  have hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t : {m // P m}, ∀ q (hq : q ∈ unitStrip) a b, a + b ≤ s →
      ∀ z ∈ U, ∀ v : Fin k → Parameter S,
        |((RF t.val t.property).parameter a b q hq).D k z v| ≤
          B * T.E0 (T.sample (cell t.val)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell t.val)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    intro k s
    exact ⟨((ht k).choose_spec s).choose, ((ht k).choose_spec s).choose_spec.1,
      fun t q hq a b hab z hz v =>
        ((ht k).choose_spec s).choose_spec.2 t.val t.property q hq a b hab
          ((RF t.val t.property).parameter a b q hq) z hz v⟩
  obtain ⟨b', hb', hprefix⟩ := n04SourceColumns_prefix_power
    (parameterGrading S) hp hI base L
    (fun t : {m // P m} => T.E0 (T.sample (cell t.val)))
    (fun k t => parameterHeightWeight (T.H (T.sample (cell t.val)) ^ (3 / 4 : ℝ)) k)
    (fun t => hE t.val)
    (fun k t => parameterHeightWeight_nonneg (Real.rpow_nonneg (hH t.val) _) k)
    (fun t z => f z t.val) (fun t => RF t.val t.property) hbound
  let ε' : ℝ := min ε (1 / 2)
  let U' := sectorNeighborhood S b' ε' ε'
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hεε : ε' ≤ ε := min_le_left _ _
  have hU' : IsOpen U' := isOpen_sectorNeighborhood S b' ε' ε'
  have hsub : U' ⊆ U := sectorNeighborhood_mono S hb' hεε hεε
  let R' : ∀ m, P m → MixedJetRegularity U' unitStrip (fun z q => g (f z m q)) :=
    fun m hm => (RG m hm).height_restrict hU' hsub
  have hlow : ∀ z ∈ U', parameterGrading S b' z ≤ 1 :=
    fun z hz => n04NegativeHeight_parameterGrading_le_one (min_le_right ε (1 / 2)) hz
  refine ⟨b', ε', hb', hε', hεε, CurrentJetDataOn.of_positive_towers hε' hE hH R'
    (fun z hz m hm q hq => congrArg g ((h.1 z (hsub hz) m hm).2 q hq))
    (fun m hm => ?_) (fun m hm q hq => congrArg g (hzero m hm q hq)) hlow ?_⟩
  · exact hg.comp (h₀.1 m hm).1 (fun q hq => by
      rw [← hzero m hm q hq]
      exact hKV (hrange 0 hz₀ m hm q hq))
  · intro k hk
    obtain ⟨shift, hshift⟩ := hprefix k
    refine ⟨b' + shift * k + 1, fun s => ?_⟩
    obtain ⟨A, hA, hraw⟩ := hshift s
    obtain ⟨C, hC, houter⟩ := compact_iteratedFDeriv_bound hK
      (fun t ht => (hg t (hKV ht)).contDiffAt (hV.mem_nhds (hKV ht))) (k + s)
    obtain ⟨B, hB, hcomp⟩ := n04SourceColumns_scalarComposition_positive_oneHigh
      (X := Parameter S) k s shift RH
    let M : ℝ := 1 + max 0 C + A
    have hM : 1 ≤ M := by dsimp only [M]; linarith [le_max_left (0 : ℝ) C]
    have hAM : A ≤ M := by dsimp only [M]; linarith [le_max_left (0 : ℝ) C]
    have hCM : C ≤ M := by dsimp only [M]; linarith [le_max_right (0 : ℝ) C]
    obtain ⟨Q, hQ, hpack⟩ := coefficientEnvelope_pack
      (B * M ^ (k + s + 1)) (M * ((k + s + 1 : ℕ) : ℝ))
    refine ⟨Q, hQ, ?_⟩
    intro m hm q hq a b hab z hz v
    let E : ℝ := T.E0 (T.sample (cell m))
    have hE0 : 1 ≤ E := hE m
    have hME : 1 ≤ M * E ^ M := one_le_mul_of_one_le_of_one_le hM
      (Real.one_le_rpow hE0 (zero_le_one.trans hM))
    have hMM : M ≤ M * E ^ M := le_mul_of_one_le_right (zero_le_one.trans hM)
      (Real.one_le_rpow hE0 (zero_le_one.trans hM))
    have hAE : A * E ^ A ≤ M * E ^ M := mul_le_mul hAM
      (Real.rpow_le_rpow_of_exponent_le hE0 hAM)
      (Real.rpow_nonneg (zero_le_one.trans hE0) _) (zero_le_one.trans hM)
    have houter' (u : ℕ) (hu : u ≤ s) (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j (iteratedDeriv u g) (f z m q)‖ ≤ M * E ^ M := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        n04SourceColumns_iteratedDeriv_add]
      have ho := houter (j + u) (by omega) (f z m q) (hrange z (hsub hz) m hm q hq)
      have ho' : ‖iteratedDeriv (j + u) g (f z m q)‖ ≤ C := by
        simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using ho
      exact ho'.trans (hCM.trans hMM)
    have hraw' (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ s)
        (d : Fin j → Parameter S) (hd : ∀ i, parameterGrading S b' (d i) ≤ 1)
        (R : ℝ) (hR : 1 ≤ R)
        (hzR : parameterGrading S (s + (b' + shift * k + 1)) (z - 0) ≤ R)
        (hdR : ∀ i, parameterGrading S (s + (b' + shift * k + 1)) (d i) ≤ R) :
        ‖((RF m hm).parameter u w q hq).D j z d‖ ≤ M * E ^ M *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) j *
            R ^ (((u + w + shift * j : ℕ) : ℝ) /
              (((s + shift * k : ℕ) : ℝ) + 1)) := by
      have hr := hraw j hj ⟨m, hm⟩ q hq u w huw z (hsub hz) (hlow z hz) d hd R hR
        (by simpa only [sub_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hzR)
        (fun i => by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdR i)
      rw [Real.norm_eq_abs]
      exact hr.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAE
          (parameterHeightWeight_nonneg (Real.rpow_nonneg (hH m) _) j))
        (Real.rpow_nonneg (zero_le_one.trans hR) _))
    have hresult := hcomp (parameterGrading S) 0 b' (s + (b' + shift * k + 1))
      U hU unitStrip hΩ V hV (fun z => f z m) g (RF m hm) hg
      (fun z hz q hq => hKV (hrange z hz m hm q hq)) q hq
      (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) (M * E ^ M)
      (Real.rpow_nonneg (hH m) _) (hHR m) hME z (hsub hz)
      (by simpa only [sub_zero] using hlow z hz) houter' hraw'
      k le_rfl hk a b hab ((RG m hm).parameter a b q hq) v
    have hcost := mul_le_mul_of_nonneg_right (hpack E hE0)
      (mul_nonneg (Real.rpow_nonneg (hH m) _)
        (oneHighVariationWeight_nonneg (parameterGrading S) b'
          (s + (b' + shift * k + 1)) z v))
    have hpow : B * (M * E ^ M) ^ (k + s + 1) =
        (B * M ^ (k + s + 1)) * E ^ (M * ((k + s + 1 : ℕ) : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE0)]
      ring
    simpa only [R', MixedJetRegularity.height_restrict, SmoothDirections.restrict,
      Real.norm_eq_abs, sub_zero, hpow, mul_assoc] using hresult.trans
        (by simpa only [sub_zero, hpow, mul_assoc] using hcost)

end ContinuousFlexibility.Analysis
