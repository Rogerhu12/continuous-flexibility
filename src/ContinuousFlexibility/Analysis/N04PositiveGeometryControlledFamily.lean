import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledEndpoints
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledBuffer
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledTransport

/-!
# One actual controlled positive transport family

Every numerical choice precedes the state. The common neighborhood, the
sample input envelope, the normalization buffer, the polynomial inverse
envelope and the logarithmic height envelope remain attached to the same
displayed transport formulas. The strict coefficient margins are retained
for the actual radial inverse construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

structure N04PositiveGeometryControlData (W : N04RealizationStart)
    (X : N04RealizationChoice W) (n : ℕ) where
  buffer : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi)
  base : ℕ
  ε : ℝ
  M : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ
  Mσ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ
  δ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ
  Cinput : ℝ
  Cbuffer : ℝ
  Cσ : ℝ
  degree : ℕ
  Clog : ℝ

namespace N04PositiveGeometryControlData

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

def τ (G : N04PositiveGeometryControlData W X n) (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : PolarPoint → PolarPoint :=
  oneSidedWholeComponentTransport n
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).1)
    (n04PositiveLeft i) (n04PositiveRight i) (G.buffer.centerLeft i) (G.buffer.centerRight i)
    (G.M i)⁻¹ ((G.M i)⁻¹ / 2) (G.M i) (G.Mσ i)

def σ (G : N04PositiveGeometryControlData W X n) (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : PolarPoint → PolarPoint :=
  oneSidedWholeComponentTransportInverse n
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).1)
    (n04PositiveLeft i) (n04PositiveRight i) (G.buffer.centerLeft i) (G.buffer.centerRight i)
    (G.M i)⁻¹ ((G.M i)⁻¹ / 2) (G.M i) (G.Mσ i)

def Q (G : N04PositiveGeometryControlData W X n) (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : PolarPoint → ℝ :=
  positiveHeightTaylorInterpolation n (n04PositiveLeft i) (n04PositiveRight i) (G.δ i)
    (fun _ => 1) (fun side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)

def lower (G : N04PositiveGeometryControlData W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : ℝ :=
  endpointFiberLower n (n04PositiveLeft i) (n04PositiveRight i)
    (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2) (G.Mσ i) *
      ((G.M i)⁻¹ / 2)

def upper (G : N04PositiveGeometryControlData W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : ℝ :=
  Real.exp 2 * G.M i ^ 2

def coefficients (G : N04PositiveGeometryControlData W X n) (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : Bool → ℕ → ℝ → ℝ :=
  n04PositiveGeometry_oneSidedFiberData n
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).1)
    (n04PositiveLeft i) (n04PositiveRight i) (G.buffer.centerLeft i) (G.buffer.centerRight i)
    (G.M i)⁻¹ (G.M i)

end N04PositiveGeometryControlData

structure N04PositiveGeometryControlledFamily (W : N04RealizationStart)
    (X : N04RealizationChoice W) (n : ℕ) extends N04PositiveGeometryControlData W X n where
  base_le : W.base ≤ base
  radius_pos : 0 < ε
  radius_le : ε ≤ W.ε
  input_constant : 1 ≤ Cinput
  buffer_constant : 0 < Cbuffer
  inverse_constant : 1 ≤ Cσ
  log_constant : 0 < Clog
  input_one : ∀ i, 1 ≤ M i
  input_cost : ∀ i, M i ≤ Cinput * W.U.E0 (W.U.sample (X.cell i)) ^ Cinput
  buffer_cost : ∀ i,
    (buffer.centerLeft i - n04PositiveLeft i)⁻¹ ≤
      Cbuffer * W.U.E0 (W.U.sample (X.cell i)) ^ Cbuffer ∧
    (buffer.normalizationLeft i - buffer.centerLeft i)⁻¹ ≤
      Cbuffer * W.U.E0 (W.U.sample (X.cell i)) ^ Cbuffer ∧
    (buffer.normalizationRight i - buffer.normalizationLeft i)⁻¹ ≤
      Cbuffer * W.U.E0 (W.U.sample (X.cell i)) ^ Cbuffer ∧
    (buffer.centerRight i - buffer.normalizationRight i)⁻¹ ≤
      Cbuffer * W.U.E0 (W.U.sample (X.cell i)) ^ Cbuffer ∧
    (n04PositiveRight i - buffer.centerRight i)⁻¹ ≤
      Cbuffer * W.U.E0 (W.U.sample (X.cell i)) ^ Cbuffer
  endpoint_bounds : ∀ z ∈ stateNeighborhood W.S W.C base ε, stateSector W.S z.1 → ∀ i,
    WholePositiveEndpointJetBounds n
      (fun side => n04PositiveSourceMap (X.src i side) (W.A X.e₀) z)
      (fun side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)
      (n04PositiveLeft i) (n04PositiveRight i) (M i)⁻¹ (M i)⁻¹ (M i) (M i)
  inverse_one : ∀ i, 1 ≤ Mσ i
  inverse_cost : ∀ i, Mσ i ≤ Cσ * M i ^ degree
  coefficient_lower : ∀ z ∈ stateNeighborhood W.S W.C base ε, stateSector W.S z.1 →
    ∀ i side θ, (M i)⁻¹ ≤ toN04PositiveGeometryControlData.coefficients z i side 1 θ
  coefficient_bound : ∀ z ∈ stateNeighborhood W.S W.C base ε, stateSector W.S z.1 →
    ∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      |toN04PositiveGeometryControlData.coefficients z i side k θ| ≤ Mσ i / 2
  log_bound : ∀ z ∈ stateNeighborhood W.S W.C base ε, stateSector W.S z.1 →
    ∀ i side k, 0 < k → k ≤ n → ∀ θ,
      |positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i) (fun _ => 1)
        (fun side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z) side k θ| ≤
          Clog * M i ^ (2 * n + 1)
  width_pos : ∀ i, 0 < δ i
  width_core : ∀ i, δ i ≤ min ((n04PositiveRight i - n04PositiveLeft i) / 4)
    (min (buffer.centerLeft i - n04PositiveLeft i) (n04PositiveRight i - buffer.centerRight i))
  width_one : ∀ i, δ i ≤ 1
  width_inverse : ∀ i, (δ i)⁻¹ =
    (min ((n04PositiveRight i - n04PositiveLeft i) / 4)
      (min (buffer.centerLeft i - n04PositiveLeft i) (n04PositiveRight i - buffer.centerRight i)))⁻¹ +
      1 + ((n + 1 : ℕ) : ℝ) * (Clog * M i ^ (2 * n + 1) + 1)
  radial_lower_pos : ∀ i, 0 < endpointFiberLower n (n04PositiveLeft i) (n04PositiveRight i)
    (buffer.centerLeft i) (buffer.centerRight i) ((M i)⁻¹ / 2) (Mσ i)
  matching : ∀ z ∈ stateNeighborhood W.S W.C base ε, stateSector W.S z.1 → ∀ i,
    WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (X.src i side) (W.A X.e₀) z)
      (fun side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)
      (toN04PositiveGeometryControlData.τ z i) (toN04PositiveGeometryControlData.σ z i)
      (toN04PositiveGeometryControlData.Q z i) (n04PositiveLeft i) (n04PositiveRight i)
      (buffer.centerLeft i) (buffer.centerRight i)
      (toN04PositiveGeometryControlData.lower i) (toN04PositiveGeometryControlData.upper i)
  reference : ∀ i,
    toN04PositiveGeometryControlData.τ (W.C.referenceState, 0) i = id ∧
    toN04PositiveGeometryControlData.σ (W.C.referenceState, 0) i = id ∧
    toN04PositiveGeometryControlData.Q (W.C.referenceState, 0) i = (fun _ => (1 : ℝ))

/-- The controlled family is constructed from the retained start and its
optical choice. No numerical source estimate or transport is assumed. -/
theorem n04PositiveGeometry_controlledFamily_nonempty
    (W : N04RealizationStart) (X : N04RealizationChoice W) (n : ℕ) :
    Nonempty (N04PositiveGeometryControlledFamily W X n) := by
  classical
  have hbuffer := n04PositiveGeometry_exists_controlled_buffer W X
  let buffer := hbuffer.choose
  let Cbuffer := hbuffer.choose_spec.choose
  have hCbuffer := hbuffer.choose_spec.choose_spec.1
  have hbufferCost := hbuffer.choose_spec.choose_spec.2
  have hinput := n04PositiveGeometry_actual_positive_endpoint_material_bounds W X n
  let base := hinput.choose
  let ε := hinput.choose_spec.choose
  let Cinput := hinput.choose_spec.choose_spec.choose
  have hd := hinput.choose_spec.choose_spec.choose_spec
  have hb := hd.1
  have hε := hd.2.1
  have hεW := hd.2.2.1
  have hCinput := hd.2.2.2.1
  have hfinite := hd.2.2.2.2
  let M := fun i => Cinput * W.U.E0 (W.U.sample (X.cell i)) ^ Cinput
  have hM (i) : 1 ≤ M i := (hfinite i).1
  let Z := {z : AnnularState W.S × ℝ //
    z ∈ stateNeighborhood W.S W.C base ε ∧ stateSector W.S z.1}
  let z₀ : Z := ⟨(W.C.referenceState, 0),
    reference_mem_stateNeighborhood W.S W.C base hε, W.through03.1.1.2.2.1.stateSector⟩
  let F := fun i (z : Z) side => n04PositiveSourceMap (X.src i side) (W.A X.e₀) z.1
  let q := fun i (z : Z) side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z.1
  have hdata (i) (z : Z) (side : Bool) :
      OneSidedTransportEndpoint (F i z side) (q i z side)
        (n04PositiveSourceLeft (X.src i side)) (n04PositiveSourceRight (X.src i side))
        (if side then n04PositiveRight i else n04PositiveLeft i) :=
    n04Coordinates_actualAtlas_positiveEndpoint_of_source
      W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
      (stateNeighborhood_mono W.S W.C hb hεW z.2.1) z.2.2
  have hf (i) (z : Z) : WholePositiveEndpointJetBounds n (F i z) (q i z)
      (n04PositiveLeft i) (n04PositiveRight i) (M i)⁻¹ (M i)⁻¹ (M i) (M i) :=
    (hfinite i).2 z.1 z.2.1 z.2.2
  have href (i) (side : Bool) (θ : ℝ) :
      F i z₀ side =ᶠ[𝓝 (if side then n04PositiveRight i else n04PositiveLeft i, θ)]
        (id : PolarPoint → PolarPoint) ∧
      q i z₀ side =ᶠ[𝓝 (if side then n04PositiveRight i else n04PositiveLeft i, θ)]
        (fun _ => (1 : ℝ)) :=
    n04Coordinates_positiveSource_reference_germs W.hT W.hS W.through03 W.field X.e₀
      (X.src i side) θ
  obtain ⟨Cσ, hCσ, degree, Clog, hClog, hfactory⟩ :=
    n04PositiveGeometry_exists_wholePositiveTransport_polynomial_envelope n
  have hordered (i) : n04PositiveLeft i < buffer.centerLeft i ∧
      buffer.centerLeft i < buffer.centerRight i ∧ buffer.centerRight i < n04PositiveRight i :=
    ⟨(buffer.ordered i).1,
      (buffer.ordered i).2.1.trans ((buffer.ordered i).2.2.1.trans (buffer.ordered i).2.2.2.1),
      (buffer.ordered i).2.2.2.2⟩
  let component := fun i => hfactory (F := F i) (q := q i)
    (a := fun side => n04PositiveSourceLeft (X.src i side))
    (b := fun side => n04PositiveSourceRight (X.src i side))
    (l := n04PositiveLeft i) (r := n04PositiveRight i)
    (c := buffer.centerLeft i) (d := buffer.centerRight i)
    (κφ := (M i)⁻¹) (κX := (M i)⁻¹ / 2) (M := M i) (H := M i) z₀
    (hordered i).1 (hordered i).2.1 (hordered i).2.2
    (inv_pos.mpr (zero_lt_one.trans_le (hM i))) (inv_le_one_of_one_le₀ (hM i))
    (by rw [inv_inv]) (half_pos (inv_pos.mpr (zero_lt_one.trans_le (hM i))))
    (hM i) (hM i) (hdata i) (fun z => (hf i z).angular_lower)
    (fun z side θ => by
      calc
        2 * ((M i)⁻¹ / 2) = (M i)⁻¹ := by ring
        _ ≤ _ := (hf i z).radial_lower side θ)
    (fun z => (hf i z).coordinate_jets) (fun z => (hf i z).height_value)
    (fun z => (hf i z).height_inverse) (fun z => (hf i z).height_jets) (href i)
  let Mσ := fun i => (component i).choose
  let δ := fun i => (component i).choose_spec.choose
  have hc (i) := (component i).choose_spec.choose_spec
  let G : N04PositiveGeometryControlData W X n :=
    { buffer := buffer, base := base, ε := ε, M := M, Mσ := Mσ, δ := δ,
      Cinput := Cinput, Cbuffer := Cbuffer, Cσ := Cσ, degree := degree, Clog := Clog }
  refine ⟨{
    toN04PositiveGeometryControlData := G
    base_le := hb
    radius_pos := hε
    radius_le := hεW
    input_constant := hCinput
    buffer_constant := hCbuffer
    inverse_constant := hCσ
    log_constant := hClog
    input_one := hM
    input_cost := fun _ => le_rfl
    buffer_cost := hbufferCost
    endpoint_bounds := fun z hz hs i => (hfinite i).2 z hz hs
    inverse_one := fun i => (hc i).1
    inverse_cost := fun i => (hc i).2.1
    coefficient_lower := ?_
    coefficient_bound := ?_
    log_bound := ?_
    width_pos := fun i => (hc i).2.2.2.2.2.1
    width_core := fun i => (hc i).2.2.2.2.2.2.1
    width_one := fun i => (hc i).2.2.2.2.2.2.2.1
    width_inverse := fun i => (hc i).2.2.2.2.2.2.2.2.1
    radial_lower_pos := fun i => (hc i).2.2.2.2.2.2.2.2.2.1
    matching := ?_
    reference := ?_ }⟩
  · intro z hz hs i side θ
    have h := (hc i).2.2.1 (⟨z, hz, hs⟩ : Z) side θ
    change 2 * ((M i)⁻¹ / 2) ≤ _ at h
    have he : 2 * ((M i)⁻¹ / 2) = (M i)⁻¹ := by ring
    exact he ▸ h
  · intro z hz hs i side k hk hkn θ
    exact (hc i).2.2.2.1 (⟨z, hz, hs⟩ : Z) side k hk hkn θ
  · intro z hz hs i side k hk hkn θ
    exact (hc i).2.2.2.2.1 (⟨z, hz, hs⟩ : Z) side k hk hkn θ
  · intro z hz hs i
    exact ((hc i).2.2.2.2.2.2.2.2.2.2 (⟨z, hz, hs⟩ : Z)).1
  · intro i
    exact ((hc i).2.2.2.2.2.2.2.2.2.2 z₀).2 rfl

end ContinuousFlexibility.Analysis
