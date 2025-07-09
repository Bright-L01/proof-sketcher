-- Point Set Topology Examples for Proof Sketcher
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation
import Mathlib.Topology.Compactness.Compact

-- Example 1: Open sets form a topology
theorem open_sets_form_topology (X : Type*) [TopologicalSpace X] :
  IsOpen (∅ : Set X) ∧ IsOpen (Set.univ : Set X) ∧
  (∀ (I : Type*) (s : I → Set X), (∀ i, IsOpen (s i)) → IsOpen (⋃ i, s i)) ∧
  (∀ s t : Set X, IsOpen s → IsOpen t → IsOpen (s ∩ t)) := by
  constructor
  · exact isOpen_empty
  constructor
  · exact isOpen_univ
  constructor
  · intros I s hs
    exact isOpen_iUnion hs
  · intros s t hs ht
    exact IsOpen.inter hs ht

-- Example 2: Hausdorff property
theorem hausdorff_separation {X : Type*} [TopologicalSpace X] [T2Space X]
  (x y : X) (h : x ≠ y) :
  ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation h
  exact ⟨U, V, hU, hV, hxU, hyV, hUV⟩

-- Example 3: Compact subsets of Hausdorff spaces are closed
theorem compact_subset_hausdorff_closed {X : Type*} [TopologicalSpace X] [T2Space X]
  {K : Set X} (hK : IsCompact K) : IsClosed K := by
  exact IsCompact.isClosed hK

-- Example 4: Continuous image of compact is compact
theorem continuous_image_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} (hf : Continuous f) {K : Set X} (hK : IsCompact K) :
  IsCompact (f '' K) := by
  exact IsCompact.image hK hf

-- Example 5: Tychonoff's theorem (finite case)
theorem tychonoff_finite {ι : Type*} [Fintype ι] {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] (h : ∀ i, CompactSpace (X i)) :
  CompactSpace (∀ i, X i) := by
  exact Pi.compactSpace

-- Example 6: Connectedness is preserved by continuous maps
theorem continuous_image_connected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} (hf : Continuous f) {S : Set X} (hS : IsConnected S) :
  IsConnected (f '' S) := by
  exact IsConnected.image hS f hf

-- Example 7: Product of connected spaces is connected
theorem product_connected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ConnectedSpace X] [ConnectedSpace Y] : ConnectedSpace (X × Y) := by
  exact instConnectedSpaceProd
