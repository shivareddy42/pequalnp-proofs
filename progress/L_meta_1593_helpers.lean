import Mathlib.Combinatorics.SimpleGraph.Clique
import PEqualNP.Defs

-- Partial progress for L-meta-1593. The posted gate-saving statement is unproved.
-- This file verifies the graph transformations and edge counts.

namespace PEqualNP.Outside.L_meta_1593_aux

noncomputable def edgeOr {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n,
    G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)

lemma edgeOr_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (x : Fin n → Bool) : edgeOr G A x = true ↔
    (∃ a ∈ A, x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
  simp [edgeOr]

lemma independent_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (hgirth : ∀ w : Fin n, ∀ c : G.Walk w w, c.IsCycle → 7 ≤ c.length)
    (z u v : Fin n) (hzu : G.Adj z u) (hzv : G.Adj z v) : ¬ G.Adj u v := by
  classical
  intro huv
  have hc : G.IsNClique 3 {z, u, v} := G.is3Clique_triple_iff.mpr ⟨hzu, hzv, huv⟩
  obtain ⟨w, c, hcycle, hlen⟩ := G.is3Clique_iff_exists_cycle_length_three.mp ⟨_, hc⟩
  have h := hgirth w c hcycle
  omega

lemma pin_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (z : Fin n) (hz : z ∉ A) (x : Fin n → Bool) :
    edgeOr G A (Function.update x z false) = edgeOr (G.deleteIncidenceSet z) A x := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [edgeOr_true, edgeOr_true]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · have haz : a ≠ z := fun e => hz (e ▸ ha)
      exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne haz] using hxa⟩
    · have huz : u ≠ z := by intro e; simp [e] at hxu
      have hvz : v ≠ z := by intro e; simp [e] at hxv
      exact Or.inr ⟨u, v, SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huv, huz, hvz⟩,
        by simpa [Function.update_of_ne huz] using hxu,
        by simpa [Function.update_of_ne hvz] using hxv⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · have haz : a ≠ z := fun e => hz (e ▸ ha)
      exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne haz] using hxa⟩
    · obtain ⟨huv, huz, hvz⟩ := SimpleGraph.deleteIncidenceSet_adj.mp huv
      exact Or.inr ⟨u, v, huv, by simpa [Function.update_of_ne huz] using hxu,
        by simpa [Function.update_of_ne hvz] using hxv⟩

lemma pin_true_nine_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n))
    (hdegree : ∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3)
    (hgirth : ∀ w : Fin n, ∀ c : G.Walk w w, c.IsCycle → 7 ≤ c.length)
    (hmarked : ∀ i j : Fin n, G.Adj i j → i ∉ A)
    (z : Fin n) (hz : z ∉ A) :
    ∃ (B : Finset (Fin n)) (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj),
      B.card = A.card + 3 ∧ H.edgeFinset.card + 9 = G.edgeFinset.card ∧
      (∀ i j : Fin n, H.Adj i j → i ∉ B) ∧
      ∀ x : Fin n → Bool, edgeOr G A (Function.update x z true) = edgeOr H B x := by
  classical
  let N := G.neighborFinset z
  let E := N.biUnion (fun u => G.incidenceFinset u)
  let B := A ∪ N
  let H := G.deleteEdges (E : Set (Sym2 (Fin n)))
  have memN (u : Fin n) : u ∈ N ↔ G.Adj z u := by simp [N]
  have ncard : N.card = 3 := by
    rw [show N = G.neighborFinset z from rfl, G.card_neighborFinset_eq_degree,
      ← G.ncard_neighborSet]
    exact hdegree z hz
  have disjointN : Disjoint A N := by
    apply Finset.disjoint_left.mpr
    intro u huA huN
    exact hmarked u z ((memN u).mp huN).symm huA
  have bcard : B.card = A.card + 3 := by
    rw [Finset.card_union_of_disjoint disjointN, ncard]
  have pairwise : (N : Set (Fin n)).PairwiseDisjoint (fun u => G.incidenceFinset u) := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro e heu hev
    have heu' : e ∈ G.incidenceSet u := by simpa using heu
    have hev' : e ∈ G.incidenceSet v := by simpa using hev
    have hadj : G.Adj u v := G.adj_of_mem_incidenceSet huv heu' hev'
    exact independent_neighbors G hgirth z u v ((memN u).mp hu) ((memN v).mp hv) hadj
  have ecard : E.card = 9 := by
    rw [Finset.card_biUnion pairwise]
    have degrees : ∀ u ∈ N, (G.incidenceFinset u).card = 3 := by
      intro u hu
      rw [G.card_incidenceFinset_eq_degree, ← G.ncard_neighborSet]
      exact hdegree u (hmarked u z ((memN u).mp hu).symm)
    calc
      (∑ u ∈ N, (G.incidenceFinset u).card) = ∑ _u ∈ N, 3 :=
        Finset.sum_congr rfl degrees
      _ = 9 := by simp [ncard]
  have esub : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨u, _, heu⟩ := Finset.mem_biUnion.mp he
    exact G.incidenceFinset_subset u heu
  have hcard : H.edgeFinset.card + 9 = G.edgeFinset.card := by
    have h := Finset.card_sdiff_add_card_eq_card esub
    simpa [H, SimpleGraph.edgeFinset_deleteEdges, ecard] using h
  have adjH (u v : Fin n) : H.Adj u v ↔ G.Adj u v ∧ u ∉ N ∧ v ∉ N := by
    change (G.deleteEdges (E : Set (Sym2 (Fin n)))).Adj u v ↔ _
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨huv, he⟩
      refine ⟨huv, ?_, ?_⟩
      · intro hu
        apply he
        exact Finset.mem_biUnion.mpr ⟨u, hu, by simpa using huv⟩
      · intro hv
        apply he
        exact Finset.mem_biUnion.mpr ⟨v, hv, by simpa using G.mk'_mem_incidenceSet_right_iff.mpr huv⟩
    · rintro ⟨huv, hu, hv⟩
      refine ⟨huv, ?_⟩
      intro he
      obtain ⟨w, hw, hew⟩ := Finset.mem_biUnion.mp he
      have hm : w ∈ s(u,v) := (show s(u,v) ∈ G.incidenceSet w by simpa using hew).2
      rcases Sym2.mem_iff.mp hm with rfl | rfl
      · exact hu hw
      · exact hv hw
  have neq_z (u v : Fin n) (huv : H.Adj u v) : u ≠ z ∧ v ≠ z := by
    obtain ⟨huvG, hu, hv⟩ := (adjH u v).mp huv
    constructor
    · intro e
      subst u
      exact hv ((memN v).mpr huvG)
    · intro e
      subst v
      exact hu ((memN u).mpr huvG.symm)
  refine ⟨B, H, inferInstance, bcard, hcard, ?_, ?_⟩
  · intro u v huv
    have hu := (adjH u v).mp huv
    intro hB
    rcases Finset.mem_union.mp hB with hA | hN
    · exact hmarked u v hu.1 hA
    · exact hu.2.1 hN
  · intro x
    apply Bool.eq_iff_iff.mpr
    rw [edgeOr_true, edgeOr_true]
    constructor
    · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩)
      · have haz : a ≠ z := fun e => hz (e ▸ ha)
        exact Or.inl ⟨a, Finset.mem_union_left N ha,
          by simpa [Function.update_of_ne haz] using hxa⟩
      · by_cases huz : u = z
        · subst u
          have hvz : v ≠ z := huv.ne.symm
          exact Or.inl ⟨v, Finset.mem_union_right A ((memN v).mpr huv),
            by simpa [Function.update_of_ne hvz] using hxv⟩
        · by_cases hvz : v = z
          · subst v
            exact Or.inl ⟨u, Finset.mem_union_right A ((memN u).mpr huv.symm),
              by simpa [Function.update_of_ne huz] using hxu⟩
          · have hxu' : x u = true := by simpa [Function.update_of_ne huz] using hxu
            have hxv' : x v = true := by simpa [Function.update_of_ne hvz] using hxv
            by_cases huN : u ∈ N
            · exact Or.inl ⟨u, Finset.mem_union_right A huN, hxu'⟩
            by_cases hvN : v ∈ N
            · exact Or.inl ⟨v, Finset.mem_union_right A hvN, hxv'⟩
            exact Or.inr ⟨u, v, (adjH u v).mpr ⟨huv, huN, hvN⟩, hxu', hxv'⟩
    · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩)
      · rcases Finset.mem_union.mp ha with haA | haN
        · have haz : a ≠ z := fun e => hz (e ▸ haA)
          exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne haz] using hxa⟩
        · have hza : G.Adj z a := (memN a).mp haN
          exact Or.inr ⟨z, a, hza, by simp,
            by simpa [Function.update_of_ne hza.ne.symm] using hxa⟩
      · obtain ⟨huz, hvz⟩ := neq_z u v huv
        exact Or.inr ⟨u, v, ((adjH u v).mp huv).1,
          by simpa [Function.update_of_ne huz] using hxu,
          by simpa [Function.update_of_ne hvz] using hxv⟩

end PEqualNP.Outside.L_meta_1593_aux
