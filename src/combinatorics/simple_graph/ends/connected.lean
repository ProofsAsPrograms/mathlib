import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.subgraph
import .mathlib


-- All this file is in great part thanks to Kyle Miller -- bad parts are mine.

open simple_graph

universes u v

namespace simple_graph

variables {V : Type u} {V' : Type v} (G : simple_graph V) (G' : simple_graph V')
variables {G}


namespace subgraph

@[simp] lemma verts_inf (H₁ H₂ : G.subgraph) :
  (H₁ ⊓ H₂).verts = H₁.verts ∩ H₂.verts := rfl

@[simp] lemma verts_sup (H₁ H₂ : G.subgraph) :
  (H₁ ⊔ H₂).verts = H₁.verts ∪ H₂.verts := rfl

end subgraph


/- TODO : Move somewhere it belongs -/
----------------------------------------------------------------------------------------------------
/-- See Note [range copy pattern] -/
protected def copy {V : Type*} (G : simple_graph V) {V' : Type*} (h : V' = V) : simple_graph V' :=
{ adj := λ u v, G.adj (cast h u) (cast h v) }

@[simp] lemma copy_rfl {V : Type*} {G : simple_graph V} : G.copy rfl = G := by { ext, refl }

@[simp] lemma copy_copy {V V' V'' : Type*} {G : simple_graph V} (h : V' = V) (h' : V'' = V') :
  (G.copy h).copy h' = G.copy (h'.trans h) := by { subst h, subst h', refl }

/-- The graphs `G.copy h` and `G` are isomorphic using `cast h` on vertices. -/
@[simps]
def copy_iso {V : Type*} (G : simple_graph V) {V' : Type*} (h : V' = V) : G.copy h ≃g G :=
{ map_rel_iff' := by { subst h, intros u v, refl }, .. equiv.cast h }

@[simp]
lemma subgraph.adj_copy_coe {V : Type*} {G : simple_graph V} (H : G.subgraph) {s : set V}
  (h : s = H.verts) {u v : V} {hu hv} :
  (H.coe.copy (by rw h) : simple_graph s).adj ⟨u, hu⟩ ⟨v, hv⟩ = H.adj u v :=
by { subst h, refl }

----------------------------------------------------------------------------------------------------

lemma subgraph.connected_iff (H : G.subgraph) :
  H.connected ↔ H.coe.preconnected ∧ H.verts.nonempty :=
begin
  change H.coe.connected ↔ _,
  rw [connected_iff, set.nonempty_coe_sort],
end

lemma induce_singleton_connected (G : simple_graph V) (v : V) :
  (G.induce {v}).connected :=
begin
  rw connected_iff,
  refine ⟨_, by simp⟩,
  rintro ⟨x, hx⟩ ⟨y, hy⟩,
  rw set.mem_singleton_iff at hx hy,
  subst_vars,
end

lemma subgraph.induce_singleton_connected (H : G.subgraph) (v : V) : (H.induce {v}).connected :=
begin
  rw subgraph.connected_iff,
  refine ⟨_, by simp⟩,
  rintro ⟨x, xe, hx⟩ ⟨y, ye, hy⟩,
  use walk.nil,
end

@[mono]
lemma connected.mono {G G' : simple_graph V} (h : G ≤ G') : G.connected → G'.connected :=
begin
  simp_rw connected_iff,
  rintro ⟨hc, hn⟩,
  refine ⟨_, hn⟩,
  refine λ u v, (hc u v).elim (λ p, _),
  constructor,
  simpa using p.map (hom.map_spanning_subgraphs h),
end

lemma subgraph.connected.edges_mono {H K : G.subgraph}
  (sub : H ≤ K) (Veq : H.verts = K.verts) : H.connected → K.connected :=
begin
  have : H.coe ≤ K.coe.copy (by rw Veq),
  { rintro ⟨u, hu⟩ ⟨v, hv⟩,
    simp only [subgraph.coe_adj, subtype.coe_mk, subgraph.adj_copy_coe],
    apply sub.2 },
  intro hc,
  have := hc.mono this,
  rw (copy_iso K.coe _).connected_iff at this,
  exact this,
end

lemma connected.union {H K : G.subgraph}
  (Hconn : H.connected) (Kconn : K.connected) (HinterK : (H ⊓ K).verts.nonempty ) :
  (H ⊔ K).connected :=
begin
  obtain ⟨u, huH, huK⟩ := HinterK,
  have hu : u ∈ (H ⊔ K).verts := or.inl huH,
  rw subgraph.connected_iff,
  refine ⟨_, ⟨u, hu⟩⟩,
  have key : ∀ (v : (H ⊔ K).verts), (H ⊔ K).coe.reachable ⟨u, hu⟩ v,
  { rintro ⟨v, hv|hv⟩,
    { refine (Hconn ⟨u, huH⟩ ⟨v, hv⟩).elim (λ p, _),
      have q := p.map (subgraph.inclusion le_sup_left : H.coe →g (H ⊔ K).coe),
      constructor,
      simpa [subgraph.inclusion] using q, },
    { refine (Kconn ⟨u, huK⟩ ⟨v, hv⟩).elim (λ p, _),
      have q := p.map (subgraph.inclusion le_sup_right : K.coe →g (H ⊔ K).coe),
      constructor,
      simpa [subgraph.inclusion] using q, } },
  intros v w,
  exact reachable.trans (key _).symm (key _),
end

lemma induce_pair_connected_of_adj {u v : V} (huv : G.adj u v) :
  (G.induce {u, v}).connected :=
begin
  rw connected_iff,
  refine ⟨_, by simp⟩,
  rintro ⟨x, hx⟩ ⟨y, hy⟩,
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at hx hy,
  obtain rfl|rfl := hx; obtain rfl|rfl := hy;
    refl <|> { refine ⟨walk.cons _ walk.nil⟩, simp [huv, huv.symm] }
end

lemma subgraph.induce_pair_connected {u v : V} (huv : G.adj u v) :
  ((⊤ : G.subgraph).induce {u, v}).connected :=
begin
  change connected (subgraph.coe _),
  rw ← induce_eq_coe_induce_top,
  exact induce_pair_connected_of_adj huv,
end

lemma connected.adj_union {H K : G.subgraph}
  (Hconn : H.connected) (Kconn : K.connected) (u v : V) (uH : u ∈ H.verts) (vK : v ∈ K.verts)
  (huv : G.adj u v) :
  ((⊤ : G.subgraph).induce {u, v} ⊔ H ⊔ K).connected :=
begin
  refine connected.union _ ‹_› _,
  { refine connected.union (subgraph.induce_pair_connected huv) ‹_› _,
    exact ⟨u, by simp [uH]⟩, },
  { exact ⟨v, by simp [vK]⟩ },
end

/-- A walk is contained in a subgraph if its vertices and edges are in the subgraph -/
def walk.contained (H : G.subgraph) :
  Π {u v : V} (p : G.walk u v),  Prop
| _ _ (walk.nil' u) := u ∈ H.verts
| _ _ (walk.cons' u v w a p) := H.adj u v  ∧ walk.contained p

@[simp]
lemma walk.contained_cons_iff (H : G.subgraph)
  {u v w : V} (a : G.adj u v) (p : G.walk v w) :
  (walk.cons a p).contained H ↔ (H.adj u v ∧ p.contained H) := by refl

@[simp]
lemma walk.contained_nil_iff (H : G.subgraph)
  {u : V} : (walk.nil' u).contained H ↔ u ∈ H.verts := by refl

lemma walk.contained_verts (H : G.subgraph)
  {u v : V} (p : G.walk u v) : p.contained H → ∀ (w : V), w ∈ p.support → w ∈ H.verts :=
begin
  rintro h,
  induction p,
  { simp, exact h, },
  { simp at h, specialize p_ih h.2,
    intros w wsup,
    rw [walk.support_cons,list.mem_cons_iff] at wsup,
    cases wsup,
    { rw wsup, exact H.edge_vert h.1, },
    { exact p_ih w wsup, },}
end

lemma walk.contained_induced_iff (S : set V) {u v : V} (p : G.walk u v) :
  p.contained ((⊤ : G.subgraph).induce S) ↔ ∀ w ∈ p.support, w ∈ S :=
begin
  split,
  { exact walk.contained_verts _ p, },
  { rintro sub,
    induction p,
    {simp, apply sub, simp, },
    { simp, refine ⟨⟨_,_,p_h⟩,_⟩,
      {apply sub, simp,},
      {apply sub, simp,},
      {apply p_ih, rintro w ws, apply sub, simp, right, exact ws,},
    }},
end

lemma walk.contained_append_left (H : G.subgraph)
  {u v w : V} (p : G.walk u v) (q : G.walk v w) : (p.append q).contained H → p.contained H := sorry

lemma walk.contained_append_right (H : G.subgraph)
  {u v w : V} (p : G.walk u v) (q : G.walk v w) : (p.append q).contained H → p.contained H := sorry

/-- A walk `contained` in a subgraph can be viewed as a walk of the subgraph -/
def walk.contained.to_subgraph {H : G.subgraph}
  {u w : H.verts} {p : G.walk u w} (pcon : p.contained H) : H.coe.walk u w :=
begin
  rcases u with ⟨uu,hu⟩,
  rcases w with ⟨ww,hw⟩,
  dsimp at p,
  induction p with u u v w uav vpw ih,
  { exact walk.nil, },
  { rw walk.contained_cons_iff at pcon,
    have hv : v ∈ H.verts := H.edge_vert (pcon.1).symm,
    refine walk.cons' _ ⟨v,hv⟩ _ _ _,
    simp only [subgraph.coe_adj, subtype.coe_mk],
    exact pcon.1,
    exact ih hv hw pcon.2,},
end

lemma walk.contained.to_subgraph_map_eq {H : G.subgraph}
  {u w : H.verts} {p : G.walk u w} (pcon : p.contained H) :
  (walk.contained.to_subgraph pcon).map H.hom = p :=
begin
  rcases u with ⟨uu,hu⟩,
  rcases w with ⟨ww,hw⟩,
  dsimp at p,
  induction p with u u v w uav vpw ih,
  { dsimp [subgraph.hom,walk.contained.to_subgraph], refl, },
  { apply congr_arg2,
    simp only [eq_iff_true_of_subsingleton],
    apply ih,}
end

/-- A walk all whose vertices are contained in a set can be viewed
    as a walk in the induced subgraph -/
def walk.to_induced (S : set V)
  {u v : S} (p : G.walk u v) (hp : ∀ w ∈ p.support, w ∈ S) : (G.induce S).walk u v :=
begin
  rw induce_eq_coe_induce_top,
  apply walk.contained.to_subgraph, rotate,
  exact p,
  rw walk.contained_induced_iff,
  exact hp,
end

lemma connected.walk_support [decidable_eq V] {u v : V} (p : G.walk u v) :
  (G.induce (p.support.to_finset : set V)).connected :=
begin
  rw connected_iff,
  split, rotate, simp, constructor, rw list.mem_to_finset, exact walk.start_mem_support p,
  rintro ⟨x,xh⟩ ⟨y,yh⟩,
  rw [finset.mem_coe,list.mem_to_finset] at xh yh,
  obtain ⟨ux,xv,ex⟩ := (walk.mem_support_iff_exists_append).mp xh,
  obtain ⟨uy,yv,ey⟩ := (walk.mem_support_iff_exists_append).mp yh,
  let q := ux.reverse.append uy,
  have : ∀ w ∈ q.support, w ∈ (p.support.to_finset : set V), by
  { rintro w wq,
    rw walk.mem_support_append_iff at wq,
    cases wq,
    { simp only [ex, finset.mem_coe, list.mem_to_finset, walk.mem_support_append_iff],
      rw [walk.support_reverse, list.mem_reverse] at wq,
      exact or.inl wq, },
    { simp only [ey, finset.mem_coe, list.mem_to_finset, walk.mem_support_append_iff],
      exact or.inl wq, },
  },
  apply nonempty.intro,
  exact walk.to_induced (p.support.to_finset) q this,
end

def finset.extend_to_connected (G : simple_graph V) (Gpc : G.preconnected) (K : finset V) (Kn : K.nonempty) :
  {K' : finset V | K ⊆ K' ∧ (G.induce (K' : set V)).connected } := sorry




end simple_graph
